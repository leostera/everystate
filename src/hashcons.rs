//! Hash-consing of values: every distinct value the search keeps is stored once, in a per-thread table,
//! and all its occurrences share that one allocation.
//!
//! A value is *canonical* when it is a scalar, or a tuple, record, function or explicit set whose node
//! is in the table and whose children are all canonical. The table owns a reference to each canonical
//! node and marks it with a tag (`canon` in the node: this table's epoch in the high 32 bits, the node's
//! id in the low 32), so asking whether a node is canonical is one load.
//!
//! What it buys:
//! - Two canonical values of the same epoch are equal exactly when they are the same scalar or the same
//!   node (`ident`), because every value has one canonical form (functions are kept as tuple, record or
//!   function by their domain, sets are sorted and duplicate-free) and the table holds one node per
//!   form. Comparing them costs a pointer comparison instead of a walk of two trees.
//! - The id is a small dense number for a value, usable as a key (`id`).
//! - Interning a value whose children are canonical costs one hash of the children's words (the same
//!   word the fingerprint uses, so it is computed once and cached in the node) and one probe.
//!
//! What is not interned (`canon` returns None): operators, lazy functions and every set that is not an
//! explicit sorted vector (intervals, symbolic and lazy sets), and any value containing one. Those keep
//! today's path: a full comparison where an identity check would do. An interval is not interned even
//! though it is a plain value: `1..3` and `{1, 2, 3}` are equal but print differently, so sharing one
//! node between them would change what a trace shows, and keeping both would break `ident`.
//!
//! Lifetime: the table belongs to the thread and is emptied by `reset` (at the start of each check),
//! which also moves to a new epoch, so a node interned by an earlier check is not taken as canonical.
use crate::value::*;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::atomic::{AtomicU32, Ordering};

static NEXT_EPOCH: AtomicU32 = AtomicU32::new(1);

/// The number of a canonical value in this thread's table (scalars have one too). Ids are dense, start at
/// 1, and stay below `NOT_INTERNED`.
pub type Id = u32;
/// Ids from here on are not ids of the table: users mark values that cannot be interned with them.
pub const NOT_INTERNED: Id = 1 << 31;
/// Ids from here to `NOT_INTERNED` are *immediate*: the value is in the id (a Boolean, or an integer
/// within `IMM_INT`), with no entry in the table. Integers are most of the scalars a search meets, and a
/// counter can take millions of values; this way they cost neither a probe nor memory.
pub const IMMEDIATE: Id = 1 << 30;
/// integers `-IMM_INT ..= IMM_INT - 1` are immediate
const IMM_INT: i64 = 1 << 28;

/// The immediate id of `v`, if it has one.
#[inline]
fn immediate(v: &Value) -> Option<Id> {
    match v {
        Value::Bool(b) => Some(IMMEDIATE + *b as Id),
        Value::Int(i) if (-IMM_INT..IMM_INT).contains(i) => Some(IMMEDIATE + 2 + (*i + IMM_INT) as Id),
        _ => None,
    }
}
/// The value of an immediate id.
#[inline]
fn immediate_value(x: Id) -> Value {
    debug_assert!((IMMEDIATE..NOT_INTERNED).contains(&x));
    match x - IMMEDIATE {
        0 => Value::Bool(false),
        1 => Value::Bool(true),
        k => Value::Int((k - 2) as i64 - IMM_INT),
    }
}

struct Table {
    /// tag bits of this table's nodes: the epoch, shifted into the high half
    epoch: u64,
    /// id -> node (id 0 is unused, so a zero `canon` means "not interned")
    vals: Vec<Value>,
    /// id -> the node's word (`value_word`)
    words: Vec<u64>,
    /// open addressing over ids, 0 = empty
    slots: Vec<u32>,
    mask: usize,
}

impl Table {
    fn new() -> Table {
        let epoch = (NEXT_EPOCH.fetch_add(1, Ordering::Relaxed) as u64) << 32;
        EPOCH.with(|e| e.set(epoch));
        Table { epoch, vals: vec![Value::Undef], words: vec![0], slots: vec![0; 1 << 12], mask: (1 << 12) - 1 }
    }

    #[inline]
    fn is_mine(&self, tag: u64) -> bool {
        tag & !0xFFFF_FFFF == self.epoch
    }

    /// The canonical value equal to `v`, interning it (and its children) if needed.
    fn canon(&mut self, v: &Value) -> Option<Value> {
        match v {
            Value::Int(_) | Value::Bool(_) | Value::Str(_) | Value::Model(_) => Some(v.clone()),
            Value::Tuple(t) if self.is_mine(t.canon.get()) => Some(v.clone()),
            Value::Record(r) if self.is_mine(r.canon.get()) => Some(v.clone()),
            Value::Fcn(f) if self.is_mine(f.canon.get()) => Some(v.clone()),
            Value::Set(s) if self.is_mine(s.canon.get()) => Some(v.clone()),
            Value::Tuple(_) | Value::Record(_) | Value::Fcn(_) | Value::Set(_) => self.intern(v),
            _ => None,
        }
    }

    /// `vs` with every element canonical: None when one cannot be; `Ok(None)`-like `Some(None)` when
    /// every element already is (nothing to rebuild).
    fn canon_all(&mut self, vs: &[Value]) -> Option<Option<Vec<Value>>> {
        let mut out: Option<Vec<Value>> = None;
        for (i, x) in vs.iter().enumerate() {
            let c = self.canon(x)?;
            if out.is_none() && !ident_child(&c, x) {
                out = Some(vs[..i].to_vec());
            }
            if let Some(o) = &mut out {
                o.push(c);
            }
        }
        Some(out)
    }

    /// The id of the canonical value equal to `v` (interning it, scalars included).
    fn id(&mut self, v: &Value) -> Option<Id> {
        if let Some(x) = immediate(v) {
            return Some(x);
        }
        let c = match v {
            Value::Int(_) | Value::Bool(_) | Value::Str(_) | Value::Model(_) => return Some(self.scalar_id(v)),
            _ => self.canon(v)?,
        };
        Some(tag(&c) as Id)
    }

    fn scalar_id(&mut self, v: &Value) -> Id {
        let w = value_word(v).expect("a scalar has a word");
        let mut i = (spread(w) as usize) & self.mask;
        loop {
            let id = self.slots[i] as usize;
            if id == 0 {
                break;
            }
            if self.words[id] == w && ident_child(&self.vals[id], v) {
                return id as Id;
            }
            i = (i + 1) & self.mask;
        }
        self.insert_at(i, v.clone(), w) as Id
    }

    fn insert_at(&mut self, slot: usize, node: Value, w: u64) -> usize {
        let id = self.vals.len();
        assert!(id < IMMEDIATE as usize, "more than 2^30 distinct values");
        self.slots[slot] = id as u32;
        self.vals.push(node);
        self.words.push(w);
        if self.vals.len() * 2 > self.slots.len() {
            self.grow();
        }
        id
    }

    #[cold]
    fn intern(&mut self, v: &Value) -> Option<Value> {
        // 1. a node equal to `v` whose children are canonical (`v` itself when they already are)
        let node = match v {
            Value::Tuple(t) => match self.canon_all(&t.e)? {
                None => v.clone(),
                Some(e) => Value::Tuple(TupleV::rc(e)),
            },
            Value::Record(r) => match self.canon_all(&r.vals)? {
                None => v.clone(),
                Some(vals) => Value::Record(Rc::new(RecordV::new(r.names.clone(), vals))),
            },
            Value::Fcn(f) => {
                let dom = self.canon_all(&f.dom)?;
                let vals = self.canon_all(&f.vals)?;
                match (dom, vals) {
                    (None, None) => v.clone(),
                    (dom, vals) => {
                        let dom = match dom {
                            None => f.dom.clone(),
                            Some(d) => Rc::new(d),
                        };
                        Value::Fcn(Rc::new(FcnV::new(dom, vals.unwrap_or_else(|| f.vals.clone()))))
                    }
                }
            }
            Value::Set(s) => match &s.k {
                SetK::Enum(e) => match self.canon_all(e)? {
                    None => v.clone(),
                    Some(e) => SetV::of(e),
                },
                _ => return None,
            },
            _ => return None,
        };
        // 2. the node already in the table, or this one
        let w = value_word(&node).ok()?;
        let mut i = (spread(w) as usize) & self.mask;
        loop {
            let id = self.slots[i] as usize;
            if id == 0 {
                break;
            }
            if self.words[id] == w && same_node(&self.vals[id], &node) {
                return Some(self.vals[id].clone());
            }
            i = (i + 1) & self.mask;
        }
        let tag = self.epoch | self.vals.len() as u64;
        match &node {
            Value::Tuple(t) => t.canon.set(tag),
            Value::Record(r) => r.canon.set(tag),
            Value::Fcn(f) => f.canon.set(tag),
            Value::Set(s) => s.canon.set(tag),
            _ => unreachable!(),
        }
        self.insert_at(i, node.clone(), w);
        Some(node)
    }

    fn grow(&mut self) {
        let cap = self.slots.len() * 2;
        self.slots = vec![0; cap];
        self.mask = cap - 1;
        for id in 1..self.vals.len() {
            let mut i = (spread(self.words[id]) as usize) & self.mask;
            while self.slots[i] != 0 {
                i = (i + 1) & self.mask;
            }
            self.slots[i] = id as u32;
        }
    }
}

/// Spreads a word over the table's index bits (words of small tuples differ mostly in their high bits).
#[inline]
fn spread(w: u64) -> u64 {
    (w ^ (w >> 29)).wrapping_mul(0xBF58_476D_1CE4_E5B9) >> 7
}

/// The same scalar or the same node. For canonical values of one epoch this is equality.
#[inline]
fn ident_child(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => x == y,
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Str(x), Value::Str(y)) => x == y,
        (Value::Model(x), Value::Model(y)) => x == y,
        (Value::Tuple(x), Value::Tuple(y)) => Rc::ptr_eq(x, y),
        (Value::Record(x), Value::Record(y)) => Rc::ptr_eq(x, y),
        (Value::Fcn(x), Value::Fcn(y)) => Rc::ptr_eq(x, y),
        (Value::Set(x), Value::Set(y)) => Rc::ptr_eq(x, y),
        _ => false,
    }
}
fn all_ident(a: &[Value], b: &[Value]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| ident_child(x, y))
}

/// Whether two nodes with canonical children are equal: the same kind and identical children.
fn same_node(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Tuple(x), Value::Tuple(y)) => all_ident(&x.e, &y.e),
        (Value::Record(x), Value::Record(y)) => (Rc::ptr_eq(&x.names, &y.names) || x.names[..] == y.names[..]) && all_ident(&x.vals, &y.vals),
        (Value::Fcn(x), Value::Fcn(y)) => (Rc::ptr_eq(&x.dom, &y.dom) || all_ident(&x.dom, &y.dom)) && all_ident(&x.vals, &y.vals),
        (Value::Set(x), Value::Set(y)) => match (&x.k, &y.k) {
            (SetK::Enum(p), SetK::Enum(q)) => all_ident(p, q),
            _ => false,
        },
        _ => false,
    }
}

thread_local! {
    static TABLE: RefCell<Table> = RefCell::new(Table::new());
    /// a copy of the table's epoch, readable without borrowing the table
    static EPOCH: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// The canonical value equal to `v` (interning it), or None when `v` cannot be interned.
#[inline]
pub fn canon(v: &Value) -> Option<Value> {
    match v {
        Value::Int(_) | Value::Bool(_) | Value::Str(_) | Value::Model(_) => Some(v.clone()),
        _ => TABLE.with(|t| t.borrow_mut().canon(v)),
    }
}

/// The id of the canonical value equal to `v` (interning it), or None when `v` cannot be interned.
#[inline]
pub fn id(v: &Value) -> Option<Id> {
    match v {
        Value::Tuple(t) if is_current(t.canon.get()) => Some(t.canon.get() as Id),
        Value::Record(r) if is_current(r.canon.get()) => Some(r.canon.get() as Id),
        Value::Fcn(f) if is_current(f.canon.get()) => Some(f.canon.get() as Id),
        Value::Set(s) if is_current(s.canon.get()) => Some(s.canon.get() as Id),
        _ => TABLE.with(|t| t.borrow_mut().id(v)),
    }
}

/// The id of `v` when it is a canonical composite of this thread's table (no interning, no borrow).
#[inline]
pub fn id_if_canonical(v: &Value) -> Option<Id> {
    if let Some(x) = immediate(v) {
        return Some(x);
    }
    let t = tag(v);
    if is_current(t) {
        Some(t as Id)
    } else {
        None
    }
}

/// The value with id `id` (a shared reference to the canonical node).
#[inline]
pub fn value(id: Id) -> Value {
    if id >= IMMEDIATE {
        return immediate_value(id);
    }
    TABLE.with(|t| t.borrow().vals[id as usize].clone())
}

/// The fingerprint word (`value_word`) of the value with id `id`.
#[inline]
pub fn word(id: Id) -> u64 {
    if id >= IMMEDIATE {
        return value_word(&immediate_value(id)).expect("a scalar has a word");
    }
    TABLE.with(|t| t.borrow().words[id as usize])
}

/// Whether `id` is immediate (its value is in it; see `IMMEDIATE`).
#[inline]
pub fn is_immediate(id: Id) -> bool {
    (IMMEDIATE..NOT_INTERNED).contains(&id)
}

/// Read access to the values and words by id, for loops over many ids (`with_ids`).
pub struct Ids<'a> {
    vals: &'a [Value],
    words: &'a [u64],
}
impl Ids<'_> {
    #[inline]
    pub fn value(&self, id: Id) -> Value {
        if id >= IMMEDIATE { immediate_value(id) } else { self.vals[id as usize].clone() }
    }
    #[inline]
    pub fn word(&self, id: Id) -> u64 {
        if id >= IMMEDIATE { value_word(&immediate_value(id)).expect("a scalar has a word") } else { self.words[id as usize] }
    }
}

/// Runs `f` with read access to the values and words by id. `f` must not intern anything.
#[inline]
pub fn with_ids<T>(f: impl FnOnce(&Ids) -> T) -> T {
    TABLE.with(|t| {
        let t = t.borrow();
        f(&Ids { vals: &t.vals, words: &t.words })
    })
}

/// Whether a tag marks a node of this thread's current table.
#[inline]
fn is_current(tag: u64) -> bool {
    tag != 0 && tag & !0xFFFF_FFFF == EPOCH.with(|e| e.get())
}

/// `canon(&v)`, or `v` itself when it cannot be interned.
#[inline]
pub fn canon_or_keep(v: Value) -> Value {
    match v {
        Value::Int(_) | Value::Bool(_) | Value::Str(_) | Value::Model(_) => v,
        _ => canon(&v).unwrap_or(v),
    }
}

/// The tag of a composite node (0: not interned by any table). It names one canonical value of one
/// epoch, so it can key a memo of results computed from that value.
#[inline]
pub fn tag(v: &Value) -> u64 {
    match v {
        Value::Tuple(t) => t.canon.get(),
        Value::Record(r) => r.canon.get(),
        Value::Fcn(f) => f.canon.get(),
        Value::Set(s) => s.canon.get(),
        _ => 0,
    }
}

/// Some(whether a and b are equal) when identity decides it: two equal scalars, one shared node, or two
/// canonical values of the same table and epoch. None when only a full comparison can tell.
#[inline]
pub fn ident(a: &Value, b: &Value) -> Option<bool> {
    if ident_child(a, b) {
        return Some(true);
    }
    let (ta, tb) = (tag(a), tag(b));
    if ta != 0 && tb != 0 && ta >> 32 == tb >> 32 {
        return Some(false);
    }
    match (a, b) {
        (Value::Int(_), Value::Int(_)) | (Value::Bool(_), Value::Bool(_)) | (Value::Str(_), Value::Str(_)) => Some(false),
        _ => None,
    }
}

/// Empties this thread's table and moves to a new epoch.
pub fn reset() {
    TABLE.with(|t| *t.borrow_mut() = Table::new());
}

/// Number of values interned on this thread since the last `reset` (scalars included).
pub fn len() -> usize {
    TABLE.with(|t| t.borrow().vals.len() - 1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intern::str_id;

    fn tup(e: Vec<Value>) -> Value {
        Value::Tuple(TupleV::rc(e))
    }

    #[test]
    fn equal_values_share_one_node() {
        reset();
        let a = canon(&tup(vec![Value::Int(1), tup(vec![Value::Str(str_id("x"))])])).unwrap();
        let b = canon(&tup(vec![Value::Int(1), tup(vec![Value::Str(str_id("x"))])])).unwrap();
        assert_eq!(ident(&a, &b), Some(true));
        let c = canon(&tup(vec![Value::Int(2), tup(vec![Value::Str(str_id("x"))])])).unwrap();
        assert_eq!(ident(&a, &c), Some(false));
        // the shared child is the same node in both
        if let (Value::Tuple(x), Value::Tuple(y)) = (&a, &c) {
            assert_eq!(ident(&x.e[1], &y.e[1]), Some(true));
        }
    }

    #[test]
    fn interning_keeps_the_fingerprint_word() {
        reset();
        let raw = SetV::of(vec![Value::Int(1), Value::Int(3)]);
        let w = value_word(&SetV::of(vec![Value::Int(1), Value::Int(3)])).unwrap();
        let c = canon(&raw).unwrap();
        assert_eq!(value_word(&c).unwrap(), w);
    }

    #[test]
    fn intervals_and_lazy_values_are_not_interned() {
        reset();
        let iv = Value::Set(Rc::new(SetV::new(SetK::Interval(1, 3))));
        assert!(canon(&iv).is_none());
        assert!(canon(&tup(vec![iv.clone()])).is_none());
        let en = canon(&SetV::of(vec![Value::Int(1), Value::Int(2), Value::Int(3)])).unwrap();
        // equal, but identity cannot tell: the interval is not canonical
        assert_eq!(ident(&iv, &en), None);
    }

    #[test]
    fn a_reset_forgets_earlier_nodes() {
        reset();
        let a = canon(&tup(vec![Value::Int(7)])).unwrap();
        reset();
        let b = canon(&tup(vec![Value::Int(7)])).unwrap();
        // `a` is from the old epoch: not identical to `b`, and not known to differ either
        assert_eq!(ident(&a, &b), None);
        assert_eq!(len(), 1); // <<7>> (a scalar gets a slot only when its id is asked for)
    }

    #[test]
    fn ids_name_values() {
        reset();
        let a = id(&tup(vec![Value::Int(1), Value::Str(str_id("y"))])).unwrap();
        let b = id(&tup(vec![Value::Int(1), Value::Str(str_id("y"))])).unwrap();
        assert_eq!(a, b);
        let one = id(&Value::Int(1)).unwrap();
        assert_ne!(one, a);
        assert_eq!(id(&Value::Int(1)), Some(one));
        // a scalar and a model value with the same number are different values
        assert_ne!(id(&Value::Str(str_id("y"))), id(&Value::Model(str_id("y"))));
        assert_eq!(word(a), value_word(&value(a)).unwrap());
        assert!(id(&Value::Set(Rc::new(SetV::new(SetK::Interval(1, 2))))).is_none());
    }
}
