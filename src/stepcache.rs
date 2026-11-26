//! On by default with the compiled evaluator (EVERYSTATE_STEP_CACHE=off turns it off): a bounded
//! cache of local steps, keyed on value ids.
//!
//! A *unit* is an action instance of a compiled plan (what is left of an action below its top-level
//! disjunctions, existential quantifiers and inlined definitions). When a unit is evaluated the compiled
//! code notes what it reads of the current state: a whole variable, one element `f[k]`, or whether a
//! value is in a set / bag variable (`Rec`, in compile.rs). The unit's result is a list of successors,
//! each given per variable as a value or as a change to the parent's value (an element put into or taken
//! out of a set or bag, an EXCEPT at a path).
//!
//! Everything an entry holds is a `hashcons` id: the bound values, the locations read (the key of `f[k]`
//! is an id), what was found there, and each successor as the ids of the variables it changes. A hit is
//! integer comparisons, and building a successor is copying the parent's row of ids with a few replaced.
//! A change (`Put::Delta`) is applied to the parent's value once per (parent value, change): the result
//! is remembered by id (`Applied`), as is what a location holds in a given value (`Located`).
//!
//! Two kinds of entries share one table:
//! - a *template* per (unit, bound values): the locations whose values pick the entry (every location an
//!   evaluation of the unit with these bound values has read), and a version that changes whenever that
//!   list does;
//! - a *leaf* per (template version, what is at each of its locations): the successors.
//!
//! Soundness: a hit compares the unit, the bound ids, the template version and the id found at every
//! location of the template, so the state agrees with the evaluation that was stored on everything that
//! evaluation read (the locations of a template include those of every evaluation stored under it, and
//! ids are equal exactly when values are). The hash only finds the entry. Nothing is stored for an
//! evaluation that failed, used the tree-walker (whose reads are not noted), whose changes could not be
//! expressed, or that involves a value that cannot be interned.
//!
//! Memory: one table of a fixed number of slots in buckets of `WAYS` (set-associative: two entries used
//! by every state whose hashes meet in a slot would otherwise replace each other on every state, and a
//! replaced template takes all its leaves with it); a full bucket gives up its oldest leaf for a new
//! entry. Every entry is charged its own size plus that of the changes it holds, and an entry that
//! would take the table over its budget (EVERYSTATE_STEP_CACHE_MB, default 32) is not stored.
use crate::hashcons::{self as hc, Id, NOT_INTERNED};
use crate::value::*;
use std::cell::RefCell;

// ---------- what an evaluation is recorded as (values) ----------

#[derive(Clone)]
pub enum Loc {
    Whole(u32),
    /// `var[key]`
    Elem(u32, Value),
    /// whether the value is an element of the set (or in the domain of the bag) `var`
    Member(u32, Value),
}
#[derive(Clone)]
pub enum DOp {
    Bag { e: Value, plus: bool },
    Set { e: Value, add: bool },
    Exc { path: Vec<Value>, v: Value },
}
#[derive(Clone)]
pub enum Write {
    /// the parent's value with these changes (none: unchanged)
    Delta(Vec<DOp>),
    Val(Value),
}

// ---------- what is stored (ids) ----------

/// A location of a state: a whole variable, `var[key]`, or whether `key` is in the set or bag `var`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct LocId {
    pub var: u32,
    pub kind: LocKind,
    /// the key's id (0 for a whole variable)
    pub key: Id,
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LocKind {
    Whole,
    Elem,
    Member,
}
/// What `locate` finds when the key is not in the domain, and whether a value is a member: outside the
/// range of ids.
pub const ABSENT: Id = u32::MAX;
pub const IN: Id = u32::MAX - 1;
pub const OUT: Id = u32::MAX - 2;

/// The new value of a variable a successor changes.
pub enum Put {
    /// this value; `word` is its word
    Id { id: Id, word: u64 },
    /// the parent's value with these changes (values canonical); `id` names the list for `Applied`;
    /// `iops` are the same changes as ids and words (for `delta_word`), when they can be given so;
    /// `shift`, when the changes only replace elements whose old values are part of the leaf's key: what
    /// they add to the parent's word, the same for every state the leaf applies to
    Delta { id: u64, ops: Box<[DOp]>, iops: Option<Box<[IdOp]>>, shift: Option<u64> },
}
/// A change (`DOp`) by the ids and words of its values.
pub enum IdOp {
    Bag { e: Id, we: u64, plus: bool },
    Set { e: Id, we: u64, add: bool },
    /// the path's keys (id, word), and the word of the new value
    Exc { path: Box<[(Id, u64)]>, wv: u64 },
}
fn id_op(op: &DOp) -> Option<IdOp> {
    Some(match op {
        DOp::Bag { e, plus } => IdOp::Bag { e: hc::id(e)?, we: value_word(e).ok()?, plus: *plus },
        DOp::Set { e, add } => IdOp::Set { e: hc::id(e)?, we: value_word(e).ok()?, add: *add },
        DOp::Exc { path, v } => IdOp::Exc { path: path.iter().map(|k| Some((hc::id(k)?, value_word(k).ok()?))).collect::<Option<Vec<_>>>()?.into_boxed_slice(), wv: value_word(v).ok()? },
    })
}
pub struct Tmpl {
    pub unit: u32,
    pub bound: Box<[Id]>,
    pub locs: Box<[LocId]>,
    pub version: u64,
}
pub struct Leaf {
    pub version: u64,
    /// the id at each location of the template (in its order)
    pub key: Box<[Id]>,
    /// per successor, the variables it changes
    pub succs: Box<[Box<[(u32, Put)]>]>,
}
pub enum Entry {
    Leaf(Leaf),
    Tmpl(Tmpl),
}

/// Bytes a value keeps alive, counted as if nothing were shared.
pub fn vsize(v: &Value) -> usize {
    16 + match v {
        Value::Tuple(t) => 48 + t.iter().map(vsize).sum::<usize>(),
        Value::Record(r) => 56 + r.vals.iter().map(vsize).sum::<usize>(),
        Value::Fcn(f) => 96 + f.dom.iter().map(vsize).sum::<usize>() + f.vals.iter().map(vsize).sum::<usize>(),
        Value::Set(s) => match &s.k {
            SetK::Enum(e) => 80 + e.iter().map(vsize).sum::<usize>(),
            SetK::Interval(..) => 80,
            // a symbolic set: not something to keep in an entry
            _ => usize::MAX / 4,
        },
        Value::Int(_) | Value::Bool(_) | Value::Str(_) | Value::Model(_) | Value::Undef => 0,
        _ => usize::MAX / 4,
    }
}
fn ops_size(ops: &[DOp]) -> usize {
    ops.iter()
        .map(|o| {
            40 + match o {
                DOp::Bag { e, .. } | DOp::Set { e, .. } => vsize(e),
                DOp::Exc { path, v } => 24 + path.iter().map(vsize).sum::<usize>() + vsize(v),
            }
        })
        .sum()
}
fn iops_size(ops: &[IdOp]) -> usize {
    ops.iter()
        .map(|o| {
            24 + match o {
                IdOp::Exc { path, .. } => 16 * path.len(),
                _ => 0,
            }
        })
        .sum()
}
fn entry_size(e: &Entry) -> usize {
    64 + match e {
        Entry::Tmpl(t) => 40 + 4 * t.bound.len() + 12 * t.locs.len(),
        Entry::Leaf(l) => {
            40 + 4 * l.key.len()
                + l.succs
                    .iter()
                    .map(|s| {
                        16 + s
                            .iter()
                            .map(|(_, p)| {
                                24 + match p {
                                    Put::Id { .. } => 0,
                                    Put::Delta { ops, iops, .. } => ops_size(ops) + iops.as_deref().map_or(0, iops_size),
                                }
                            })
                            .sum::<usize>()
                    })
                    .sum::<usize>()
        }
    }
}

#[derive(Default, Clone, Copy)]
pub struct CacheStats {
    pub lookups: u64,
    pub hits: u64,
    pub stored: u64,
    pub replaced: u64,
    /// not stored: the entry alone, or the table with it, would exceed the budget
    pub too_big: u64,
    /// evaluations whose result could not be cached (tree-walker used, a change not expressible)
    pub uncacheable: u64,
}

thread_local! {
    static NEXT_ID: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}
/// A fresh number (never 0, never reused by this thread): for template versions and lists of changes.
fn fresh() -> u64 {
    NEXT_ID.with(|c| {
        let n = c.get() + 1;
        c.set(n);
        n
    })
}

/// A direct-mapped memo of fixed size: (a u64, an id) -> a value; a newer value replaces the older one
/// in its slot. (Slots are cells: a lookup is a load, with no borrow to check.)
pub struct Memo<T: Copy> {
    slots: Box<[std::cell::Cell<(u64, Id, T)>]>,
    mask: usize,
}
/// A type whose all-zero bits are a value (`zeroed`).
///
/// # Safety
/// The all-zero bit pattern must be a valid value of the type.
unsafe trait Zeroable {}
unsafe impl Zeroable for u32 {}
unsafe impl Zeroable for u64 {}
unsafe impl<T: Zeroable> Zeroable for std::cell::Cell<T> {}
unsafe impl<A: Zeroable, B: Zeroable, C: Zeroable> Zeroable for (A, B, C) {}
// (a bucket of empty ways: hashes 0 and no entries, `None` being the null pointer)
unsafe impl Zeroable for Bucket {}
/// `n` zeroed values, from zeroed memory (pages the program never touches stay untouched: a table that
/// stays small costs little memory however large it may grow).
fn zeroed<T: Zeroable>(n: usize) -> Box<[T]> {
    if n == 0 || std::mem::size_of::<T>() == 0 {
        return (0..n).map(|_| unsafe { std::mem::zeroed() }).collect();
    }
    let layout = std::alloc::Layout::array::<T>(n).expect("a table of a size that fits");
    // SAFETY: the layout has a non-zero size; the memory is zeroed, which is a valid `T` (`Zeroable`),
    // and it is handed to a box of the same layout.
    unsafe {
        let p = std::alloc::alloc_zeroed(layout) as *mut T;
        if p.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        Box::from_raw(std::ptr::slice_from_raw_parts_mut(p, n))
    }
}
impl<T: Copy + Default + Zeroable> Memo<T> {
    fn new(n: usize) -> Memo<T> {
        // (zeroed slots are empty: a key is never 0)
        Memo { slots: zeroed(n), mask: n - 1 }
    }
    /// The value at (a, b); `a` is never 0 (an empty slot).
    #[inline]
    fn get(&self, a: u64, b: Id) -> Option<T> {
        let s = self.slots[(mix(a, b as u64) as usize) & self.mask].get();
        (s.0 == a && s.1 == b).then_some(s.2)
    }
    #[inline]
    fn put(&self, a: u64, b: Id, v: T) {
        self.slots[(mix(a, b as u64) as usize) & self.mask].set((a, b, v));
    }
}
/// What a stored list of changes made of a given parent: (list, parent id) -> result id. Sound because
/// both keys are identities: an id names one value (for the life of the table, which is that of a
/// check), a list number one list of changes for the life of the thread.
pub type Applied = Memo<Id>;

/// The word of what a list of changes made of a value: (list, parent id) -> word. As `Applied`.
pub type Words = Memo<u64>;

/// What is at (value id, key id, kind of location): the element of a function (or `ABSENT`), or whether
/// a value is in a set or bag (`IN` / `OUT`). Finding it again costs a binary search with full
/// comparisons of the keys (records, for a bag of messages), while the same value and key recur in many
/// states. With identities for keys (see `Applied`): ((value id << 32 | key id) + 1, kind) -> what is there.
pub type Located = Memo<Id>;

/// A slot of the table: (hash, size charged, entry). Shared, so that a successor found from a leaf can
/// be built after the leaf was replaced (`Recipe`).
pub type Slot = (u64, usize, Entry);
/// The slots of the memo of domains (`Table::domain_ids`).
const DOMS: usize = 1 << 12;
/// The entries per bucket of `Table`.
const WAYS: usize = 4;
/// A bucket: the hash of each way inline (a lookup reads one cache line before the entry it finds),
/// newest first.
#[repr(align(64))]
#[derive(Default)]
struct Bucket {
    h: [u64; WAYS],
    e: [Option<std::rc::Rc<Slot>>; WAYS],
}
pub struct Table {
    buckets: Box<[Bucket]>,
    mask: usize,
    pub applied: Applied,
    /// the word of what a list of changes makes of a value (`delta_word`), as `Applied`
    pub words: Words,
    /// the ids of the domain of a function, by its id (direct-mapped, as `Applied`)
    doms: RefCell<Vec<(Id, Option<std::rc::Rc<[Id]>>)>>,
    pub located: Located,
    pub used: usize,
    pub budget: usize,
    pub peak: usize,
    pub n: CacheStats,
    /// changes applied and locations found (`Applied`, `Located`): lookups, and how many were computed
    pub memo: [std::cell::Cell<u64>; 4],
    /// the number of each distinct list of changes (by the ids of its values), so that equal changes
    /// stored by different entries share their results in `Applied`
    lists: std::collections::HashMap<Box<[Id]>, u64>,
}

impl Table {
    pub fn new(budget_bytes: usize) -> Table {
        // about one slot per 512 bytes of budget; the slot array is part of the budget
        let mut slots = (budget_bytes / 512).max(16 * WAYS);
        if !slots.is_power_of_two() {
            slots = slots.next_power_of_two() / 2;
        }
        let v = zeroed::<Bucket>(slots / WAYS);
        let used = slots / WAYS * std::mem::size_of::<Bucket>();
        Table {
            buckets: v,
            mask: slots / WAYS - 1,
            applied: Applied::new(1 << 18),
            words: Words::new(1 << 15),
            doms: RefCell::new(vec![(0, None); DOMS]),
            located: Located::new(1 << 16),
            used,
            budget: budget_bytes.max(used),
            peak: used,
            n: CacheStats::default(),
            memo: Default::default(),
            lists: Default::default(),
        }
    }
    /// The slot whose hash is `h`.
    #[inline]
    fn slot(&self, h: u64) -> Option<&std::rc::Rc<Slot>> {
        let b = &self.buckets[(h as usize) & self.mask];
        (0..WAYS).find(|&w| b.h[w] == h).and_then(|w| b.e[w].as_ref())
    }
    #[inline]
    pub fn get(&self, h: u64) -> Option<&Entry> {
        self.slot(h).map(|b| &b.2)
    }
    pub fn put(&mut self, h: u64, e: Entry) {
        let size = entry_size(&e);
        let b = &self.buckets[(h as usize) & self.mask];
        // the way it goes to: the entry with the same hash, else an empty way, else the oldest leaf (a
        // template is given up only by a bucket of templates: its leaves go with it), and what it frees
        let w = (0..WAYS)
            .find(|&w| b.h[w] == h && b.e[w].is_some())
            .or_else(|| (0..WAYS).find(|&w| b.e[w].is_none()))
            .or_else(|| (0..WAYS).rev().find(|&w| matches!(b.e[w].as_deref(), Some((_, _, Entry::Leaf(_))))))
            .unwrap_or(WAYS - 1);
        let old = b.e[w].as_ref().map_or(0, |x| x.1);
        // no entry may take more than a small share of the table, and the total stays within the budget
        if size > 4 * 1024 || self.used - old + size > self.budget {
            self.n.too_big += 1;
            return;
        }
        if old > 0 {
            self.n.replaced += 1;
        }
        self.used = self.used - old + size;
        self.peak = self.peak.max(self.used);
        let b = &mut self.buckets[(h as usize) & self.mask];
        // (newest first: the ways before `w` move one down)
        b.e[w] = None;
        b.h[..=w].rotate_right(1);
        b.e[..=w].rotate_right(1);
        b.h[0] = h;
        b.e[0] = Some(std::rc::Rc::new((h, size, e)));
        self.n.stored += 1;
    }

    /// The number of a list of changes (canonical values): the same for equal lists. None when a value
    /// has no id. Bounded: past 2^20 lists the numbering starts again from fresh numbers (a list then
    /// gets a new number, which is still sound: equal numbers still mean equal lists).
    fn list_number(&mut self, ops: &[DOp]) -> Option<u64> {
        let mut key = Vec::with_capacity(ops.len() * 3);
        for o in ops {
            match o {
                DOp::Bag { e, plus } => key.extend([1 + *plus as Id, hc::id(e)?]),
                DOp::Set { e, add } => key.extend([3 + *add as Id, hc::id(e)?]),
                DOp::Exc { path, v } => {
                    key.extend([5, path.len() as Id, hc::id(v)?]);
                    for p in path {
                        key.push(hc::id(p)?);
                    }
                }
            }
        }
        if self.lists.len() >= 1 << 20 {
            self.lists.clear();
        }
        Some(*self.lists.entry(key.into_boxed_slice()).or_insert_with(fresh))
    }

    #[inline]
    fn count(&self, i: usize) {
        self.memo[i].set(self.memo[i].get() + 1);
    }

    /// The template for (unit, bound ids).
    #[inline]
    pub fn template(&self, h0: u64, unit: u32, bound: &[Id]) -> Option<&Tmpl> {
        match self.get(h0) {
            Some(Entry::Tmpl(t)) if t.unit == unit && same_ids(&t.bound, bound) => Some(t),
            _ => None,
        }
    }
    /// The leaf of template version `version` whose key is `key`.
    #[inline]
    pub fn leaf(&self, version: u64, key: &[Id]) -> Option<&Leaf> {
        match self.get(leaf_hash(version, key)) {
            Some(Entry::Leaf(l)) if l.version == version && same_ids(&l.key, key) => Some(l),
            _ => None,
        }
    }
    /// The same, with the slot that holds it; `h` is its `leaf_hash`.
    #[inline]
    pub fn leaf_slot(&self, h: u64, version: u64, key: &[Id]) -> Option<(&std::rc::Rc<Slot>, &Leaf)> {
        match self.slot(h) {
            Some(b) => match &b.2 {
                Entry::Leaf(l) if l.version == version && same_ids(&l.key, key) => Some((b, l)),
                _ => None,
            },
            None => None,
        }
    }

    /// What is at `loc` in the state whose variables have the ids `cur`. None when that cannot be told
    /// (the variable's value is not interned, or the element is not).
    #[inline(always)]
    pub fn locate(&self, cur: &[Id], loc: LocId) -> Option<Id> {
        let c = cur[loc.var as usize];
        if c >= NOT_INTERNED {
            return None;
        }
        if loc.kind == LocKind::Whole {
            return Some(c);
        }
        self.locate_in(c, loc.kind, loc.key)
    }
    /// What is at `key` (`Elem`: the element, or `ABSENT`; `Member`: `IN` or `OUT`) in the value `c`.
    #[inline(always)]
    pub fn locate_in(&self, c: Id, kind: LocKind, key: Id) -> Option<Id> {
        let k = (((c as u64) << 32) | key as u64) + 1;
        self.count(2);
        if let Some(r) = self.located.get(k, kind as Id) {
            return Some(r);
        }
        self.locate_miss(c, kind, key, k)
    }
    #[cold]
    #[inline(never)]
    fn locate_miss(&self, c: Id, kind: LocKind, key: Id, k: u64) -> Option<Id> {
        self.count(3);
        let r = locate_slow(c, LocId { var: 0, kind, key })?;
        self.located.put(k, kind as Id, r);
        Some(r)
    }

    /// The ids of the domain of the function (tuple, record) with id `f`, in order; None when it is not a
    /// function or an element of its domain has no id.
    #[inline]
    pub fn domain_ids(&self, f: Id) -> Option<std::rc::Rc<[Id]>> {
        if f >= NOT_INTERNED || hc::is_immediate(f) {
            return None;
        }
        let slot = (mix(f as u64, 0xD0) as usize) & (DOMS - 1);
        if let (x, Some(d)) = &self.doms.borrow()[slot] {
            if *x == f {
                return Some(d.clone());
            }
        }
        let d: std::rc::Rc<[Id]> = match hc::value(f) {
            Value::Fcn(fc) => fc.dom.iter().map(hc::id_if_canonical).collect::<Option<Vec<Id>>>()?.into(),
            Value::Tuple(t) => (1..=t.len() as i64).map(|i| hc::int_id(i)).collect::<Option<Vec<Id>>>()?.into(),
            Value::Record(r) => r.names.iter().map(|nm| hc::id(&Value::Str(*nm))).collect::<Option<Vec<Id>>>()?.into(),
            _ => return None,
        };
        self.doms.borrow_mut()[slot] = (f, Some(d.clone()));
        Some(d)
    }
    /// The word of the parent's value with the changes `ops` (numbered `list`) applied (`delta_word`),
    /// remembered.
    #[inline]
    pub fn delta_word(&self, ids: hc::Local, parent: Id, list: u64, ops: &[IdOp]) -> Option<u64> {
        if let Some(w) = self.words.get(list, parent) {
            return Some(w);
        }
        let w = delta_word(self, ids, parent, ops)?;
        self.words.put(list, parent, w);
        Some(w)
    }
    /// The id of the parent's value with the changes `ops` (numbered `list`) applied, remembered.
    #[inline]
    pub fn applied(&self, parent: Id, list: u64, apply: impl FnOnce(&Value) -> Option<Value>) -> Option<Id> {
        if parent >= NOT_INTERNED {
            return None;
        }
        self.count(0);
        if let Some(r) = self.applied.get(list, parent) {
            return Some(r);
        }
        self.count(1);
        let r = hc::id(&apply(&hc::value(parent))?)?;
        self.applied.put(list, parent, r);
        Some(r)
    }
}

/// The word (`value_word`) of the value with id `parent` after the changes `ops`, computed from the
/// parent's word without building that value: each change replaces the terms of the elements it
/// changes (see `value::fn_tag`). None when a change would not apply (`apply_ops` would fail) or this
/// cannot tell; the value has to be built then.
pub fn delta_word(t: &Table, ids: hc::Local, parent: Id, ops: &[IdOp]) -> Option<u64> {
    if parent >= NOT_INTERNED {
        return None;
    }
    let sh = ids.shape(parent);
    let mut w = ids.word(parent);
    let mut len = sh.len as usize;
    // what earlier changes of the list did to the elements they touched: (key id, what is there now)
    let mut done: [(Id, Id); 8] = [(0, 0); 8];
    let mut nd = 0;
    for op in ops {
        if nd == usize::MAX {
            // (a change after an EXCEPT of the same value: not followed here)
            return None;
        }
        match op {
            IdOp::Bag { e, we, plus } => {
                // as `stdlib::bag_one`
                if sh.kind != hc::ShapeKind::Fcn || !sh.bag {
                    return None;
                }
                let c = match done[..nd].iter().rev().find(|d| d.0 == *e) {
                    Some(d) => d.1,
                    None => t.locate_in(parent, LocKind::Elem, *e)?,
                };
                let old = if c == ABSENT { 0 } else { hc::int_of(c)? };
                if old == 0 && !*plus {
                    continue;
                }
                // (as `bag_add`: past 2^31 - 1 the change fails)
                let new = if *plus { old + 1 } else { old - 1 };
                if new > i32::MAX as i64 {
                    return None;
                }
                if old > 0 {
                    w = w.wrapping_sub(entry_term(*we, int_word(old)));
                } else {
                    w = w.wrapping_sub(fn_tag(len)).wrapping_add(fn_tag(len + 1));
                    len += 1;
                }
                if new > 0 {
                    w = w.wrapping_add(entry_term(*we, int_word(new)));
                } else {
                    w = w.wrapping_sub(fn_tag(len)).wrapping_add(fn_tag(len - 1));
                    len -= 1;
                }
                if nd == done.len() {
                    return None;
                }
                done[nd] = (*e, if new > 0 { hc::int_id(new)? } else { ABSENT });
                nd += 1;
            }
            IdOp::Set { e, we, add } => {
                // as `set_one`
                if sh.kind != hc::ShapeKind::Set {
                    return None;
                }
                let m = match done[..nd].iter().rev().find(|d| d.0 == *e) {
                    Some(d) => d.1,
                    None => t.locate_in(parent, LocKind::Member, *e)?,
                };
                if (m == IN) == *add {
                    continue;
                }
                let te = elem_term(*we);
                if *add {
                    w = w.wrapping_sub(set_tag(len)).wrapping_add(set_tag(len + 1)).wrapping_add(te);
                    len += 1;
                } else {
                    w = w.wrapping_sub(set_tag(len)).wrapping_add(set_tag(len - 1)).wrapping_sub(te);
                    len -= 1;
                }
                if nd == done.len() {
                    return None;
                }
                done[nd] = (*e, if *add { IN } else { OUT });
                nd += 1;
            }
            IdOp::Exc { path, wv } => {
                // as `except_with` at a path whose every key is in the domain (else `apply_ops` fails)
                if nd > 0 || path.is_empty() {
                    // (an EXCEPT after another change of the same value: not followed here)
                    return None;
                }
                w = exc_word(t, ids, parent, w, path, *wv)?;
                nd = usize::MAX;
            }
        }
    }
    Some(w)
}
/// What the changes `ops` of variable `var` add to its word, when they are EXCEPTs at keys whose old
/// values are at locations of the leaf (`locs`, with the values `key`): the same for every state the
/// leaf applies to, as those values are part of what selects it.
fn key_shift(t: &Table, var: u32, ops: &[IdOp], locs: &[LocId], key: &[Id]) -> Option<u64> {
    let ids = hc::Local::get();
    let mut seen: Vec<Id> = vec![];
    let mut d = 0u64;
    for op in ops {
        let IdOp::Exc { path, wv } = op else { return None };
        let (k, wk) = *path.first()?;
        if seen.contains(&k) {
            return None;
        }
        seen.push(k);
        let j = locs.iter().position(|l| l.var == var && l.kind == LocKind::Elem && l.key == k)?;
        let old = key[j];
        if old == ABSENT || old >= NOT_INTERNED {
            return None;
        }
        let wold = ids.word(old);
        let wnew = if path.len() == 1 { *wv } else { exc_word(t, ids, old, wold, &path[1..], *wv)? };
        d = d.wrapping_add(entry_term(wk, wnew)).wrapping_sub(entry_term(wk, wold));
    }
    Some(d)
}
/// The word of the function `f` (word `w`) with `f[path]` replaced by a value of word `wv`.
fn exc_word(t: &Table, ids: hc::Local, f: Id, w: u64, path: &[(Id, u64)], wv: u64) -> Option<u64> {
    if ids.shape(f).kind != hc::ShapeKind::Fcn {
        return None;
    }
    let (k, wk) = path[0];
    let old = t.locate_in(f, LocKind::Elem, k)?;
    if old == ABSENT || old >= NOT_INTERNED {
        return None;
    }
    let wold = ids.word(old);
    let wnew = if path.len() == 1 { wv } else { exc_word(t, ids, old, wold, &path[1..], wv)? };
    Some(w.wrapping_sub(entry_term(wk, wold)).wrapping_add(entry_term(wk, wnew)))
}

#[cold]
fn locate_slow(c: Id, loc: LocId) -> Option<Id> {
    let (v, k) = (hc::value(c), hc::value(loc.key));
    match loc.kind {
        // (a key that cannot be compared with the domain's: not something an entry can say)
        LocKind::Elem => match elem_at_checked(&v, &k)? {
            Some(x) => hc::id(&x),
            None => Some(ABSENT),
        },
        LocKind::Member => member_of(&v, &k).map(|b| if b { IN } else { OUT }),
        LocKind::Whole => unreachable!(),
    }
}

#[inline]
pub fn mix(h: u64, x: u64) -> u64 {
    let m = ((h ^ x) as u128).wrapping_mul(0xD6E8_FEB8_6659_FD93u128);
    ((m as u64) ^ ((m >> 64) as u64)).wrapping_add(0x9E37_79B9_7F4A_7C15)
}
/// Where a template is found: the unit and the bound ids.
#[inline]
pub fn template_hash(unit: u32, bound: &[Id]) -> u64 {
    let mut h = mix(0x5EED, unit as u64);
    for &b in bound {
        h = mix(h, b as u64);
    }
    h
}
/// Whether two short lists of ids are equal (inline: a call to `memcmp` costs more than these few ids).
#[inline(always)]
fn same_ids(a: &[Id], b: &[Id]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x == y)
}
/// `leaf_hash` of an empty key (the hash goes on with `mix` of each id of the key).
#[inline]
pub fn leaf_hash_start(version: u64) -> u64 {
    mix(0x1EAF, version)
}
/// Where a leaf is found: its template version and key.
#[inline]
pub fn leaf_hash(version: u64, key: &[Id]) -> u64 {
    let mut h = leaf_hash_start(version);
    for &k in key {
        h = mix(h, k as u64);
    }
    h
}

/// `f[k]`: Some(None) when `k` is not in the domain (or `f` is not a function), None when that cannot be
/// told (a comparison of `k` with the domain fails).
pub fn elem_at_checked(f: &Value, k: &Value) -> Option<Option<Value>> {
    match f {
        Value::Fcn(fc) => match bsearch(&fc.dom, k) {
            Ok(Some(i)) => Some(Some(fc.vals[i].clone())),
            Ok(None) => Some(None),
            Err(_) => None,
        },
        // (a key of another kind than the domain's cannot be compared with it either)
        Value::Tuple(_) if !matches!(k, Value::Int(_)) => None,
        Value::Record(_) if !matches!(k, Value::Str(_)) => None,
        _ => Some(elem_at(f, k)),
    }
}
/// `f[k]` without an error: None when `k` is not in the domain (or `f` is not a function).
pub fn elem_at(f: &Value, k: &Value) -> Option<Value> {
    match f {
        Value::Fcn(fc) => match bsearch(&fc.dom, k) {
            Ok(Some(i)) => Some(fc.vals[i].clone()),
            _ => None,
        },
        Value::Tuple(t) => match k {
            Value::Int(i) if *i >= 1 && *i as usize <= t.len() => Some(t[*i as usize - 1].clone()),
            _ => None,
        },
        Value::Record(r) => match k {
            Value::Str(s) => r.get(*s).cloned(),
            _ => None,
        },
        _ => None,
    }
}
/// Whether `e` is in the set `v`, or in the domain of the function (bag) `v`. None when that cannot be told.
pub fn member_of(v: &Value, e: &Value) -> Option<bool> {
    match v {
        Value::Set(s) => s.contains(e).ok(),
        Value::Fcn(f) => bsearch(&f.dom, e).ok().map(|x| x.is_some()),
        Value::Tuple(t) => match e {
            Value::Int(i) => Some(*i >= 1 && *i as usize <= t.len()),
            _ => None,
        },
        Value::Record(r) => match e {
            Value::Str(s) => Some(r.get(*s).is_some()),
            _ => None,
        },
        _ => None,
    }
}

/// A recorded location as ids. None when its key cannot be interned.
fn loc_id(l: &Loc) -> Option<LocId> {
    Some(match l {
        Loc::Whole(i) => LocId { var: *i, kind: LocKind::Whole, key: 0 },
        Loc::Elem(i, k) => LocId { var: *i, kind: LocKind::Elem, key: hc::id(k)? },
        Loc::Member(i, k) => LocId { var: *i, kind: LocKind::Member, key: hc::id(k)? },
    })
}

/// A recorded evaluation of a unit, to be stored.
pub struct Recorded<'a> {
    pub unit: u32,
    pub bound: &'a [Id],
    pub reads: &'a [(Loc, Value)],
    /// per successor, one write per variable
    pub succs: &'a [Vec<Write>],
}

/// Stores an evaluation of a unit in the state `cur` (ids of its variables): the template, extended
/// with the locations this evaluation read, and a leaf. False when it cannot be stored.
pub fn store(t: &mut Table, cur: &[Id], r: Recorded) -> bool {
    // A large value read whole makes a poor key: it rarely recurs. Such an evaluation is not stored (and
    // its unit soon backs off).
    if r.reads.iter().any(|(_, v)| vsize(v) > 512) {
        return false;
    }
    let h0 = template_hash(r.unit, r.bound);
    // the locations that pick the entry: those of earlier evaluations of this unit with these bound
    // values, and any new ones
    let (mut locs, version) = match t.template(h0, r.unit, r.bound) {
        Some(tm) => (tm.locs.to_vec(), tm.version),
        None => (vec![], 0),
    };
    let had = locs.len();
    for (l, _) in r.reads {
        let Some(l) = loc_id(l) else { return false };
        if !locs.contains(&l) {
            locs.push(l);
        }
    }
    if locs.len() > 24 {
        return false;
    }
    let mut key = Vec::with_capacity(locs.len());
    for &l in &locs {
        match t.locate(cur, l) {
            Some(x) => key.push(x),
            None => return false,
        }
    }
    let mut succs = Vec::with_capacity(r.succs.len());
    for s in r.succs {
        let mut puts = vec![];
        for (i, w) in s.iter().enumerate() {
            match w {
                Write::Delta(ops) if ops.is_empty() => {}
                Write::Delta(ops) => {
                    let Some(ops) = ops.iter().map(canon_op).collect::<Option<Vec<DOp>>>() else { return false };
                    let Some(id) = t.list_number(&ops) else { return false };
                    let iops = ops.iter().map(id_op).collect::<Option<Vec<IdOp>>>().map(|v| v.into_boxed_slice());
                    let shift = iops.as_deref().and_then(|o| key_shift(t, i as u32, o, &locs, &key));
                    puts.push((i as u32, Put::Delta { id, ops: ops.into_boxed_slice(), iops, shift }));
                }
                // (an absolute value, even one equal to the parent's here: in another state it is not)
                Write::Val(v) => match hc::id(v) {
                    Some(x) => puts.push((i as u32, Put::Id { id: x, word: hc::word(x) })),
                    None => return false,
                },
            }
        }
        succs.push(puts.into_boxed_slice());
    }
    let version = if version == 0 || locs.len() != had {
        let version = fresh();
        t.put(h0, Entry::Tmpl(Tmpl { unit: r.unit, bound: r.bound.into(), locs: locs.into_boxed_slice(), version }));
        version
    } else {
        version
    };
    t.put(leaf_hash(version, &key), Entry::Leaf(Leaf { version, key: key.into_boxed_slice(), succs: succs.into_boxed_slice() }));
    true
}
fn canon_op(o: &DOp) -> Option<DOp> {
    use hc::canon as c;
    Some(match o {
        DOp::Bag { e, plus } => DOp::Bag { e: c(e)?, plus: *plus },
        DOp::Set { e, add } => DOp::Set { e: c(e)?, add: *add },
        DOp::Exc { path, v } => DOp::Exc { path: path.iter().map(c).collect::<Option<Vec<_>>>()?, v: c(v)? },
    })
}

/// The ids of the variables of a state; `NOT_INTERNED` for a value that cannot be interned.
pub fn ids_of(vals: &[Value], out: &mut Vec<Id>) {
    out.clear();
    out.extend(vals.iter().map(|v| hc::id(v).unwrap_or(NOT_INTERNED)));
}

/// Successors as rows of ids, in the order they are found, with the action of each. A variable whose
/// value cannot be interned is `NOT_INTERNED + i`, `i` an index into `opaque`.
#[derive(Default)]
pub struct Rows {
    /// the rows built, `nv` ids each (`ROW` entries point into it)
    pub ids: Vec<Id>,
    pub opaque: Vec<Value>,
    pub meta: RowMeta,
}
/// A successor found from a leaf whose row is not built yet: most are known states, which need none.
pub struct Recipe {
    pub slot: std::rc::Rc<Slot>,
    pub succ: u32,
    /// the unit's expression (what an error applying a change would be reported at)
    pub n: crate::ast::N,
}
impl Recipe {
    /// The changes of this successor.
    pub fn puts(&self) -> &[(u32, Put)] {
        match &self.slot.2 {
            Entry::Leaf(l) => &l.succs[self.succ as usize],
            Entry::Tmpl(_) => unreachable!("a recipe refers to a leaf"),
        }
    }
}
/// A successor in `Rows`, in the order they were found.
#[derive(Clone, Copy)]
pub struct Found {
    /// its fingerprint when it is known (0: to be computed from its row)
    pub fp: u64,
    /// the action that found it
    pub act: u32,
    /// where it is: a row of `Rows::ids` (below `RECIPE`), or `RECIPE` + its index in `recipes`
    pub src: u32,
}
/// What `Rows` knows about its successors besides the ids of those that are built.
#[derive(Default)]
pub struct RowMeta {
    pub found: Vec<Found>,
    pub recipes: Vec<Recipe>,
    /// the action whose successors are being found
    pub cur_act: u32,
    rows: u32,
}
pub const RECIPE: u32 = 1 << 31;
impl RowMeta {
    /// A row was added (after its ids), with its fingerprint (0: unknown).
    #[inline]
    pub fn added(&mut self, fp: u64) {
        self.found.push(Found { fp, act: self.cur_act, src: self.rows });
        self.rows += 1;
    }
    /// A successor that is to be built from a leaf, if it turns out to be new.
    #[inline]
    pub fn recipe(&mut self, fp: u64, r: Recipe) {
        self.found.push(Found { fp, act: self.cur_act, src: RECIPE + self.recipes.len() as u32 });
        self.recipes.push(r);
    }
    /// The recipe of successor `i`, if it is one.
    #[inline]
    pub fn recipe_of(&self, i: usize) -> Option<&Recipe> {
        let s = self.found[i].src;
        (s >= RECIPE).then(|| &self.recipes[(s - RECIPE) as usize])
    }
}
/// Where `Rows` was, to go back to (`Rows::truncate`).
#[derive(Clone, Copy)]
pub struct RowsMark {
    ids: usize,
    found: usize,
    recipes: usize,
    rows: u32,
}
impl Rows {
    pub fn clear(&mut self) {
        self.ids.clear();
        self.opaque.clear();
        let m = &mut self.meta;
        m.found.clear();
        m.recipes.clear();
        m.rows = 0;
    }
    #[inline]
    pub fn mark(&self) -> RowsMark {
        RowsMark { ids: self.ids.len(), found: self.meta.found.len(), recipes: self.meta.recipes.len(), rows: self.meta.rows }
    }
    pub fn truncate(&mut self, k: RowsMark) {
        self.ids.truncate(k.ids);
        let m = &mut self.meta;
        m.found.truncate(k.found);
        m.recipes.truncate(k.recipes);
        m.rows = k.rows;
    }
    /// The number of successors.
    pub fn len(&self) -> usize {
        self.meta.found.len()
    }
    /// The row of successor `i`, when it is built.
    #[inline]
    pub fn row(&self, i: usize, nv: usize) -> Option<&[Id]> {
        let s = self.meta.found[i].src;
        if s >= RECIPE {
            return None;
        }
        let s = s as usize;
        Some(&self.ids[s * nv..(s + 1) * nv])
    }
    /// Adds a successor given as values. Only a value that is already canonical is taken by its id; any
    /// other is kept as it is, and interned only if the successor turns out to be a new state (most
    /// successors are not, and interning costs a probe of a table as large as all the values found).
    pub fn push_values(&mut self, vals: &[Value]) {
        for v in vals {
            let x = match hc::id_if_canonical(v) {
                Some(x) => x,
                None => {
                    self.opaque.push(v.clone());
                    NOT_INTERNED + (self.opaque.len() - 1) as Id
                }
            };
            self.ids.push(x);
        }
        self.meta.added(0);
    }
    /// The value of a row's entry.
    pub fn value(&self, x: Id) -> Value {
        if x >= NOT_INTERNED {
            self.opaque[(x - NOT_INTERNED) as usize].clone()
        } else {
            hc::value(x)
        }
    }
}
