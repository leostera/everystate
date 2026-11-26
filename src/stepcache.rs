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
//! Memory: one table of a fixed number of slots, direct-mapped, a newer entry replaces the older one in
//! its slot. Every entry is charged its own size plus that of the changes it holds, and an entry that
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
    Id(Id),
    /// the parent's value with these changes (values canonical); `id` names the list for `Applied`
    Delta { id: u64, ops: Box<[DOp]> },
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
                                    Put::Id(_) => 0,
                                    Put::Delta { ops, .. } => ops_size(ops),
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

/// What a stored list of changes made of a given parent: (parent id, list) -> result id. Direct-mapped
/// and fixed in size; a newer result replaces the older one in its slot. Sound because both keys are
/// identities: an id names one value (for the life of the table, which is that of a check), a list
/// number one list of changes for the life of the thread.
pub struct Applied {
    slots: Vec<(u64, Id, Id)>,
    mask: usize,
}
impl Applied {
    fn new(n: usize) -> Applied {
        Applied { slots: vec![(0, 0, 0); n], mask: n - 1 }
    }
}

/// What is at (value id, key id, kind of location): the element of a function (or `ABSENT`), or whether
/// a value is in a set or bag (`IN` / `OUT`). Finding it again costs a binary search with full
/// comparisons of the keys (records, for a bag of messages), while the same value and key recur in many
/// states. Direct-mapped and fixed in size, with identities for keys (see `Applied`).
pub struct Located {
    slots: Vec<(u64, u32, Id)>,
    mask: usize,
}
impl Located {
    fn new(n: usize) -> Located {
        Located { slots: vec![(0, 0, 0); n], mask: n - 1 }
    }
}

pub struct Table {
    slots: Vec<Option<Box<(u64, usize, Entry)>>>,
    mask: usize,
    pub applied: RefCell<Applied>,
    pub located: RefCell<Located>,
    pub used: usize,
    pub budget: usize,
    pub peak: usize,
    pub n: CacheStats,
    /// changes applied and locations found (`Applied`, `Located`): lookups, and how many were computed
    pub memo: std::cell::Cell<[u64; 4]>,
    /// the number of each distinct list of changes (by the ids of its values), so that equal changes
    /// stored by different entries share their results in `Applied`
    lists: std::collections::HashMap<Box<[Id]>, u64>,
}

impl Table {
    pub fn new(budget_bytes: usize) -> Table {
        // about one slot per 512 bytes of budget; the slot array is part of the budget
        let mut slots = (budget_bytes / 512).max(16);
        if !slots.is_power_of_two() {
            slots = slots.next_power_of_two() / 2;
        }
        let mut v = Vec::new();
        v.resize_with(slots, || None);
        let used = slots * 8;
        Table {
            slots: v,
            mask: slots - 1,
            applied: RefCell::new(Applied::new(1 << 18)),
            located: RefCell::new(Located::new(1 << 16)),
            used,
            budget: budget_bytes.max(used),
            peak: used,
            n: CacheStats::default(),
            memo: Default::default(),
            lists: Default::default(),
        }
    }
    #[inline]
    pub fn get(&self, h: u64) -> Option<&Entry> {
        match &self.slots[(h as usize) & self.mask] {
            Some(b) if b.0 == h => Some(&b.2),
            _ => None,
        }
    }
    pub fn put(&mut self, h: u64, e: Entry) {
        let size = entry_size(&e);
        let i = (h as usize) & self.mask;
        let old = self.slots[i].as_ref().map_or(0, |b| b.1);
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
        self.slots[i] = Some(Box::new((h, size, e)));
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
        let mut m = self.memo.get();
        m[i] += 1;
        self.memo.set(m);
    }

    /// The template for (unit, bound ids).
    #[inline]
    pub fn template(&self, h0: u64, unit: u32, bound: &[Id]) -> Option<&Tmpl> {
        match self.get(h0) {
            Some(Entry::Tmpl(t)) if t.unit == unit && *t.bound == *bound => Some(t),
            _ => None,
        }
    }
    /// The leaf of template version `version` whose key is `key`.
    #[inline]
    pub fn leaf(&self, version: u64, key: &[Id]) -> Option<&Leaf> {
        match self.get(leaf_hash(version, key)) {
            Some(Entry::Leaf(l)) if l.version == version && *l.key == *key => Some(l),
            _ => None,
        }
    }

    /// What is at `loc` in the state whose variables have the ids `cur`. None when that cannot be told
    /// (the variable's value is not interned, or the element is not).
    #[inline]
    pub fn locate(&self, cur: &[Id], loc: LocId) -> Option<Id> {
        let c = cur[loc.var as usize];
        if c >= NOT_INTERNED {
            return None;
        }
        if loc.kind == LocKind::Whole {
            return Some(c);
        }
        let k = ((c as u64) << 32) | loc.key as u64;
        let kind = loc.kind as u32;
        self.count(2);
        let slot = (mix(k, kind as u64) as usize) & self.located.borrow().mask;
        {
            let m = self.located.borrow();
            let s = &m.slots[slot];
            if s.0 == k && s.1 == kind {
                return Some(s.2);
            }
        }
        self.count(3);
        let r = locate_slow(c, loc)?;
        self.located.borrow_mut().slots[slot] = (k, kind, r);
        Some(r)
    }

    /// The id of the parent's value with the changes `ops` (numbered `list`) applied, remembered.
    #[inline]
    pub fn applied(&self, parent: Id, list: u64, apply: impl FnOnce(&Value) -> Option<Value>) -> Option<Id> {
        if parent >= NOT_INTERNED {
            return None;
        }
        let slot = (mix(list, parent as u64) as usize) & self.applied.borrow().mask;
        self.count(0);
        {
            let m = self.applied.borrow();
            let s = &m.slots[slot];
            if s.0 == list && s.1 == parent {
                return Some(s.2);
            }
        }
        self.count(1);
        let r = hc::id(&apply(&hc::value(parent))?)?;
        self.applied.borrow_mut().slots[slot] = (list, parent, r);
        Some(r)
    }
}

#[cold]
fn locate_slow(c: Id, loc: LocId) -> Option<Id> {
    let (v, k) = (hc::value(c), hc::value(loc.key));
    match loc.kind {
        LocKind::Elem => match elem_at(&v, &k) {
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
/// Where a leaf is found: its template version and key.
#[inline]
pub fn leaf_hash(version: u64, key: &[Id]) -> u64 {
    let mut h = mix(0x1EAF, version);
    for &k in key {
        h = mix(h, k as u64);
    }
    h
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
                    puts.push((i as u32, Put::Delta { id, ops: ops.into_boxed_slice() }));
                }
                // (an absolute value, even one equal to the parent's here: in another state it is not)
                Write::Val(v) => match hc::id(v) {
                    Some(x) => puts.push((i as u32, Put::Id(x))),
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
    pub ids: Vec<Id>,
    pub opaque: Vec<Value>,
    pub act: Vec<u32>,
    /// the action whose successors are being found
    pub cur_act: u32,
}
impl Rows {
    pub fn clear(&mut self) {
        self.ids.clear();
        self.opaque.clear();
        self.act.clear();
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
        self.act.push(self.cur_act);
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
