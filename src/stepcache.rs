//! On by default with the compiled evaluator (EVERYSTATE_STEP_CACHE=off turns it off): a bounded
//! cache of local steps.
//!
//! A *unit* is an action instance of a compiled plan (what is left of an action below its top-level
//! disjunctions, existential quantifiers and inlined definitions). When a unit is evaluated the compiled
//! code notes what it reads of the current state: a whole variable, one element `f[k]`, or whether a
//! value is in a set / bag variable. The unit's result is a list of successors, each given per variable
//! as a value or as a change to the parent's value (unchanged, an element put into or taken out of a set
//! or bag, an EXCEPT at a path). An entry holds (unit, bound values, reads with their values, successors);
//! a later state in which every read has the same value gets the successors by applying the changes.
//!
//! Soundness: a hit compares the unit, the bound values and every read in full (the hash only finds
//! the entry). Nothing is stored for an evaluation that failed, used the tree-walker (whose reads are not
//! noted), or whose changes could not be expressed.
//!
//! Memory: one table of a fixed number of slots, direct-mapped, a newer entry replaces the older one in
//! its slot. Every entry is charged its own size plus the size of every value it holds, and an entry that
//! would take the table over its budget (EVERYSTATE_STEP_CACHE_MB, default 32) is not stored.
use crate::intern::R;
use crate::value::*;

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
pub struct Leaf {
    pub unit: u32,
    pub bound: Vec<Value>,
    pub reads: Vec<(Loc, Value)>,
    /// per successor, one write per variable
    pub succs: Vec<Vec<Write>>,
}
pub struct Tmpl {
    pub unit: u32,
    pub bound: Vec<Value>,
    pub locs: Vec<Loc>,
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
fn loc_size(l: &Loc) -> usize {
    24 + match l {
        Loc::Whole(_) => 0,
        Loc::Elem(_, k) | Loc::Member(_, k) => vsize(k),
    }
}
fn entry_size(e: &Entry) -> usize {
    let vals = |vs: &[Value]| vs.iter().map(vsize).sum::<usize>();
    64 + match e {
        Entry::Tmpl(t) => 24 + vals(&t.bound) + t.locs.iter().map(loc_size).sum::<usize>(),
        Entry::Leaf(l) => {
            48 + vals(&l.bound)
                + l.reads.iter().map(|(loc, v)| loc_size(loc) + vsize(v)).sum::<usize>()
                + l.succs
                    .iter()
                    .map(|s| {
                        24 + s
                            .iter()
                            .map(|w| {
                                32 + match w {
                                    Write::Val(v) => vsize(v),
                                    Write::Delta(ops) => ops
                                        .iter()
                                        .map(|o| {
                                            40 + match o {
                                                DOp::Bag { e, .. } | DOp::Set { e, .. } => vsize(e),
                                                DOp::Exc { path, v } => 24 + vals(path) + vsize(v),
                                            }
                                        })
                                        .sum::<usize>(),
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

pub struct Table {
    slots: Vec<Option<Box<(u64, usize, Entry)>>>,
    mask: usize,
    pub used: usize,
    pub budget: usize,
    pub peak: usize,
    pub n: CacheStats,
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
        Table { slots: v, mask: slots - 1, used, budget: budget_bytes.max(used), peak: used, n: CacheStats::default() }
    }
    #[inline]
    pub fn get(&self, h: u64) -> Option<&Entry> {
        match &self.slots[(h as usize) & self.mask] {
            Some(b) if b.0 == h => Some(&b.2),
            _ => None,
        }
    }
    pub fn put(&mut self, h: u64, e: Entry) {
        let e = canon_entry(e);
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
}

#[inline]
pub fn mix(h: u64, x: u64) -> u64 {
    let m = ((h ^ x) as u128).wrapping_mul(0xD6E8_FEB8_6659_FD93u128);
    ((m as u64) ^ ((m >> 64) as u64)).wrapping_add(0x9E37_79B9_7F4A_7C15)
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
const ABSENT: u64 = 0x0A85_E271;
/// The word that stands for what is at `loc` in a state (for hashing).
pub fn word_at(vals: &[Value], loc: &Loc) -> Option<u64> {
    match loc {
        Loc::Whole(i) => value_word(&vals[*i as usize]).ok(),
        Loc::Elem(i, k) => match elem_at(&vals[*i as usize], k) {
            Some(v) => value_word(&v).ok(),
            None => Some(ABSENT),
        },
        Loc::Member(i, e) => member_of(&vals[*i as usize], e).map(|b| b as u64 + 2),
    }
}
#[inline]
pub fn same(a: &Value, b: &Value) -> bool {
    match crate::hashcons::ident(a, b) {
        Some(eq) => eq,
        None => matches!(val_eq(a, b), Ok(true)),
    }
}
/// The entry with every value it holds replaced by the canonical equal value (`hashcons`), so that a
/// later lookup compares them to the state's (canonical) values by identity.
pub fn canon_entry(e: Entry) -> Entry {
    use crate::hashcons::canon_or_keep as c;
    let loc = |l: Loc| match l {
        Loc::Whole(i) => Loc::Whole(i),
        Loc::Elem(i, k) => Loc::Elem(i, c(k)),
        Loc::Member(i, k) => Loc::Member(i, c(k)),
    };
    let op = |o: DOp| match o {
        DOp::Bag { e, plus } => DOp::Bag { e: c(e), plus },
        DOp::Set { e, add } => DOp::Set { e: c(e), add },
        DOp::Exc { path, v } => DOp::Exc { path: path.into_iter().map(c).collect(), v: c(v) },
    };
    match e {
        Entry::Tmpl(t) => Entry::Tmpl(Tmpl { unit: t.unit, bound: t.bound.into_iter().map(c).collect(), locs: t.locs.into_iter().map(loc).collect() }),
        Entry::Leaf(l) => Entry::Leaf(Leaf {
            unit: l.unit,
            bound: l.bound.into_iter().map(c).collect(),
            reads: l.reads.into_iter().map(|(l, v)| (loc(l), c(v))).collect(),
            succs: l
                .succs
                .into_iter()
                .map(|s| {
                    s.into_iter()
                        .map(|w| match w {
                            Write::Val(v) => Write::Val(c(v)),
                            Write::Delta(ops) => Write::Delta(ops.into_iter().map(op).collect()),
                        })
                        .collect()
                })
                .collect(),
        }),
    }
}
/// Does the state have, at `loc`, the value an entry recorded?
pub fn holds(vals: &[Value], loc: &Loc, v: &Value) -> bool {
    match loc {
        Loc::Whole(i) => same(&vals[*i as usize], v),
        Loc::Elem(i, k) => matches!(elem_at(&vals[*i as usize], k), Some(x) if same(&x, v)),
        Loc::Member(i, e) => matches!((member_of(&vals[*i as usize], e), v), (Some(b), Value::Bool(w)) if b == *w),
    }
}
pub fn same_loc(a: &Loc, b: &Loc) -> bool {
    match (a, b) {
        (Loc::Whole(i), Loc::Whole(j)) => i == j,
        (Loc::Elem(i, x), Loc::Elem(j, y)) | (Loc::Member(i, x), Loc::Member(j, y)) => i == j && same(x, y),
        _ => false,
    }
}
pub fn loc_word(l: &Loc) -> R<u64> {
    Ok(match l {
        Loc::Whole(i) => *i as u64 + 1,
        Loc::Elem(i, k) => mix((*i as u64 + 1) << 20, value_word(k)?),
        Loc::Member(i, k) => mix((*i as u64 + 1) << 40, value_word(k)?),
    })
}
