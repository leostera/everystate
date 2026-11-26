//! Parallel breadth-first search (`-workers N`).
//!
//! Values, the syntax tree and the evaluator are single-threaded (`Rc`, `Cell`), so the workers share
//! nothing but bytes: every worker thread builds its own copy of the model, and states cross threads
//! in a serialized form (string and model-value ids are process-wide, see `intern`).
//!
//! The search stays level-synchronised and its result is the one of the sequential search, state for
//! state. One level at a time:
//!
//! 1. The workers take chunks of the level in increasing order. For every state they compute the
//!    successors, constraints and fingerprints exactly as the sequential loop does, look the
//!    fingerprints up in the fingerprint set (frozen while the workers run), and evaluate the
//!    invariants of every successor that may be new. They report, per state and in successor order,
//!    the candidates for new states.
//! 2. The main thread merges the reports in state order: the first occurrence of a fingerprint gets the
//!    next state id, as in the sequential search, so ids, parents, counts, depth and the state graph
//!    are identical to a one-worker run.
//!
//! Whatever is not this plain path is not handled here at all. When a worker meets a violation, an
//! error, a deadlock, or an operator whose effect depends on the order of exploration (Print, TLCSet,
//! TLCGet of a register or a statistic, RandomElement, I/O, a string that does not exist yet ...), it
//! reports the position of that state and stops; the workers never print, write or decide anything.
//! The level is merged up to that state and the sequential loop of `Checker::search` takes over from
//! exactly there: it re-expands the state and reports what it finds, with its own code. After an
//! order-dependent operator it finishes the level, so that every such effect happens in the sequential
//! order, and the next level goes to (fresh) workers again; the third time the search stays sequential
//! and says so.
//!
//! The candidates for initial states are dealt with in the same way (`Par::init`).
//!
//! States found by a parallel level exist as bytes only; `Checker::state_at` rebuilds one for a trace,
//! and `finish` rebuilds all of them when the state graph is going to be read (`-dump`, liveness).
//!
//! Test hooks (environment): EVERYSTATE_PAR_MIN, EVERYSTATE_PAR_CHUNK (see `cli::par_config`) and
//! EVERYSTATE_PAR_DEBUG (a summary of what the workers did, on standard error).
use crate::checker::{Checker, Events, FpSet, ParConfig, NO_PARENT};
use crate::eval::{set_stack_limit, StateData, StateRef};
use crate::host::Host;
use crate::intern::*;
use crate::model::{build_model, Model};
use crate::value::*;
use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher as StdHasher};
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::Arc;

// ---------- serialized values ----------
const T_FALSE: u8 = 0;
const T_TRUE: u8 = 1;
const T_INT: u8 = 2;
const T_STR: u8 = 3;
const T_MODEL: u8 = 4;
const T_TUPLE: u8 = 5;
const T_RECORD: u8 = 6;
const T_FCN: u8 = 7;
const T_ENUM: u8 = 8;
const T_INTERVAL: u8 = 9;
const T_SUBSET: u8 = 10;
const T_FCNSET: u8 = 11;
const T_RECSET: u8 = 12;
const T_CROSS: u8 = 13;
const T_SEQ: u8 = 14;
const T_INF: u8 = 15;
const T_ANY: u8 = 16;
const T_KSUBSET: u8 = 17;
const T_CUP: u8 = 18;
const T_CAP: u8 = 19;
const T_DIFF: u8 = 20;
const T_UNION: u8 = 21;

#[inline]
fn put_u(out: &mut Vec<u8>, mut x: u64) {
    while x >= 0x80 {
        out.push((x as u8) | 0x80);
        x >>= 7;
    }
    out.push(x as u8);
}
#[inline]
fn put_i(out: &mut Vec<u8>, x: i64) {
    put_u(out, ((x << 1) ^ (x >> 63)) as u64);
}
#[inline]
fn get_u(b: &[u8], pos: &mut usize) -> u64 {
    let mut x = 0u64;
    let mut shift = 0;
    loop {
        let c = b[*pos];
        *pos += 1;
        x |= ((c & 0x7f) as u64) << shift;
        if c < 0x80 {
            return x;
        }
        shift += 7;
    }
}
#[inline]
fn get_i(b: &[u8], pos: &mut usize) -> i64 {
    let u = get_u(b, pos);
    ((u >> 1) as i64) ^ -((u & 1) as i64)
}

/// Appends `v`; false when the value has no serialized form (an operator, a lazy function, a set
/// defined by a predicate), in which case `out` is left with a partial encoding.
fn ser_value(v: &Value, out: &mut Vec<u8>) -> bool {
    match v {
        Value::Bool(b) => out.push(if *b { T_TRUE } else { T_FALSE }),
        Value::Int(i) => {
            out.push(T_INT);
            put_i(out, *i);
        }
        Value::Str(s) => {
            out.push(T_STR);
            put_u(out, s.0 as u64);
        }
        Value::Model(s) => {
            out.push(T_MODEL);
            put_u(out, s.0 as u64);
        }
        Value::Tuple(t) => {
            out.push(T_TUPLE);
            put_u(out, t.len() as u64);
            for x in t.iter() {
                if !ser_value(x, out) {
                    return false;
                }
            }
        }
        Value::Record(r) => {
            out.push(T_RECORD);
            put_u(out, r.names.len() as u64);
            for n in r.names.iter() {
                put_u(out, n.0 as u64);
            }
            for x in &r.vals {
                if !ser_value(x, out) {
                    return false;
                }
            }
        }
        Value::Fcn(f) => {
            out.push(T_FCN);
            put_u(out, f.dom.len() as u64);
            // the domain is length-prefixed: the reader shares equal domains without decoding them again
            let mark = out.len();
            for x in f.dom.iter() {
                if !ser_value(x, out) {
                    return false;
                }
            }
            let len = out.len() - mark;
            let mut tmp = Vec::with_capacity(5);
            put_u(&mut tmp, len as u64);
            out.splice(mark..mark, tmp);
            for x in &f.vals {
                if !ser_value(x, out) {
                    return false;
                }
            }
        }
        Value::Set(s) => return ser_set(s, out),
        Value::Undef | Value::Closure(_) | Value::DefRef(_) | Value::LazyFcn(_) | Value::Thunk(_) => return false,
    }
    true
}
fn ser_set(s: &SetV, out: &mut Vec<u8>) -> bool {
    let all = |ss: &[Rc<SetV>], out: &mut Vec<u8>| ss.iter().all(|x| ser_set(x, out));
    match &s.k {
        SetK::Enum(e) => {
            out.push(T_ENUM);
            put_u(out, e.len() as u64);
            e.iter().all(|x| ser_value(x, out))
        }
        SetK::Interval(lo, hi) => {
            out.push(T_INTERVAL);
            put_i(out, *lo);
            put_i(out, *hi);
            true
        }
        SetK::Subset(b) => {
            out.push(T_SUBSET);
            ser_set(b, out)
        }
        SetK::FcnSet(d, r) => {
            out.push(T_FCNSET);
            ser_set(d, out) && ser_set(r, out)
        }
        SetK::RecSet(names, sets) => {
            out.push(T_RECSET);
            put_u(out, names.len() as u64);
            for n in names.iter() {
                put_u(out, n.0 as u64);
            }
            all(sets, out)
        }
        SetK::Cross(sets) => {
            out.push(T_CROSS);
            put_u(out, sets.len() as u64);
            all(sets, out)
        }
        SetK::Seq(b) => {
            out.push(T_SEQ);
            ser_set(b, out)
        }
        SetK::Inf(k) => {
            out.push(T_INF);
            out.push(*k as u8);
            true
        }
        SetK::Any => {
            out.push(T_ANY);
            true
        }
        SetK::KSubset(k, b) => {
            out.push(T_KSUBSET);
            put_i(out, *k);
            ser_set(b, out)
        }
        SetK::Cup(a, b) => {
            out.push(T_CUP);
            ser_set(a, out) && ser_set(b, out)
        }
        SetK::Cap(a, b) => {
            out.push(T_CAP);
            ser_set(a, out) && ser_set(b, out)
        }
        SetK::Diff(a, b) => {
            out.push(T_DIFF);
            ser_set(a, out) && ser_set(b, out)
        }
        SetK::Union(ss) => {
            out.push(T_UNION);
            put_u(out, ss.len() as u64);
            all(ss, out)
        }
        SetK::Filter(_) => false,
    }
}
/// Appends one variable: the length of its encoding, then the encoding.
fn ser_var(v: &Value, out: &mut Vec<u8>, tmp: &mut Vec<u8>) -> bool {
    match v {
        // scalars: one length byte, written in place
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Model(_) => {
            let mark = out.len();
            out.push(0);
            ser_value(v, out);
            out[mark] = (out.len() - mark - 1) as u8;
            true
        }
        _ => {
            tmp.clear();
            if !ser_value(v, tmp) {
                return false;
            }
            put_u(out, tmp.len() as u64);
            out.extend_from_slice(tmp);
            true
        }
    }
}
/// Appends the variables of a state; false when one of them cannot be serialized.
fn ser_state(s: &StateRef, nvars: usize, out: &mut Vec<u8>) -> bool {
    let mut tmp = Vec::new();
    s.with(|vals| vals[..nvars].iter().all(|v| ser_var(v, out, &mut tmp)))
}
/// The same value by identity: the variable was not touched between a state and its successor.
#[inline]
fn same_rc(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Tuple(x), Value::Tuple(y)) => Rc::ptr_eq(x, y),
        (Value::Record(x), Value::Record(y)) => Rc::ptr_eq(x, y),
        (Value::Fcn(x), Value::Fcn(y)) => Rc::ptr_eq(x, y),
        (Value::Set(x), Value::Set(y)) => Rc::ptr_eq(x, y),
        _ => false,
    }
}
/// `ser_state` for a successor `t` of the state `s` whose encoding is `sb` (variable `i` at `spans[i]`):
/// the variables that `t` shares with `s` are copied instead of encoded again.
fn ser_successor(t: &StateRef, s: &StateRef, sb: &[u8], spans: &[(usize, usize)], out: &mut Vec<u8>, tmp: &mut Vec<u8>) -> bool {
    t.with(|tv| ser_row(tv, s, sb, spans, out, tmp))
}
/// `ser_successor` for a successor given as a row of variables.
fn ser_row(tv: &[Value], s: &StateRef, sb: &[u8], spans: &[(usize, usize)], out: &mut Vec<u8>, tmp: &mut Vec<u8>) -> bool {
    {
        s.with(|sv| {
            for i in 0..spans.len() {
                if same_rc(&tv[i], &sv[i]) {
                    out.extend_from_slice(&sb[spans[i].0..spans[i].1]);
                } else if !ser_var(&tv[i], out, tmp) {
                    return false;
                }
            }
            true
        })
    }
}
/// Where the variables are in the encoding of a state (each span includes the length prefix).
fn var_spans(b: &[u8], nvars: usize, spans: &mut Vec<(usize, usize)>) {
    spans.clear();
    let mut pos = 0;
    for _ in 0..nvars {
        let start = pos;
        let len = get_u(b, &mut pos) as usize;
        pos += len;
        spans.push((start, pos));
    }
}

#[derive(Default, Clone, Copy)]
struct Fx(u64);
impl StdHasher for Fx {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for c in bytes.chunks(8) {
            let mut w = [0u8; 8];
            w[..c.len()].copy_from_slice(c);
            self.write_u64(u64::from_le_bytes(w));
        }
    }
    #[inline]
    fn write_u64(&mut self, x: u64) {
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
    #[inline]
    fn write_u32(&mut self, x: u32) {
        self.write_u64(x as u64);
    }
    #[inline]
    fn write_usize(&mut self, x: usize) {
        self.write_u64(x as u64);
    }
    /// (mixed: the table takes its low bits, which a product alone leaves the same for keys that differ
    /// only in their high bytes, as the encodings of numbers do)
    #[inline]
    fn finish(&self) -> u64 {
        let mut x = self.0;
        x ^= x >> 33;
        x = x.wrapping_mul(0xff51_afd7_ed55_8ccd);
        x ^ (x >> 29)
    }
}
type FxBuild = BuildHasherDefault<Fx>;

/// Rebuilds values. Record field lists and function domains are shared between the values of one
/// thread, as they are between the values the evaluator itself builds.
#[derive(Default)]
pub struct De {
    names: HashMap<Box<[StrId]>, Rc<Vec<StrId>>, FxBuild>,
    doms: HashMap<Box<[u8]>, Rc<Vec<Value>>, FxBuild>,
    scratch: Vec<StrId>,
}
impl De {
    fn names(&mut self, b: &[u8], pos: &mut usize, n: usize) -> Rc<Vec<StrId>> {
        self.scratch.clear();
        for _ in 0..n {
            self.scratch.push(StrId(get_u(b, pos) as u32));
        }
        if let Some(r) = self.names.get(&self.scratch[..]) {
            return r.clone();
        }
        let r = Rc::new(self.scratch.clone());
        self.names.insert(self.scratch.clone().into_boxed_slice(), r.clone());
        r
    }
    fn values(&mut self, b: &[u8], pos: &mut usize, n: usize) -> Vec<Value> {
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            out.push(self.value(b, pos));
        }
        out
    }
    fn sets(&mut self, b: &[u8], pos: &mut usize, n: usize) -> Vec<Rc<SetV>> {
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            out.push(self.set(b, pos));
        }
        out
    }
    fn value(&mut self, b: &[u8], pos: &mut usize) -> Value {
        let tag = b[*pos];
        *pos += 1;
        match tag {
            T_FALSE => Value::Bool(false),
            T_TRUE => Value::Bool(true),
            T_INT => Value::Int(get_i(b, pos)),
            T_STR => Value::Str(StrId(get_u(b, pos) as u32)),
            T_MODEL => Value::Model(StrId(get_u(b, pos) as u32)),
            T_TUPLE => {
                let n = get_u(b, pos) as usize;
                if n == 0 {
                    return empty_tuple();
                }
                Value::Tuple(TupleV::rc(self.values(b, pos, n)))
            }
            T_RECORD => {
                let n = get_u(b, pos) as usize;
                let names = self.names(b, pos, n);
                Value::Record(Rc::new(RecordV::new(names, self.values(b, pos, n))))
            }
            T_FCN => {
                let n = get_u(b, pos) as usize;
                let len = get_u(b, pos) as usize;
                let key = &b[*pos..*pos + len];
                let dom = match self.doms.get(key) {
                    Some(d) => {
                        *pos += len;
                        d.clone()
                    }
                    None => {
                        let key: Box<[u8]> = key.into();
                        let d = Rc::new(self.values(b, pos, n));
                        if self.doms.len() >= 1 << 16 {
                            self.doms.clear();
                        }
                        self.doms.insert(key, d.clone());
                        d
                    }
                };
                Value::Fcn(Rc::new(FcnV::new(dom, self.values(b, pos, n))))
            }
            _ => {
                *pos -= 1;
                Value::Set(self.set(b, pos))
            }
        }
    }
    fn set(&mut self, b: &[u8], pos: &mut usize) -> Rc<SetV> {
        let tag = b[*pos];
        *pos += 1;
        let k = match tag {
            T_ENUM => {
                let n = get_u(b, pos) as usize;
                SetK::Enum(self.values(b, pos, n))
            }
            T_INTERVAL => {
                let lo = get_i(b, pos);
                SetK::Interval(lo, get_i(b, pos))
            }
            T_SUBSET => SetK::Subset(self.set(b, pos)),
            T_FCNSET => {
                let d = self.set(b, pos);
                SetK::FcnSet(d, self.set(b, pos))
            }
            T_RECSET => {
                let n = get_u(b, pos) as usize;
                let names = self.names(b, pos, n);
                SetK::RecSet(names, self.sets(b, pos, n))
            }
            T_CROSS => {
                let n = get_u(b, pos) as usize;
                SetK::Cross(self.sets(b, pos, n))
            }
            T_SEQ => SetK::Seq(self.set(b, pos)),
            T_INF => {
                let k = b[*pos];
                *pos += 1;
                SetK::Inf(match k {
                    0 => Inf::Nat,
                    1 => Inf::Int,
                    2 => Inf::Real,
                    _ => Inf::String,
                })
            }
            T_ANY => SetK::Any,
            T_KSUBSET => {
                let k = get_i(b, pos);
                SetK::KSubset(k, self.set(b, pos))
            }
            T_CUP | T_CAP | T_DIFF => {
                let x = self.set(b, pos);
                let y = self.set(b, pos);
                match tag {
                    T_CUP => SetK::Cup(x, y),
                    T_CAP => SetK::Cap(x, y),
                    _ => SetK::Diff(x, y),
                }
            }
            T_UNION => {
                let n = get_u(b, pos) as usize;
                SetK::Union(self.sets(b, pos, n))
            }
            t => panic!("corrupt serialized state (tag {})", t),
        };
        Rc::new(SetV::new(k))
    }
    pub fn state(&mut self, b: &[u8], nvars: usize) -> StateRef {
        let mut pos = 0;
        let mut vals = Vec::with_capacity(nvars);
        for _ in 0..nvars {
            // (a cache of whole variables keyed by their encoding was tried here: slower than decoding)
            let _len = get_u(b, &mut pos);
            vals.push(self.value(b, &mut pos));
        }
        debug_assert_eq!(pos, b.len());
        StateData::new(vals)
    }
}

/// Consecutive states in serialized form: state `base + i` is `bytes[offs[i]..offs[i + 1]]`; or, in
/// numbered form (`nums`), the numbers of its variables' values (`Dict`), `nv` per state.
pub struct Batch {
    base: usize,
    offs: Vec<usize>,
    bytes: Vec<u8>,
    nums: Option<(usize, Vec<u32>)>,
}
impl Batch {
    fn new(base: usize) -> Batch {
        Batch { base, offs: vec![0], bytes: Vec::new(), nums: None }
    }
    fn numbered(base: usize, nv: usize) -> Batch {
        Batch { base, offs: vec![], bytes: Vec::new(), nums: Some((nv, Vec::new())) }
    }
    fn len(&self) -> usize {
        match &self.nums {
            Some((nv, r)) => r.len() / (*nv).max(1),
            None => self.offs.len() - 1,
        }
    }
    fn get(&self, i: usize) -> &[u8] {
        &self.bytes[self.offs[i]..self.offs[i + 1]]
    }
    /// The numbers of state `base + i` (numbered form).
    fn nums(&self, i: usize) -> Option<&[u32]> {
        self.nums.as_ref().map(|(nv, r)| &r[i * nv..(i + 1) * nv])
    }
}

/// Numbers for the values of variables, shared by the threads of a parallel search (id mode): a value
/// gets one the first time a thread sends it, and is kept as its encoding (`ser_var`). A state then
/// crosses threads as one number per variable, and a worker that has met a number knows its value by
/// it (`Nums`). Booleans and small integers are their own numbers (the immediate ids of `hashcons`).
pub struct Dict {
    shards: Box<[std::sync::Mutex<DictShard>]>,
}
#[derive(Default)]
struct DictShard {
    by_bytes: HashMap<Arc<[u8]>, u32, FxBuild>,
    bytes: Vec<Arc<[u8]>>,
}
const DICT_SHARDS: u32 = 64;
impl Dict {
    fn new() -> Dict {
        Dict { shards: (0..DICT_SHARDS).map(|_| Default::default()).collect() }
    }
    /// The number of the value encoded as `b` (`ser_var`).
    fn number(&self, b: &[u8]) -> u32 {
        let mut h = Fx(0);
        h.write(b);
        let k = (h.finish() >> 40) as u32 % DICT_SHARDS;
        let mut sh = self.shards[k as usize].lock().unwrap();
        if let Some(&x) = sh.by_bytes.get(b) {
            return x;
        }
        let i = sh.bytes.len() as u32;
        assert!(i < 1 << 24, "parallel search: more than 2^30 distinct values of variables");
        let x = i * DICT_SHARDS + k;
        let a: Arc<[u8]> = b.into();
        sh.bytes.push(a.clone());
        sh.by_bytes.insert(a, x);
        x
    }
    /// The encoding of the value numbered `x`.
    fn bytes(&self, x: u32) -> Arc<[u8]> {
        self.shards[(x % DICT_SHARDS) as usize].lock().unwrap().bytes[(x / DICT_SHARDS) as usize].clone()
    }
    /// Appends the encoding of the value numbered `x` (`ser_var`).
    fn encode(&self, x: u32, out: &mut Vec<u8>) {
        if crate::hashcons::is_immediate(x) {
            ser_var(&crate::hashcons::value(x), out, &mut vec![]);
        } else {
            out.extend_from_slice(&self.bytes(x));
        }
    }
    /// The value numbered `x`.
    fn value(&self, de: &mut De, x: u32) -> Value {
        if crate::hashcons::is_immediate(x) {
            return crate::hashcons::value(x);
        }
        let b = self.bytes(x);
        let mut pos = 0;
        let _len = get_u(&b, &mut pos);
        de.value(&b, &mut pos)
    }
}
/// The candidates of `out` from `mark` on that were written as encodings (`ser_state`), as numbers.
fn number_encodings(dict: &Dict, out: &mut ChunkOut, mark: (usize, usize, usize), nv: usize) {
    if out.bytes.len() == mark.1 {
        return;
    }
    let mut off = mark.1;
    for e in &out.ent[mark.0..] {
        if e.kind != CAND || e.len == 0 {
            continue;
        }
        let b = &out.bytes[off..off + e.len as usize];
        let mut pos = 0;
        for _ in 0..nv {
            let start = pos;
            let len = get_u(b, &mut pos) as usize;
            pos += len;
            out.nums.push(dict.number(&b[start..pos]));
        }
        off += e.len as usize;
    }
    out.bytes.truncate(mark.1);
}
/// A thread's side of `Dict`: the ids of the values it has met by number and back.
#[derive(Default)]
struct Nums {
    /// per shard, by index: the id + 1 (0: not met)
    ids: Vec<Vec<u32>>,
    /// by id: the number + 1 (0: not met)
    nums: Vec<u32>,
}
impl Nums {
    fn note(&mut self, x: u32, id: crate::hashcons::Id) {
        let (k, i) = ((x % DICT_SHARDS) as usize, (x / DICT_SHARDS) as usize);
        if self.ids.len() <= k {
            self.ids.resize(DICT_SHARDS as usize, vec![]);
        }
        if self.ids[k].len() <= i {
            self.ids[k].resize(i + 1, 0);
        }
        self.ids[k][i] = id + 1;
        let j = id as usize;
        if self.nums.len() <= j {
            self.nums.resize(j + 1, 0);
        }
        self.nums[j] = x + 1;
    }
    /// The id of the value numbered `x` on this thread (interning it); None when it cannot be interned.
    #[inline]
    fn id(&mut self, dict: &Dict, de: &mut De, x: u32) -> Option<crate::hashcons::Id> {
        if crate::hashcons::is_immediate(x) {
            return Some(x);
        }
        let (k, i) = ((x % DICT_SHARDS) as usize, (x / DICT_SHARDS) as usize);
        if let Some(&y) = self.ids.get(k).and_then(|v| v.get(i)) {
            if y != 0 {
                return Some(y - 1);
            }
        }
        let id = crate::hashcons::id(&dict.value(de, x))?;
        self.note(x, id);
        Some(id)
    }
    /// The number of the value with id `id` on this thread; None when it cannot be encoded.
    #[inline]
    fn num(&mut self, dict: &Dict, id: crate::hashcons::Id, tmp: &mut Vec<u8>, out: &mut Vec<u8>) -> Option<u32> {
        if crate::hashcons::is_immediate(id) {
            return Some(id);
        }
        if let Some(&y) = self.nums.get(id as usize) {
            if y != 0 {
                return Some(y - 1);
            }
        }
        out.clear();
        if !ser_var(&crate::hashcons::value(id), out, tmp) {
            return None;
        }
        let x = dict.number(out);
        self.note(x, id);
        Some(x)
    }
}

// ---------- the workers ----------
const CAND: u8 = 0; // not in the fingerprint set, first occurrence in this worker: carries the state
const DUP: u8 = 1; // seen earlier in this level by the same worker
const SEEN: u8 = 2; // in the fingerprint set (a state of an earlier level): `fp` holds its id

/// One successor that the merge has to know about.
struct Ent {
    fp: u64,
    act: u32,
    kind: u8,
    /// length of its serialized state in `ChunkOut::bytes` (0 = not sent)
    len: u32,
}
enum Event {
    /// a violation, an error or a deadlock: the sequential search reports it
    Check,
    /// the state cannot be expanded by a worker; the reason
    Fallback(String),
}
/// What a worker reports for the states `start .. start + done` of a level.
struct ChunkOut {
    start: usize,
    done: usize,
    /// what stopped the worker at state `start + done`
    event: Option<Event>,
    /// per state: generated successors, number of entries in `ent`
    src: Vec<(u64, u32)>,
    ent: Vec<Ent>,
    bytes: Vec<u8>,
    /// id mode: the candidates by group of the fingerprint set (see `Claim`), (fingerprint, entry), in
    /// order
    by_group: Vec<Vec<(u64, u32)>>,
    /// id mode: the candidates as numbers (`Dict`), `nv` per entry, instead of `bytes`
    nums: Vec<u32>,
}
/// Who found each fingerprint first in a level, as far as the workers can tell while they expand it
/// (id mode, `Par::level_ids`): fingerprint -> the smallest position (state of the level, successor)
/// it was found at so far. A worker that finds a fingerprint at a later position than one already
/// noted drops it: that is not the occurrence the sequential search meets first. (Only a shortcut: the
/// claim after the level decides; a fingerprint that finds no room here is a candidate.)
struct Firsts {
    keys: Box<[std::sync::atomic::AtomicU64]>,
    /// the complement of the earliest position (0: none yet; zeroed memory is a table with nothing in it)
    at: Box<[std::sync::atomic::AtomicU64]>,
    mask: usize,
}
/// How far `Firsts::first` looks for a fingerprint's slot (a table that full makes candidates).
const FIRSTS_PROBES: usize = 32;
impl Firsts {
    fn new(cap: usize) -> Firsts {
        Firsts { keys: crate::checker::zeroed_u64(cap), at: crate::checker::zeroed_u64(cap), mask: cap - 1 }
    }
    /// Notes that `fp` was found at `at`; false when it was found at an earlier position already.
    #[inline]
    fn first(&self, fp: u64, at: u64) -> bool {
        let k = if fp == 0 { 0x9E37_79B9_7F4A_7C15 } else { fp };
        let mut i = (k as usize) & self.mask;
        for _ in 0..FIRSTS_PROBES {
            let mut cur = self.keys[i].load(Ordering::Acquire);
            if cur == 0 {
                cur = match self.keys[i].compare_exchange(0, k, Ordering::AcqRel, Ordering::Acquire) {
                    Ok(_) => k,
                    Err(x) => x,
                };
            }
            if cur == k {
                return !at > self.at[i].fetch_max(!at, Ordering::AcqRel);
            }
            i = (i + 1) & self.mask;
        }
        true
    }
}

struct Job {
    /// the states are the candidates for initial states, not a level
    init: bool,
    /// id mode: who found each fingerprint first (see `Firsts`)
    firsts: Option<Firsts>,
    /// id mode: the numbers of values (states cross threads as numbers)
    dict: Option<Arc<Dict>>,
    /// what the sequential search measured of the step cache (see `Plans::adopt`)
    verdicts: Arc<[crate::compile::Verdict]>,
    frontier: Arc<Batch>,
    lvl: u32,
    chunk: usize,
    next: AtomicUsize,
    /// smallest position at which a worker stopped; states behind it are not expanded
    stop: AtomicUsize,
    fps: Arc<FpSet>,
}
enum ToWorker {
    Level(Arc<Job>),
    Claim(Arc<Claim>),
    Grow(Arc<Grow>),
    Exit,
}
/// The second half of a level in id mode (`Par::level_ids`): the candidates of every chunk go into the
/// fingerprint set, each worker taking the fingerprints of its groups of segments, in the order of the
/// level. The first of the level to insert a fingerprint is the one the sequential search finds first:
/// it is a new state (see `wins`); the others are not.
struct Claim {
    chunks: Vec<ChunkOut>,
    /// per chunk: how many of its entries count (the level ends at the first state a worker stopped at)
    upto: Vec<usize>,
    fps: Arc<FpSet>,
    next: AtomicUsize,
    /// per group: its new states (chunk, entry), stored once the group is done
    wins: Vec<std::sync::Mutex<Vec<(u32, u32)>>>,
}
/// The groups of segments of the fingerprint set that the workers claim fingerprints in: a fingerprint
/// belongs to group `FpSet::segment(fp) % CLAIM_GROUPS`. (More than workers: one slow worker delays the
/// end of the claim less.)
const CLAIM_GROUPS: usize = 16;
impl Claim {
    fn run(&self) {
        loop {
            let g = self.next.fetch_add(1, Ordering::Relaxed);
            if g >= CLAIM_GROUPS {
                return;
            }
            // (results are kept by the group and handed on once: threads writing one shared bitmap, or
            // one shared count, took longer than the inserts)
            let mut wins = vec![];
            for (ci, c) in self.chunks.iter().enumerate() {
                for &(fp, ei) in c.by_group[g].iter() {
                    if ei as usize >= self.upto[ci] {
                        break;
                    }
                    // (`Par::level_ids` made room for every candidate)
                    if self.fps.insert_owned(fp) {
                        wins.push((ci as u32, ei));
                    }
                }
            }
            self.fps.add_len(wins.len());
            *self.wins[g].lock().unwrap() = wins;
        }
    }
}
/// The fingerprint set moved to a larger one by the workers, a segment at a time (a fingerprint stays
/// in its segment whatever the size: see `FpSet`).
struct Grow {
    old: FpSet,
    new: FpSet,
    next: AtomicUsize,
}
impl Grow {
    fn run(&self) {
        loop {
            let s = self.next.fetch_add(1, Ordering::Relaxed);
            if s >= crate::checker::SEGMENTS {
                return;
            }
            self.new.refill_segment(&self.old, s);
        }
    }
}
enum FromWorker {
    Ready(Result<(), String>),
    Chunk(ChunkOut),
    Done,
    /// a claim or a grow is done (on this worker's side)
    Finished,
}
#[derive(Clone, Copy)]
struct Flags {
    check_deadlock: bool,
    /// the merge needs every edge of the state graph (`-dump`, liveness)
    record: bool,
    /// ... and the successor states themselves (liveness under VIEW or SYMMETRY)
    keep_states: bool,
}

/// The host of a worker's evaluator: nothing may be read from or written to the outside by a worker.
struct GuardHost;
const IO: &str = "an operator that prints or does input/output";
impl Host for GuardHost {
    fn read_file(&self, path: &str) -> Result<Vec<u8>, String> {
        worker_impure(IO);
        Err(path.to_string())
    }
    fn write_file(&self, path: &str, _: &[u8]) -> Result<(), String> {
        worker_impure(IO);
        Err(path.to_string())
    }
    fn append_file(&self, path: &str, _: &[u8]) -> Result<(), String> {
        worker_impure(IO);
        Err(path.to_string())
    }
    fn exists(&self, _: &str) -> bool {
        worker_impure(IO);
        false
    }
    fn env(&self) -> Vec<(String, String)> {
        worker_impure(IO);
        vec![]
    }
    fn exec(&self, _: &[String], _: Option<&[(String, String)]>) -> Result<(i32, String, String), String> {
        worker_impure(IO);
        Err("not available".into())
    }
    fn print(&self, _: &str) {
        worker_impure(IO);
    }
    fn now_ms(&self) -> f64 {
        worker_impure("the clock");
        0.0
    }
}

/// The recipe by which a worker thread builds its own copy of the model: the configuration text and
/// the module sources the main thread read.
pub fn model_factory(root_name: String, cfg_text: String, sources: Vec<(String, String)>) -> Arc<dyn Fn() -> R<Model> + Send + Sync> {
    let sources = Arc::new(sources);
    Arc::new(move || {
        let cfg = crate::cfg::parse_config(&cfg_text)?;
        let src = sources.clone();
        let resolve: crate::modules::SourceResolver = Box::new(move |name: &str| src.iter().find(|(n, _)| n == name).map(|(_, t)| t.clone()));
        build_model(&root_name, resolve, &cfg, Rc::new(GuardHost))
    })
}

/// A level this large goes to the workers however long the search has run.
const BIG_LEVEL: usize = 512;
const STACK: usize = 1 << 30;
const UNSENDABLE: &str = "a state holds a value that cannot be passed between workers (a set defined by a predicate, or an operator)";

/// macOS: a thread of the default quality of service may run on an efficiency core, which takes about
/// twice as long; the level waits for its slowest worker.
#[cfg(target_os = "macos")]
fn prefer_fast_cores() {
    extern "C" {
        fn pthread_set_qos_class_self_np(class: u32, relative_priority: i32) -> i32;
    }
    const QOS_CLASS_USER_INTERACTIVE: u32 = 0x21;
    // SAFETY: sets an attribute of the calling thread only
    unsafe {
        pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0);
    }
}
#[cfg(not(target_os = "macos"))]
fn prefer_fast_cores() {}

fn worker_main(factory: Arc<dyn Fn() -> R<Model> + Send + Sync>, flags: Flags, rx: Receiver<ToWorker>, tx: Sender<FromWorker>) {
    set_stack_limit(STACK - (64 << 20));
    set_worker(true);
    prefer_fast_cores();
    let model = match factory() {
        Ok(m) => m,
        Err(_) => {
            let _ = tx.send(FromWorker::Ready(Err("a worker could not load the specification".into())));
            return;
        }
    };
    let ck = Checker::new(&model, crate::checker::CheckOptions { check_deadlock: flags.check_deadlock, record_graph: false, par: None });
    if let Some(what) = take_impure() {
        let _ = tx.send(FromWorker::Ready(Err(format!("loading the specification uses {}", what))));
        return;
    }
    if tx.send(FromWorker::Ready(Ok(()))).is_err() {
        return;
    }
    let mut de = De::default();
    let mut succs: Vec<StateRef> = vec![];
    let mut acts: Vec<u32> = vec![];
    let mut scratch = Scratch::default();
    let mut sbuf: Vec<u8> = vec![];
    // EVERYSTATE_PAR_DEBUG: seconds spent on levels, states expanded
    let mut busy = (0.0f64, 0u64);
    let nvars = model.vars.len();
    let idmode = ck.is_flat() && !flags.record && ck.caching();
    loop {
        let job = match rx.recv() {
            Ok(ToWorker::Level(job)) => job,
            Ok(ToWorker::Claim(c)) => {
                c.run();
                drop(c);
                if tx.send(FromWorker::Finished).is_err() {
                    return;
                }
                continue;
            }
            Ok(ToWorker::Grow(g)) => {
                g.run();
                drop(g);
                if tx.send(FromWorker::Finished).is_err() {
                    return;
                }
                continue;
            }
            _ => {
                if let Some(r) = ck.eval_report() {
                    eprint!("worker: {}", r);
                }
                if std::env::var_os("EVERYSTATE_PAR_DEBUG").is_some() {
                    eprintln!("par: worker: {:.1} ms on levels, {} states, {:.0} ns per state", busy.0 * 1e3, busy.1, busy.0 * 1e9 / busy.1.max(1) as f64);
                }
                break;
            }
        };
        ck.adopt(&job.verdicts);
        // fingerprints this worker has met in this level
        let mut local = FpSet::with_capacity(1 << 10);
        let t_job = std::time::Instant::now();
        {
            let fps = &*job.fps;
            let n = job.frontier.len();
            loop {
                let start = job.next.fetch_add(1, Ordering::Relaxed).saturating_mul(job.chunk);
                if start >= n || start > job.stop.load(Ordering::Relaxed) {
                    break;
                }
                let end = (start + job.chunk).min(n);
                let mut out = ChunkOut { start, done: 0, event: None, src: Vec::with_capacity(end - start), ent: vec![], bytes: vec![], by_group: if idmode { vec![vec![]; CLAIM_GROUPS] } else { vec![] }, nums: vec![] };
                for i in start..end {
                    if i > job.stop.load(Ordering::Relaxed) {
                        break;
                    }
                    // a numbered level: the ids by number (the values only if something needs them), or,
                    // with a value that cannot be interned, the encoding
                    let xs = job.frontier.nums(i);
                    let mut lazy = false;
                    if let Some(xs) = xs {
                        let dict = job.dict.as_ref().expect("a numbered level comes with its numbers");
                        scratch.cur.clear();
                        lazy = idmode && !job.init && xs.iter().all(|&x| scratch.nums.id(dict, &mut de, x).map(|id| scratch.cur.push(id)).is_some());
                        if !lazy {
                            scratch.cur.clear();
                            sbuf.clear();
                            for &x in xs {
                                dict.encode(x, &mut sbuf);
                            }
                        }
                    }
                    let sb: &[u8] = if xs.is_some() { &sbuf } else { job.frontier.get(i) };
                    let s = if lazy {
                        scratch.blank_state(nvars)
                    } else if idmode && !job.init {
                        scratch.enc.state(&mut de, sb, nvars, &mut scratch.cur)
                    } else {
                        de.state(sb, nvars)
                    };
                    let mark = (out.ent.len(), out.bytes.len(), out.nums.len());
                    let firsts = job.firsts.as_ref().map(|f| (f, i as u64));
                    let numbers = job.dict.as_deref().map(|d| (d, if lazy { xs } else { None }));
                    let mut event = if job.init { expand_init(&ck, &s, &mut local, &mut out) } else { expand(&ck, &s, sb, job.lvl, fps, &mut local, firsts, numbers, &mut de, &mut out, &mut succs, &mut acts, flags, &mut scratch) };
                    if let (Some(dict), None) = (&job.dict, &event) {
                        // (candidates found as values: their encodings to numbers)
                        number_encodings(dict, &mut out, mark, nvars);
                    }
                    // an order-dependent operator decides, whatever else happened to the evaluation
                    if let Some(what) = take_impure() {
                        event = Some(Event::Fallback(format!("the specification uses {}", what)));
                    }
                    if let Some(e) = event {
                        out.ent.truncate(mark.0);
                        out.bytes.truncate(mark.1);
                        out.nums.truncate(mark.2);
                        for g in out.by_group.iter_mut() {
                            while g.last().is_some_and(|x| x.1 as usize >= mark.0) {
                                g.pop();
                            }
                        }
                        ck.ev.extra_generated.set(0);
                        job.stop.fetch_min(i, Ordering::Relaxed);
                        out.event = Some(e);
                        break;
                    }
                    out.done += 1;
                }
                busy.1 += out.done as u64;
                if tx.send(FromWorker::Chunk(out)).is_err() {
                    return;
                }
            }
        }
        busy.0 += t_job.elapsed().as_secs_f64();
        drop(job);
        if tx.send(FromWorker::Done).is_err() {
            return;
        }
    }
    if let Some(r) = ck.eval_report() {
        eprint!("{}: {}", std::thread::current().name().unwrap_or("worker"), r);
    }
    // the process is about to end or goes on without this thread: nothing here is worth tearing down
    std::mem::forget(ck);
    std::mem::forget(model);
}

/// Expands one state as the sequential loop does (same evaluations in the same order, same TLCGet("level")),
/// without its bookkeeping. Some(..) when the state has to go to the sequential search instead.
#[allow(clippy::too_many_arguments)]
#[allow(clippy::too_many_arguments)]
fn expand(ck: &Checker, s: &StateRef, sb: &[u8], lvl: u32, fps: &FpSet, local: &mut FpSet, firsts: Option<(&Firsts, u64)>, numbers: Option<(&Dict, Option<&[u32]>)>, de: &mut De, out: &mut ChunkOut, succs: &mut Vec<StateRef>, acts: &mut Vec<u32>, flags: Flags, scratch: &mut Scratch) -> Option<Event> {
    let m = ck.model;
    let ev = ck.ev;
    let level = &ev.stats.level;
    level.set(lvl as i64);
    succs.clear();
    acts.clear();
    if ck.is_flat() && !flags.record {
        // As the sequential loop in flat mode: the successors are rows of a buffer, their fingerprints
        // are the parent's with the changed variables replaced, and a state is built (for the
        // invariants) only for a successor that may be new. There are no constraints and no action
        // properties in this mode.
        let nv = ck.model.vars.len();
        if !scratch.cur.is_empty() {
            return expand_ids(ck, s, sb, lvl, fps, local, firsts, numbers, de, out, flags, scratch);
        }
        scratch.rows.clear();
        if ck.successors_flat(s, &mut scratch.rows, acts).is_err() {
            return Some(Event::Check);
        }
        let extra = ev.extra_generated.replace(0);
        let first = out.ent.len();
        var_spans(sb, nv, &mut scratch.spans);
        if !acts.is_empty() && ck.parent_terms(s, &mut scratch.terms).is_err() {
            return Some(Event::Check);
        }
        for i in 0..acts.len() {
            let row = &scratch.rows[i * nv..(i + 1) * nv];
            level.set(lvl as i64 + 1);
            let fp = match ck.row_fingerprint(s, &scratch.terms, row) {
                Ok(fp) => fp,
                Err(_) => return Some(Event::Check),
            };
            let candidate = fps.get(fp).is_none() && local.put(fp, 0).is_none();
            if candidate {
                let mark = out.bytes.len();
                if !ser_row(row, s, sb, &scratch.spans, &mut out.bytes, &mut scratch.tmp) {
                    return Some(Event::Fallback(UNSENDABLE.into()));
                }
                if !out.by_group.is_empty() {
                    out.by_group[FpSet::segment(fp) % CLAIM_GROUPS].push((fp, out.ent.len() as u32));
                }
                out.ent.push(Ent { fp, act: acts[i], kind: CAND, len: (out.bytes.len() - mark) as u32 });
                if !m.invariants.is_empty() {
                    let t = StateData::new(row.to_vec());
                    for ii in 0..m.invariants.len() {
                        if !matches!(ck.eval_invariant(ii, &t), Ok(true)) {
                            return Some(Event::Check);
                        }
                    }
                }
            }
            level.set(lvl as i64);
        }
        if acts.is_empty() && flags.check_deadlock {
            return Some(Event::Check);
        }
        out.src.push((acts.len() as u64 + extra, (out.ent.len() - first) as u32));
        return None;
    }
    if ck.successors(s, succs, acts).is_err() {
        return Some(Event::Check);
    }
    let extra = ev.extra_generated.replace(0);
    let first = out.ent.len();
    var_spans(sb, ck.model.vars.len(), &mut scratch.spans);
    for i in 0..succs.len() {
        let t = &succs[i];
        let act = acts[i];
        let fp: R<Option<u64>> = (|| {
            level.set(lvl as i64 + 1);
            for c in &m.constraints {
                if !ck.eval_pred(c, t, None)? {
                    return Ok(None);
                }
            }
            level.set(lvl as i64);
            for c in &m.action_constraints {
                if !ck.eval_pred(c, s, Some(t))? {
                    level.set(lvl as i64 + 1);
                    return Ok(None);
                }
            }
            level.set(lvl as i64 + 1);
            Ok(Some(ck.fingerprint(t)?))
        })();
        let fp = match fp {
            Ok(fp) => fp,
            Err(_) => return Some(Event::Check),
        };
        let mut unseen = true;
        if let Some(fp) = fp {
            let (kind, word) = match fps.get(fp) {
                Some(id) => (SEEN, id as u64),
                None => match local.put(fp, 0) {
                    Some(_) => (DUP, fp),
                    None => (CAND, fp),
                },
            };
            unseen = kind == CAND;
            if kind == CAND || flags.record {
                let mark = out.bytes.len();
                if (kind == CAND || flags.keep_states) && !ser_successor(t, s, sb, &scratch.spans, &mut out.bytes, &mut scratch.tmp) {
                    return Some(Event::Fallback(UNSENDABLE.into()));
                }
                out.ent.push(Ent { fp: word, act, kind, len: (out.bytes.len() - mark) as u32 });
            }
        }
        if unseen {
            for ii in 0..m.invariants.len() {
                if !matches!(ck.eval_invariant(ii, t), Ok(true)) {
                    return Some(Event::Check);
                }
            }
        }
        level.set(lvl as i64);
        for p in &m.implied_actions {
            if !matches!(ck.eval_pred(p, s, Some(t)), Ok(true)) {
                return Some(Event::Check);
            }
        }
    }
    if succs.is_empty() && flags.check_deadlock {
        return Some(Event::Check);
    }
    out.src.push((succs.len() as u64 + extra, (out.ent.len() - first) as u32));
    None
}

/// `expand` in flat mode with the step cache: as the sequential search in id mode. The parent is interned
/// (and rebuilt from the canonical values, which the step cache compares by identity), its successors are
/// rows of ids, and a candidate is encoded from the parent's encoding and the values of the ids that
/// differ.
#[allow(clippy::too_many_arguments)]
#[allow(clippy::too_many_arguments)]
fn expand_ids(ck: &Checker, s: &StateRef, sb: &[u8], lvl: u32, fps: &FpSet, local: &mut FpSet, firsts: Option<(&Firsts, u64)>, numbers: Option<(&Dict, Option<&[u32]>)>, de: &mut De, out: &mut ChunkOut, flags: Flags, scratch: &mut Scratch) -> Option<Event> {
    use crate::hashcons::NOT_INTERNED;
    let m = ck.model;
    let ev = ck.ev;
    let level = &ev.stats.level;
    let nv = m.vars.len();
    let cur = &mut scratch.cur;
    // (the parent's terms first: a successor found from the step cache gets its fingerprint from them,
    // and its row is built only if it is a candidate)
    let lazy = numbers.is_some_and(|(_, xs)| xs.is_some());
    let terms = if lazy { ck.id_terms(cur, &mut scratch.terms) } else { ck.parent_terms(s, &mut scratch.terms) };
    if terms.is_err() {
        return Some(Event::Check);
    }
    let fpx = scratch.terms.fp_ctx(fps);
    let ids_now: Vec<crate::hashcons::Id> = if lazy { cur.clone() } else { vec![] };
    let fill = || s.refill(|v| v.extend(ids_now.iter().map(|&x| crate::hashcons::value(x))));
    if ck.successors_ids(s, if lazy { Some(&fill) } else { None }, cur, &scratch.idrows, Some(&fpx)).is_err() {
        return Some(Event::Check);
    }
    let extra = ev.extra_generated.replace(0);
    let first = out.ent.len();
    let rows = scratch.idrows.borrow();
    let n = rows.len();
    if n > 0 {
        ck.id_fingerprints(s, cur, &scratch.terms, &rows, &mut scratch.fps);
        if numbers.is_none() {
            var_spans(sb, nv, &mut scratch.spans);
        }
    }
    // the parent's numbers (a bytes level: from its ids)
    if let (Some((dict, pn)), true) = (numbers, n > 0) {
        scratch.pnums.clear();
        match pn {
            Some(xs) => scratch.pnums.extend_from_slice(xs),
            None => {
                for &x in cur.iter() {
                    let y = if x < NOT_INTERNED {
                        scratch.nums.num(dict, x, &mut scratch.tmp, &mut scratch.tmp2)
                    } else {
                        scratch.tmp2.clear();
                        ser_var(&rows.value(x), &mut scratch.tmp2, &mut scratch.tmp).then(|| dict.number(&scratch.tmp2))
                    };
                    match y {
                        Some(y) => scratch.pnums.push(y),
                        None => return Some(Event::Fallback(UNSENDABLE.into())),
                    }
                }
            }
        }
    }
    level.set(lvl as i64 + 1);
    for i in 0..n {
        let fp = match scratch.fps[i] {
            Some(fp) => fp,
            None => return Some(Event::Check),
        };
        if fps.get(fp).is_some() {
            continue;
        }
        let first = match firsts {
            // (position: the state in the level, then the successor; past 2^24 successors, every one is a candidate)
            Some((f, at)) if i < 1 << 24 => f.first(fp, at << 24 | i as u64),
            Some(_) => true,
            None => local.put(fp, 0).is_none(),
        };
        if !first {
            continue;
        }
        let row: &[crate::hashcons::Id] = match rows.row(i, nv) {
            Some(row) => row,
            None => {
                let rc = rows.meta.recipe_of(i).expect("a successor without a row is a recipe");
                if !ck.build_recipe(rc, cur, &mut scratch.recipe_row) {
                    // (its changes do not apply after all: the sequential search finds out why)
                    return Some(Event::Check);
                }
                &scratch.recipe_row
            }
        };
        let mark = out.bytes.len();
        match numbers {
            Some((dict, _)) => {
                for k in 0..nv {
                    let x = row[k];
                    let y = if x == cur[k] {
                        Some(scratch.pnums[k])
                    } else if x < NOT_INTERNED {
                        scratch.nums.num(dict, x, &mut scratch.tmp, &mut scratch.tmp2)
                    } else {
                        scratch.tmp2.clear();
                        ser_var(&rows.value(x), &mut scratch.tmp2, &mut scratch.tmp).then(|| dict.number(&scratch.tmp2))
                    };
                    match y {
                        Some(y) => out.nums.push(y),
                        None => return Some(Event::Fallback(UNSENDABLE.into())),
                    }
                }
            }
            None => {
                for k in 0..nv {
                    let x = row[k];
                    if x == cur[k] {
                        out.bytes.extend_from_slice(&sb[scratch.spans[k].0..scratch.spans[k].1]);
                    } else if x < NOT_INTERNED {
                        if !scratch.enc.encode(x, &mut out.bytes, &mut scratch.tmp) {
                            return Some(Event::Fallback(UNSENDABLE.into()));
                        }
                    } else if !ser_var(&rows.value(x), &mut out.bytes, &mut scratch.tmp) {
                        return Some(Event::Fallback(UNSENDABLE.into()));
                    }
                }
            }
        }
        out.by_group[FpSet::segment(fp) % CLAIM_GROUPS].push((fp, out.ent.len() as u32));
        out.ent.push(Ent { fp, act: rows.meta.found[i].act, kind: CAND, len: (out.bytes.len() - mark) as u32 });
        if !m.invariants.is_empty() {
            let t = StateData::new(row.iter().map(|&x| rows.value(x)).collect());
            for ii in 0..m.invariants.len() {
                if !matches!(ck.eval_invariant(ii, &t), Ok(true)) {
                    return Some(Event::Check);
                }
            }
        }
    }
    let _ = de;
    level.set(lvl as i64);
    if n == 0 && flags.check_deadlock {
        return Some(Event::Check);
    }
    out.src.push((n as u64 + extra, (out.ent.len() - first) as u32));
    None
}

/// The same for a candidate initial state: constraints, fingerprint, invariants and implied initial
/// predicates, as in `Checker::compute_init`.
fn expand_init(ck: &Checker, s: &StateRef, local: &mut FpSet, out: &mut ChunkOut) -> Option<Event> {
    let m = ck.model;
    ck.ev.stats.level.set(1);
    let fp: R<Option<u64>> = (|| {
        for c in &m.constraints {
            if !ck.eval_pred(c, s, None)? {
                return Ok(None);
            }
        }
        Ok(Some(ck.fingerprint(s)?))
    })();
    let fp = match fp {
        Ok(fp) => fp,
        Err(_) => return Some(Event::Check),
    };
    let mut unseen = true;
    if let Some(fp) = fp {
        unseen = local.put(fp, 0).is_none();
        if unseen {
            // the merge takes the state itself from the level
            out.ent.push(Ent { fp, act: 0, kind: CAND, len: 0 });
        }
    }
    if unseen {
        for p in m.invariants.iter().chain(m.implied_inits.iter()) {
            if !matches!(ck.eval_pred(p, s, None), Ok(true)) {
                return Some(Event::Check);
            }
        }
    }
    out.src.push((1, (fp.is_some() && unseen) as u32));
    None
}

/// A worker's memo of the encodings of the values it interned, both ways: decoding a variable it has met
/// is a hash of its bytes, and encoding an id it has met is a copy.
#[derive(Default)]
struct Enc {
    arena: Vec<u8>,
    /// per id: where its variable encoding (length prefix included) is in `arena`; (0, 0) = not known
    by_id: Vec<(u32, u32)>,
    by_bytes: HashMap<Box<[u8]>, crate::hashcons::Id, FxBuild>,
}
impl Enc {
    fn note(&mut self, x: crate::hashcons::Id, bytes: &[u8]) {
        if crate::hashcons::is_immediate(x) {
            return;
        }
        let i = x as usize;
        if self.by_id.len() <= i {
            self.by_id.resize(i + 1, (0, 0));
        }
        if self.by_id[i].1 == 0 && self.arena.len() + bytes.len() < u32::MAX as usize {
            self.by_id[i] = (self.arena.len() as u32, bytes.len() as u32);
            self.arena.extend_from_slice(bytes);
        }
    }
    /// The state encoded in `b`, from canonical values; `cur` gets the ids of its variables
    /// (`NOT_INTERNED` for a value that cannot be interned).
    fn state(&mut self, de: &mut De, b: &[u8], nvars: usize, cur: &mut Vec<crate::hashcons::Id>) -> StateRef {
        use crate::hashcons::NOT_INTERNED;
        cur.clear();
        let mut vals = Vec::with_capacity(nvars);
        let mut pos = 0;
        for _ in 0..nvars {
            let start = pos;
            let len = get_u(b, &mut pos) as usize;
            let mut vpos = pos;
            pos += len;
            let span = &b[start..pos];
            if len <= 9 {
                // a scalar (or a small value): decoding it is cheaper than the memo
                let v = de.value(b, &mut vpos);
                match crate::hashcons::id(&v) {
                    Some(x) => {
                        cur.push(x);
                        vals.push(crate::hashcons::value(x));
                    }
                    None => {
                        cur.push(NOT_INTERNED);
                        vals.push(v);
                    }
                }
                continue;
            }
            if let Some(&x) = self.by_bytes.get(span) {
                cur.push(x);
                vals.push(crate::hashcons::value(x));
                continue;
            }
            let v = de.value(b, &mut vpos);
            match crate::hashcons::id(&v) {
                Some(x) => {
                    self.by_bytes.insert(span.into(), x);
                    self.note(x, span);
                    cur.push(x);
                    vals.push(crate::hashcons::value(x));
                }
                None => {
                    cur.push(NOT_INTERNED);
                    vals.push(v);
                }
            }
        }
        StateData::new(vals)
    }
    /// Appends the variable encoding of the value with id `x`; false when it cannot be encoded.
    fn encode(&mut self, x: crate::hashcons::Id, out: &mut Vec<u8>, tmp: &mut Vec<u8>) -> bool {
        if crate::hashcons::is_immediate(x) {
            return ser_var(&crate::hashcons::value(x), out, tmp);
        }
        if let Some(&(o, l)) = self.by_id.get(x as usize) {
            if l > 0 {
                out.extend_from_slice(&self.arena[o as usize..(o + l) as usize]);
                return true;
            }
        }
        let mark = out.len();
        if !ser_var(&crate::hashcons::value(x), out, tmp) {
            return false;
        }
        let bytes = out[mark..].to_vec();
        self.note(x, &bytes);
        true
    }
}

#[derive(Default)]
struct Scratch {
    enc: Enc,
    spans: Vec<(usize, usize)>,
    tmp: Vec<u8>,
    /// flat mode: the variables of the successors of the state being expanded, and its fingerprint terms
    rows: Vec<Value>,
    terms: crate::checker::ParentTerms,
    /// id mode: the ids of the parent, its successors, their fingerprints
    cur: Vec<crate::hashcons::Id>,
    idrows: RefCell<crate::stepcache::Rows>,
    fps: Vec<Option<u64>>,
    /// the row of a candidate noted as a recipe
    recipe_row: Vec<crate::hashcons::Id>,
    /// numbered levels: this thread's ids of numbers, the parent's numbers, an encoding, a blank state
    nums: Nums,
    pnums: Vec<u32>,
    tmp2: Vec<u8>,
    blank: Option<StateRef>,
}
impl Scratch {
    /// A state without values (filled when something needs them), reused unless something kept it.
    fn blank_state(&mut self, nv: usize) -> StateRef {
        match &self.blank {
            // (ours plus the evaluator's make two)
            Some(b) if Rc::strong_count(b) <= 2 => b.clone(),
            _ => {
                let b = StateData::blank(nv);
                self.blank = Some(b.clone());
                b
            }
        }
    }
}

struct Engine {
    /// the main thread's `Checker::verdicts`, set before each level
    verdicts: Arc<[crate::compile::Verdict]>,
    txs: Vec<Sender<ToWorker>>,
    rx: Receiver<FromWorker>,
    fps: Arc<FpSet>,
}
impl Engine {
    /// Starts the workers; they load the specification meanwhile (`wait_ready`).
    fn spawn(cfg: &ParConfig, flags: Flags) -> Result<Engine, String> {
        let (tx, rx) = channel::<FromWorker>();
        let mut txs = vec![];
        for i in 0..cfg.workers {
            let (wtx, wrx) = channel::<ToWorker>();
            let (factory, tx) = (cfg.factory.clone(), tx.clone());
            let spawned = std::thread::Builder::new().name(format!("worker-{}", i + 1)).stack_size(STACK).spawn(move || worker_main(factory, flags, wrx, tx));
            if spawned.is_err() {
                return Err("a worker thread could not be started".into());
            }
            txs.push(wtx);
        }
        drop(tx);
        Ok(Engine { verdicts: Arc::new([]), txs, rx, fps: Arc::new(FpSet::with_capacity(2)) })
    }
    /// Waits until every worker has loaded the specification.
    fn wait_ready(self) -> Result<Engine, String> {
        let mut failure = None;
        for _ in 0..self.txs.len() {
            match self.rx.recv() {
                Ok(FromWorker::Ready(Ok(()))) => {}
                Ok(FromWorker::Ready(Err(why))) => failure = Some(why),
                _ => failure = Some("a worker thread stopped unexpectedly".to_string()),
            }
        }
        match failure {
            Some(why) => Err(why), // dropping the engine tells the workers to leave
            None => Ok(self),
        }
    }
    /// Hands the workers a level (or the initial states); they report chunks, then `Done` each.
    fn start_job(&mut self, init: bool, frontier: Arc<Batch>, lvl: u32, chunk: usize) -> Arc<Job> {
        self.start_job_with(init, frontier, lvl, chunk, None, None)
    }
    fn start_job_with(&mut self, init: bool, frontier: Arc<Batch>, lvl: u32, chunk: usize, firsts: Option<Firsts>, dict: Option<Arc<Dict>>) -> Arc<Job> {
        let verdicts = self.verdicts.clone();
        let job = Arc::new(Job { init, firsts, dict, verdicts, frontier, lvl, chunk, next: AtomicUsize::new(0), stop: AtomicUsize::new(usize::MAX), fps: self.fps.clone() });
        for tx in &self.txs {
            tx.send(ToWorker::Level(job.clone())).expect("a worker thread stopped unexpectedly");
        }
        job
    }
    /// Has the workers run a claim (see `Claim`).
    fn claim(&mut self, c: Arc<Claim>) {
        for tx in &self.txs {
            tx.send(ToWorker::Claim(c.clone())).expect("a worker thread stopped unexpectedly");
        }
        drop(c);
        self.wait_finished();
    }
    fn wait_finished(&mut self) {
        let mut done = 0;
        while done < self.txs.len() {
            if let FromWorker::Finished = self.rx.recv().expect("a worker thread stopped unexpectedly") {
                done += 1;
            }
        }
    }
    /// Makes room in the fingerprint set for `more` fingerprints; the workers move a segmented set.
    fn make_room(&mut self, more: usize) {
        let fps = Arc::get_mut(&mut self.fps).expect("parallel search: the fingerprint set is still shared");
        while !fps.segmented() {
            fps.grow();
        }
        let mut cap = fps.capacity();
        while (fps.len() + more) * 2 >= cap {
            cap *= 2;
        }
        if cap == fps.capacity() {
            return;
        }
        let old = std::mem::replace(fps, FpSet::with_capacity(2));
        let new = old.empty_like(cap);
        let g = Arc::new(Grow { old, new, next: AtomicUsize::new(0) });
        for tx in &self.txs {
            tx.send(ToWorker::Grow(g.clone())).expect("a worker thread stopped unexpectedly");
        }
        self.wait_finished();
        let g = Arc::into_inner(g).expect("parallel search: a worker still holds the fingerprint set");
        *Arc::get_mut(&mut self.fps).expect("parallel search: the fingerprint set is still shared") = g.new;
    }
    /// Has the workers expand a level; the reports sorted by position, and where they stopped.
    fn run(&mut self, init: bool, frontier: Arc<Batch>, lvl: u32, chunk: usize) -> (Vec<ChunkOut>, usize) {
        self.run_with(init, frontier, lvl, chunk, None, None)
    }
    fn run_with(&mut self, init: bool, frontier: Arc<Batch>, lvl: u32, chunk: usize, firsts: Option<Firsts>, dict: Option<Arc<Dict>>) -> (Vec<ChunkOut>, usize) {
        let job = self.start_job_with(init, frontier, lvl, chunk, firsts, dict);
        let mut chunks = vec![];
        let mut done = 0;
        while done < self.txs.len() {
            match self.rx.recv().expect("a worker thread stopped unexpectedly") {
                FromWorker::Chunk(c) => chunks.push(c),
                FromWorker::Done => done += 1,
                FromWorker::Ready(_) | FromWorker::Finished => {}
            }
        }
        chunks.sort_by_key(|c| c.start);
        (chunks, job.stop.load(Ordering::Relaxed))
    }
}
impl Drop for Engine {
    fn drop(&mut self) {
        for tx in &self.txs {
            let _ = tx.send(ToWorker::Exit);
        }
    }
}

// ---------- the main thread ----------
/// Merges the first `upto` states of a chunk of the level starting at state `a`: new states get ids (in
/// order), their encodings go to `found`. `put` and `get` are the fingerprint set.
#[allow(clippy::too_many_arguments)]
fn merge_chunk(ck: &mut Checker, de: &RefCell<De>, c: &ChunkOut, upto: usize, a: usize, lvl: u32, record: bool, found: &mut Batch, put: &mut dyn FnMut(u64, u32) -> Option<u32>, get: &dyn Fn(u64) -> Option<u32>) {
    let nvars = ck.model.vars.len();
    let (mut ei, mut boff) = (0, 0);
    for k in 0..upto {
        let sid = a + c.start + k;
        let (generated, entries) = c.src[k];
        ck.generated += generated;
        let mut fresh = 0u32;
        for _ in 0..entries {
            let e = &c.ent[ei];
            ei += 1;
            let bytes = &c.bytes[boff..boff + e.len as usize];
            boff += e.len as usize;
            let id = match e.kind {
                CAND => {
                    let nid = ck.states.len() as u32;
                    match put(e.fp, nid) {
                        None => {
                            ck.states.push(ck.empty.clone());
                            ck.parent.push(sid as u32);
                            ck.level.push(lvl + 1);
                            ck.act.push(e.act as i32);
                            if record {
                                ck.succ.push(vec![]);
                                ck.succ_act.push(vec![]);
                                if let Some(ss) = &mut ck.succ_state {
                                    ss.push(vec![]);
                                }
                            }
                            found.bytes.extend_from_slice(bytes);
                            found.offs.push(found.bytes.len());
                            fresh += 1;
                            nid
                        }
                        Some(ex) => ex,
                    }
                }
                DUP => get(e.fp).expect("parallel search: a duplicate without its original"),
                _ => e.fp as u32,
            };
            if record {
                ck.succ[sid].push(id);
                ck.succ_act[sid].push(e.act);
                if let Some(ss) = &mut ck.succ_state {
                    ss[sid].push(de.borrow_mut().state(bytes, nvars));
                }
            }
        }
        ck.outdeg.push(fresh);
    }
}
/// `merge_chunk` into the checker's own fingerprint set.
#[allow(clippy::too_many_arguments)]
fn merge_chunk_seq(ck: &mut Checker, de: &RefCell<De>, c: &ChunkOut, upto: usize, a: usize, lvl: u32, record: bool, found: &mut Batch) {
    let mut fps = std::mem::replace(&mut ck.fps, FpSet::with_capacity(2));
    {
        let cell = RefCell::new(&mut fps);
        merge_chunk(ck, de, c, upto, a, lvl, record, found, &mut |fp, id| cell.borrow_mut().put(fp, id), &|fp| cell.borrow().get(fp));
    }
    ck.fps = fps;
}

/// The parallel side of a `Checker`.
pub struct Par {
    cfg: ParConfig,
    engine: Option<Engine>,
    /// workers started at the beginning of the search, not yet known to be ready
    starting: Option<Engine>,
    /// the states found by parallel levels, by ascending first id
    store: Vec<Arc<Batch>>,
    /// the states the last parallel level found: the next level, already serialized
    next: Option<Arc<Batch>>,
    de: RefCell<De>,
    /// the numbers of values for numbered levels (see `Dict`); it outlives the workers, as the levels do
    dict: Arc<Dict>,
    t0: f64,
    off: bool,
    /// how often a level went back to the sequential search because of an order-dependent operator
    strikes: u32,
    /// for EVERYSTATE_PAR_DEBUG: levels and states searched by the workers, and why they stopped
    stats: (u64, u64, Option<String>),
    /// milliseconds: before the first parallel level, in the workers, in the merge
    times: (f64, f64, f64),
}

/// Called once before the search loop.
fn flags_of(ck: &Checker) -> Flags {
    Flags { check_deadlock: ck.opts.check_deadlock, record: ck.opts.record_graph, keep_states: ck.succ_state.is_some() }
}
pub fn prepare(ck: &mut Checker) {
    if let Some(cfg) = ck.opts.par.clone() {
        if cfg.workers > 1 {
            let t0 = ck.t_start;
            // (the workers load the specification while the first levels are searched sequentially)
            let starting = Engine::spawn(&cfg, flags_of(ck)).ok();
            ck.par = Some(Box::new(Par { cfg, engine: None, starting, store: vec![], next: None, de: RefCell::new(De::default()), dict: Arc::new(Dict::new()), t0, off: false, strikes: 0, stats: (0, 0, None), times: (0.0, 0.0, 0.0) }));
            ck.level_end = ck.head;
        }
    }
}

/// Called with the candidates for initial states, before any of them is looked at. Returns how many of
/// them (from the first) the workers have dealt with; the sequential code goes on with the rest.
pub fn init(ck: &mut Checker, found: &[StateRef], events: &mut dyn Events) -> usize {
    match ck.par.take() {
        Some(mut par) => {
            let done = par.init(ck, found, events);
            ck.par = Some(par);
            done
        }
        None => 0,
    }
}

/// Called at the first state of every level. True when the level (or its beginning, up to a state the
/// sequential search has to look at) was searched by the workers; `ck.head` has moved accordingly.
pub fn level(ck: &mut Checker, events: &mut dyn Events) -> bool {
    let mut par = match ck.par.take() {
        Some(p) => p,
        None => {
            ck.level_end = usize::MAX;
            return false;
        }
    };
    let r = par.level(ck, events);
    if par.off {
        ck.level_end = usize::MAX;
    }
    ck.par = Some(par);
    r
}

/// Called when the search is over: the workers leave, and the states are rebuilt when the caller will
/// read them all (`-dump`, liveness).
pub fn finish(ck: &mut Checker) {
    if let Some(mut par) = ck.par.take() {
        if std::env::var_os("EVERYSTATE_PAR_DEBUG").is_some() {
            // Linux: CPU time of this thread and of all threads, in ms (the workers are still alive)
            let cpu = |path: &std::path::Path| std::fs::read_to_string(path).ok().and_then(|t| t.split_whitespace().next().and_then(|x| x.parse::<f64>().ok())).unwrap_or(0.0) / 1e6;
            let main = cpu(std::path::Path::new("/proc/thread-self/schedstat"));
            let all: f64 = std::fs::read_dir("/proc/self/task").map(|d| d.flatten().map(|e| cpu(&e.path().join("schedstat"))).sum()).unwrap_or(0.0);
            eprintln!("par cpu: {:.0} ms main thread, {:.0} ms other threads", main, all - main);
            eprintln!("par: {} levels, {} of {} states expanded by workers, {} handed back{}", par.stats.0, par.stats.1, ck.head, par.strikes, par.stats.2.as_ref().map_or(String::new(), |w| format!("; stopped: {}", w)));
            eprintln!("par times: {:.0} ms before, {:.0} ms workers, {:.0} ms merge, {:.0} ms total", par.times.0, par.times.1, par.times.2, ck.ev.host.borrow().now_ms() - par.t0);
        }
        par.engine = None;
        if ck.opts.record_graph {
            par.materialize(ck, 0);
            par.store = vec![];
        }
        ck.par = Some(par);
    }
}

impl Par {
    /// State `i`, which the parallel search found.
    pub fn load(&self, i: usize, nvars: usize) -> StateRef {
        let k = self.store.partition_point(|b| b.base <= i) - 1;
        let b = &self.store[k];
        match b.nums(i - b.base) {
            Some(xs) => {
                let mut de = self.de.borrow_mut();
                StateData::new(xs.iter().map(|&x| self.dict.value(&mut de, x)).collect())
            }
            None => self.de.borrow_mut().state(b.get(i - b.base), nvars),
        }
    }
    /// Rebuilds the states from `from` on that exist in serialized form only.
    fn materialize(&mut self, ck: &mut Checker, from: usize) {
        for i in from..ck.states.len() {
            if Rc::ptr_eq(&ck.states[i], &ck.empty) {
                ck.states[i] = self.load(i, ck.model.vars.len());
            }
        }
    }
    /// From here on the search is sequential.
    fn give_up(&mut self, ck: &mut Checker, events: &mut dyn Events, why: &str) {
        self.off = true;
        self.engine = None;
        self.starting = None;
        self.next = None;
        self.materialize(ck, ck.head);
        self.stats.2 = Some(why.to_string());
        events.note(&format!("The search continues with 1 worker instead of {}: {}.", self.cfg.workers, why));
    }

    /// A worker met a state that only the sequential search may expand (an operator whose effect depends
    /// on the order of exploration, a value that cannot be passed on). The sequential search finishes
    /// this level from that state on, which keeps every such effect in its sequential order; the next
    /// level goes to the workers again. They are replaced, because the abandoned evaluation may have left
    /// something behind in their evaluators. The third time is the last.
    fn strike(&mut self, ck: &mut Checker, events: &mut dyn Events, why: &str) {
        self.strikes += 1;
        if self.strikes >= 3 {
            return self.give_up(ck, events, why);
        }
        self.engine = None;
        self.next = None;
        self.materialize(ck, ck.head);
    }

    /// Whether `n` states are worth handing to the workers; starts them when they are. (Starting them
    /// takes a few milliseconds; a level of `BIG_LEVEL` states takes longer than that on one thread.)
    fn ready(&mut self, ck: &mut Checker, events: &mut dyn Events, n: usize) -> bool {
        if !self.off && crate::eval::WORKERS.load(Ordering::Relaxed) < 2 {
            self.give_up(ck, events, "the specification reads TLCGet(\"config\")");
        }
        if self.off || n < self.cfg.min_frontier || !(self.cfg.eager || n >= BIG_LEVEL || ck.ev.host.borrow().now_ms() - self.t0 >= 50.0) {
            return false;
        }
        if self.engine.is_none() {
            let ts = ck.ev.host.borrow().now_ms();
            let started = match self.starting.take() {
                Some(e) => Ok(e),
                None => Engine::spawn(&self.cfg, flags_of(ck)),
            }
            .and_then(Engine::wait_ready);
            if std::env::var_os("EVERYSTATE_PAR_DEBUG").is_some() {
                eprintln!("par: workers started in {:.1} ms, {:.1} ms after the search began", ck.ev.host.borrow().now_ms() - ts, ts - self.t0);
            }
            match started {
                Ok(e) => self.engine = Some(e),
                Err(why) => {
                    self.give_up(ck, events, &why);
                    return false;
                }
            }
        }
        self.engine.as_mut().unwrap().verdicts = ck.verdicts().into();
        true
    }
    fn chunk(&self, n: usize) -> usize {
        if self.cfg.chunk > 0 { self.cfg.chunk } else { (n / (self.cfg.workers * 8)).clamp(1, 256) }
    }

    fn init(&mut self, ck: &mut Checker, cands: &[StateRef], events: &mut dyn Events) -> usize {
        let n = cands.len();
        let nvars = ck.model.vars.len();
        if !self.ready(ck, events, n) {
            return 0;
        }
        let mut f = Batch::new(0);
        for s in cands {
            if !ser_state(s, nvars, &mut f.bytes) {
                self.give_up(ck, events, UNSENDABLE);
                return 0;
            }
            f.offs.push(f.bytes.len());
        }
        let frontier = Arc::new(f);
        let t1 = ck.ev.host.borrow().now_ms();
        if self.stats.0 == 0 && self.times.0 == 0.0 {
            self.times.0 = t1 - self.t0;
        }
        let chunk = self.chunk(n);
        let eng = self.engine.as_mut().unwrap();
        std::mem::swap(&mut ck.fps, Arc::get_mut(&mut eng.fps).expect("parallel search: the fingerprint set is still shared"));
        let (chunks, stop) = eng.run(true, frontier.clone(), 1, chunk);
        let eng = self.engine.as_mut().unwrap();
        std::mem::swap(&mut ck.fps, Arc::get_mut(&mut eng.fps).expect("parallel search: the fingerprint set is still shared"));
        let t2 = ck.ev.host.borrow().now_ms();
        self.times.1 += t2 - t1;
        let p = stop.min(n);
        let record = ck.opts.record_graph;
        let mut found = Batch::new(ck.states.len());
        let mut pos = 0;
        let mut event: Option<Event> = None;
        for c in chunks {
            if c.start + c.done == p && c.event.is_some() {
                event = c.event;
            }
            if c.start >= p {
                continue;
            }
            assert_eq!(c.start, pos, "parallel search: a part of the initial states is missing");
            let upto = c.done.min(p - c.start);
            let mut ei = 0;
            for k in 0..upto {
                ck.generated += 1;
                ck.init_generated += 1;
                if c.src[k].1 == 0 {
                    continue;
                }
                let e = &c.ent[ei];
                ei += 1;
                let nid = ck.states.len() as u32;
                if ck.fps.put(e.fp, nid).is_none() {
                    ck.states.push(ck.empty.clone());
                    ck.parent.push(NO_PARENT);
                    ck.level.push(1);
                    ck.act.push(-1);
                    ck.inits.push(nid);
                    if record {
                        ck.succ.push(vec![]);
                        ck.succ_act.push(vec![]);
                        if let Some(ss) = &mut ck.succ_state {
                            ss.push(vec![]);
                        }
                    }
                    ck.depth = ck.depth.max(1);
                    ck.init_distinct += 1;
                    found.bytes.extend_from_slice(frontier.get(c.start + k));
                    found.offs.push(found.bytes.len());
                }
            }
            pos += upto;
        }
        assert_eq!(pos, p, "parallel search: a part of the initial states is missing");
        self.stats.1 += p as u64;
        self.times.2 += ck.ev.host.borrow().now_ms() - t2;
        if found.len() > 0 {
            let found = Arc::new(found);
            self.store.push(found.clone());
            if p == n {
                self.next = Some(found);
            }
        }
        if p < n {
            match event {
                Some(Event::Fallback(why)) => self.strike(ck, events, &why),
                _ => {
                    self.off = true;
                    self.engine = None;
                    self.next = None;
                    self.materialize(ck, 0);
                    self.stats.2 = Some("violation or error".into());
                }
            }
        }
        p
    }

    /// A level whose workers find successors as ids (`expand_ids`), without the state graph. In two
    /// steps, both on the workers: they expand the level, each chunk's candidates for new states in
    /// state order; then they put the candidates into the fingerprint set, each worker the fingerprints
    /// of its own segments of the set (`Claim`), in the order of the level, so that the first occurrence
    /// of a fingerprint is the one the sequential search meets first. The main thread only numbers the
    /// new states in that order. (The ids kept in the set are not those of the states: nothing reads
    /// them without the state graph.)
    fn level_ids(&mut self, ck: &mut Checker, events: &mut dyn Events, frontier: Arc<Batch>, lvl: u32, chunk: usize, t1: f64) -> bool {
        let (a, n) = (frontier.base, frontier.len());
        let eng = self.engine.as_mut().unwrap();
        std::mem::swap(&mut ck.fps, Arc::get_mut(&mut eng.fps).expect("parallel search: the fingerprint set is still shared"));
        // (room for a few new fingerprints per state; more than that only makes candidates)
        let firsts = Firsts::new((4 * n).next_power_of_two().max(1 << 12));
        let (chunks, stop) = eng.run_with(false, frontier, lvl, chunk, Some(firsts), Some(self.dict.clone()));
        let t2 = ck.ev.host.borrow().now_ms();
        self.times.1 += t2 - t1;
        // the level ends at the first state a worker stopped at
        let p = stop.min(n);
        let mut event: Option<Event> = None;
        let mut upto = Vec::with_capacity(chunks.len());
        let mut states = Vec::with_capacity(chunks.len());
        let mut cands = 0;
        let mut pos = 0;
        for c in &chunks {
            if c.start + c.done == p && c.event.is_some() {
                event = c.event.as_ref().map(|e| match e {
                    Event::Check => Event::Check,
                    Event::Fallback(w) => Event::Fallback(w.clone()),
                });
            }
            let u = if c.start >= p { 0 } else { c.done.min(p - c.start) };
            if u > 0 {
                assert_eq!(c.start, pos, "parallel search: a part of the level is missing");
                pos += u;
            }
            let e = c.src[..u].iter().map(|x| x.1 as usize).sum::<usize>();
            cands += e;
            states.push(u);
            upto.push(e);
        }
        assert_eq!(pos, p, "parallel search: a part of the level is missing");
        eng.make_room(cands);
        let wins = (0..CLAIM_GROUPS).map(|_| Default::default()).collect();
        let claim = Arc::new(Claim { chunks, upto, fps: eng.fps.clone(), next: AtomicUsize::new(0), wins });
        let tb = ck.ev.host.borrow().now_ms();
        eng.claim(claim.clone());
        let tc = ck.ev.host.borrow().now_ms();
        let Claim { chunks, wins, fps: shared, .. } = Arc::into_inner(claim).expect("parallel search: a worker still holds the claim");
        // per chunk, one bit per entry: a new state
        let mut win: Vec<Vec<u64>> = chunks.iter().map(|c| vec![0; c.ent.len().div_ceil(64)]).collect();
        let mut news = 0;
        for w in wins {
            let w = w.into_inner().unwrap();
            news += w.len();
            for (ci, ei) in w {
                win[ci as usize][ei as usize / 64] |= 1 << (ei % 64);
            }
        }
        drop(shared);
        std::mem::swap(&mut ck.fps, Arc::get_mut(&mut eng.fps).expect("parallel search: the fingerprint set is still shared"));
        // the new states, numbered in the order of the level
        let nv = ck.model.vars.len();
        let mut found = Batch::numbered(ck.states.len(), nv);
        ck.states.reserve(news);
        ck.parent.reserve(news);
        ck.level.reserve(news);
        ck.act.reserve(news);
        ck.outdeg.reserve(p);
        let nums = &mut found.nums.as_mut().unwrap().1;
        nums.reserve(news * nv);
        for (ci, c) in chunks.iter().enumerate() {
            debug_assert!(c.bytes.is_empty(), "a numbered level has no encodings");
            let mut ei = 0;
            for k in 0..states[ci] {
                let sid = a + c.start + k;
                let (generated, entries) = c.src[k];
                ck.generated += generated;
                let mut fresh = 0u32;
                for _ in 0..entries {
                    let e = &c.ent[ei];
                    if win[ci][ei / 64] >> (ei % 64) & 1 == 1 {
                        ck.states.push(ck.empty.clone());
                        ck.parent.push(sid as u32);
                        ck.level.push(lvl + 1);
                        ck.act.push(e.act as i32);
                        nums.extend_from_slice(&c.nums[ei * nv..(ei + 1) * nv]);
                        fresh += 1;
                    }
                    ei += 1;
                }
                ck.outdeg.push(fresh);
            }
        }
        debug_assert!(NO_PARENT as usize > ck.states.len());
        if std::env::var_os("EVERYSTATE_PAR_DEBUG").is_some() {
            let td = ck.ev.host.borrow().now_ms();
            eprintln!("par: level {}: {} states, {} candidates, {} new; expand {:.1} ms, prepare {:.1} ms, claim {:.1} ms, number {:.1} ms", lvl, p, cands, found.len(), t2 - t1, tb - t2, tc - tb, td - tc);
        }
        ck.head = a + p;
        ck.cur_level = lvl;
        self.stats.0 += 1;
        self.stats.1 += p as u64;
        self.times.2 += ck.ev.host.borrow().now_ms() - t2;
        self.end_level(ck, events, found, p == n, event)
    }

    fn level(&mut self, ck: &mut Checker, events: &mut dyn Events) -> bool {
        let (a, b) = (ck.head, ck.states.len());
        let n = b - a;
        let nvars = ck.model.vars.len();
        if !self.ready(ck, events, n) {
            // this level is searched sequentially
            self.next = None;
            self.materialize(ck, a);
            return false;
        }
        let frontier = match self.next.take() {
            Some(f) if f.base == a && f.len() == n => f,
            _ => {
                let mut f = Batch::new(a);
                for i in a..b {
                    if !ser_state(&ck.states[i], nvars, &mut f.bytes) {
                        self.give_up(ck, events, UNSENDABLE);
                        return false;
                    }
                    f.offs.push(f.bytes.len());
                }
                Arc::new(f)
            }
        };
        let lvl = ck.level[a];
        let chunk = self.chunk(n);
        let t1 = ck.ev.host.borrow().now_ms();
        if self.stats.0 == 0 && self.times.0 == 0.0 {
            self.times.0 = t1 - self.t0;
        }
        if ck.is_flat() && !ck.opts.record_graph && ck.caching() {
            // (the workers find successors as ids: see `level_ids`)
            return self.level_ids(ck, events, frontier, lvl, chunk, t1);
        }
        let eng = self.engine.as_mut().unwrap();
        // The workers read the fingerprint set while they run, and the chunks they finish are merged
        // meanwhile, in state order, into the same set (which has room for them; see `FpSet`). A chunk
        // is merged early only when it and every chunk before it are whole; the rest waits for the end
        // of the level, when it is known where the workers stopped. So does the rest of the level once
        // the set has no room left without growing, which it can do only when nobody reads it.
        let fps_now = Arc::get_mut(&mut eng.fps).expect("parallel search: the fingerprint set is still shared");
        std::mem::swap(&mut ck.fps, fps_now);
        let job = eng.start_job(false, frontier, lvl, chunk);
        let record = ck.opts.record_graph;
        let mut found = Batch::new(b);
        let mut pos = 0;
        let mut pending: std::collections::BTreeMap<usize, ChunkOut> = Default::default();
        let mut early = true;
        let mut merge_ms = 0.0;
        let mut done = 0;
        while done < eng.txs.len() {
            match eng.rx.recv().expect("a worker thread stopped unexpectedly") {
                FromWorker::Chunk(c) => {
                    pending.insert(c.start, c);
                }
                FromWorker::Done => done += 1,
                FromWorker::Ready(_) | FromWorker::Finished => {}
            }
            while early {
                let whole = match pending.get(&pos) {
                    Some(c) => c.event.is_none() && c.done == chunk.min(n - c.start),
                    None => break,
                };
                let c = pending.remove(&pos).unwrap();
                let cands = c.ent.iter().filter(|e| e.kind == CAND).count();
                if !whole || !job.fps.room(cands) {
                    pending.insert(c.start, c);
                    early = false;
                    break;
                }
                let tm = ck.ev.host.borrow().now_ms();
                merge_chunk(ck, &self.de, &c, c.done, a, lvl, record, &mut found, &mut |fp, id| job.fps.put_shared(fp, id).expect("parallel search: no room in the fingerprint set"), &|fp| job.fps.get(fp));
                merge_ms += ck.ev.host.borrow().now_ms() - tm;
                pos += c.done;
            }
        }
        let stop = job.stop.load(Ordering::Relaxed);
        drop(job);
        let eng = self.engine.as_mut().unwrap();
        let fps_now = Arc::get_mut(&mut eng.fps).expect("parallel search: the fingerprint set is still shared");
        std::mem::swap(&mut ck.fps, fps_now);

        let t2 = ck.ev.host.borrow().now_ms();
        self.times.1 += t2 - t1;
        self.times.2 += merge_ms;
        // merge, in state order, everything before the first state a worker stopped at
        let p = stop.min(n);
        let mut event: Option<Event> = None;
        for (_, mut c) in pending {
            if c.start + c.done == p && c.event.is_some() {
                event = c.event.take();
            }
            if c.start >= p {
                continue;
            }
            assert_eq!(c.start, pos, "parallel search: a part of the level is missing");
            let upto = c.done.min(p - c.start);
            merge_chunk_seq(ck, &self.de, &c, upto, a, lvl, record, &mut found);
            pos += upto;
        }
        assert_eq!(pos, p, "parallel search: a part of the level is missing");
        debug_assert!(NO_PARENT as usize > ck.states.len());
        ck.head = a + p;
        ck.cur_level = lvl;
        self.stats.0 += 1;
        self.stats.1 += p as u64;
        self.times.2 += ck.ev.host.borrow().now_ms() - t2;
        self.end_level(ck, events, found, p == n, event)
    }
    /// After a level: `found` is the next one (`complete`: the workers expanded the whole level), else
    /// the sequential search takes over at `ck.head` because of `event`.
    fn end_level(&mut self, ck: &mut Checker, events: &mut dyn Events, found: Batch, complete: bool, event: Option<Event>) -> bool {
        let lvl = ck.cur_level;
        if found.len() > 0 {
            ck.depth = ck.depth.max(lvl + 1);
            let found = Arc::new(found);
            self.store.push(found.clone());
            if complete {
                self.next = Some(found);
            }
        }
        if !complete {
            match event {
                Some(Event::Fallback(why)) => self.strike(ck, events, &why),
                _ => {
                    // the sequential search re-expands state `head` and reports what the worker met
                    self.off = true;
                    self.engine = None;
                    self.next = None;
                    self.materialize(ck, ck.head);
                    self.stats.2 = Some("violation or error".into());
                }
            }
            return true;
        }
        let now = ck.ev.host.borrow().now_ms();
        if now - ck.last_progress > 60000.0 {
            ck.last_progress = now;
            events.progress(ck.depth, ck.generated, ck.states.len() as u64, (ck.states.len() - ck.head) as u64);
        }
        true
    }
}
