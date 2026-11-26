# RFD0001 - The search on value ids

- Feature Name: `search-on-value-ids`
- Status: Implemented (snapshot of branch `perf/interned-values`)
- Author: `leostera`
- Start Date: `2026-11-25`
- Updated: `2026-11-26`
- Discussion PR: `TBD`
- Tracking Issue: `TBD`

This RFD records a change that is already implemented. It says what the search does now and why,
and what it measured. It is not a proposal for a redesign.

## Summary

Every distinct value the search keeps is stored once, in a per-thread table, and has a small
number: its **id**. Booleans and integers within ±2^28 have **immediate** ids, which hold the value
itself. The step cache is keyed on ids and stores successors as ids. When a model is *flat* (no
VIEW, SYMMETRY, constraints or action properties), the search on one thread keeps states as rows of
ids. A successor is then its parent's row with a few ids replaced, and its fingerprint is the
parent's fingerprint with the terms of those ids replaced. With several workers, each worker runs
the same id path on the states it is given. The main thread merges each finished chunk while the
workers go on. Results do not change: states, counts, depth, verdicts and traces are the same.

On the five larger actor models, CPU time on one worker drops from 6.00 s to 2.70 s in total
(2.2×), and peak memory drops by 60 to 70 %. On 8 workers, wall time drops from 1.56 s to 0.76 s
(2.1×). The 12 BENCHMARK.md models and the 125 Feynman configurations agree with before. The
BENCHMARK.md models take the same time in total, within 3 % on each model; the Feynman
configurations take 1.44× less CPU.

## Motivation

On actor-style models, with messages in a bag and a few counters, profiles of 0.4.1 showed that
most of the time went to work on the same values over and over:

- comparing values in full to decide whether a step-cache entry applies (`same`);
- hashing and building successor states that were then found to be known (about 85 % of
  successors are known states);
- keeping every state as its own tree of reference-counted values, even though neighbouring
  states share almost all of them. OrSet-fixed-f4 had a peak RSS of 314 MB for 524,832 states.

The step cache (0.4.1) already found that most steps repeat. What was missing was a cheap way to
say "this is the same value": a pointer comparison when two values are canonical, and an integer
key when one is used in a table.

## Goals

- The same results as 0.4.1 for every model, on any number of workers.
- Less CPU time on one worker, the default, on models where the step cache hits.
- Less memory, from sharing equal values.
- A parallel search that uses the same id path, so that adding workers adds speed.
- No slowdown beyond noise on the 12 BENCHMARK.md models.

## Non-goals

- A table of values shared between threads. Values are `Rc` trees and stay on their thread.
- Changing the parallel engine's design: chunks of a level are handed to workers, and one
  coordinator merges them in state order (see the comment at the top of `src/par.rs`).
- Making models faster where the step cache does not pay, such as MCLamportMutex, where every
  unit is measured as not paying.

## Guide-level explanation

Nothing changes in how everystate is used. `-workers N`, `EVERYSTATE_STEP_CACHE` and
`EVERYSTATE_EVAL` keep their meaning. `EVERYSTATE_EVAL_STATS=1` now also prints the statistics
of each worker's step cache, and the counters of the two id memos (`changes applied`,
`locations looked up`).

How to think about it:

- **A value has one canonical form and one node.** The table (`src/hashcons.rs`) interns tuples,
  records, functions and explicit sets bottom-up. Each node carries a tag, `epoch << 32 | id`.
  Two canonical values of the same epoch are equal exactly when they are the same node
  (`hashcons::ident`). Lazy and symbolic values, intervals and operators are never interned,
  and they keep the full comparison.
- **An id is a dense `u32`.** Ids below 2^30 are table entries. Ids from 2^30 up to 2^31 are
  immediate: false, true, and the integers from −2^28 to 2^28 − 1. Ids from 2^31 up mark values
  that cannot be interned (`NOT_INTERNED + i`, an index into a side vector).
- **A step-cache entry is integers.** A template is keyed by (unit, the ids of the bound values)
  and lists the *locations* the evaluation read, such as `net[m]`. A leaf is keyed by (template
  version, the ids found at those locations) and holds each successor as the variables it
  changes. Each change is either `Put::Id(x)` or `Put::Delta { list, ops }`. A hit compares
  integers and copies the parent's row of ids with a few of them replaced.
- **A successor row has a fingerprint before it has a state.** A state's fingerprint is
  `fp_finish` of a sum of one term per variable, and each term mixes the variable's index with
  the word of its value (`value_word`). The word depends only on the value's content, so every
  thread computes the same one. The fingerprint of a successor row is the parent's sum with the
  changed ids' terms swapped. A state is built from its ids only when it is new and has to be
  expanded, or when its invariants have to be checked.

### Example: one step of OrSet-fixed-f4 on one worker (the ids are illustrative)

1. The state with id row `[17, 4, 1073742000, …]` is expanded. Its values are taken from the
   table, and they are canonical.
2. The unit `Deliver(m)` is looked up with bound ids `[m = 812]`. The template lists the location
   `net[812]`, and the leaf is keyed by the id found there. On a hit, the leaf gives two
   successors. One changes `net` by "remove one 812", and the memo `Applied[(list 3, parent id
   17)]` already holds the resulting id. The other also changes `seen` to `Put::Id(951)`.
3. The two rows are the parent's with those ids replaced. Their fingerprints are the parent's
   sum with two or three terms swapped. One of them is in the fingerprint set, so nothing more is
   done for it. The other is new: its row of ids is pushed to the `IdStore`, and its values are
   built only if there are invariants to check.

## Reference-level explanation

### Interning (`src/hashcons.rs`)

- There is one `Table` per thread. `reset()` runs in `Checker::new` and moves the table to a new
  epoch, so nodes interned by an earlier check are not taken as canonical. A node whose tag has
  another epoch counts as not interned.
- `canon(v)` interns the children first, then the node. The node is keyed by the children's
  words, which are the same words the fingerprint uses and are cached in the node.
- `id(v)` interns `v`. `id_if_canonical(v)` only reads the tag, or the immediate id, and never
  interns. `value(id)` and `word(id)` read the table, or decode an immediate id.
  `with_ids(|ids| …)` borrows the table once for loops over many ids.
- Invariant: a canonical node is never mutated. The table holds a reference to it, so
  `Rc::get_mut` fails and every in-place `EXCEPT` clones the node. The fast paths that do mutate
  in place (`except_with`) clear `canon` along with the cached hash.

### The step cache on ids (`src/stepcache.rs`, `src/compile.rs`)

- `store()` turns what an evaluation recorded into a template and a leaf. Every absolute write is
  stored as `Put::Id`, including a write equal to the parent's value. An earlier version dropped
  such writes, which broke DieHard-like models. `test/stepcache.test.ts` covers that case.
- `Applied` is a direct-mapped memo with 2^18 slots, mapping (number of the change list, parent
  id) to a result id. `list_number` numbers change lists by their content, so equal changes in
  different entries share their results. The numbering is capped at 2^20 lists.
- `Located` is a direct-mapped memo with 2^16 slots, mapping (value id, key id, kind) to the id
  found there.
- `cached_rows` appends a hit's rows directly to the caller's `Rows`.

### The search in id mode (`src/checker.rs`)

- `idmode = flat && caching()`, both on one thread and in workers.
- `IdStore` keeps one row of `nvars` ids per state, plus the values that cannot be interned.
  `states[i]` holds the shared `empty` placeholder, and `state_at(i)` rebuilds the state.
- `successors_ids` collects successors as rows of ids. `id_fingerprints` computes their
  fingerprints. A known fingerprint ends the work on that successor.
- Outside id mode, a new state is interned (`canon_state`) only while some unit uses the step
  cache (`Plans::caching_now`). Interning costs about 5 % of the search when no unit pays
  (MCNanoMedium).

### The parallel search on ids (`src/par.rs`)

- A worker decodes the encoded parent through `Enc`, a per-worker memo from the bytes of a
  variable to its id. Values of 9 bytes or fewer are decoded directly. The worker then runs
  `successors_ids` and `id_fingerprints`. It encodes a candidate from the parent's encoding, plus
  the memoised encodings of the ids that changed.
- `FpSet` has one writer and many readers. A slot's id is stored before its key, the key is
  stored with release ordering, and readers load it with acquire ordering. Only `&mut self` can
  grow the set. The sequential search uses `&mut` access and plain loads.
- The main thread merges a chunk while the workers are still running. It does so only when that
  chunk and every chunk before it arrived whole, and when the set has room for the chunk's
  candidates without growing. Everything else is merged at the end of the level, as before. So
  the merge still runs in state order, and where a level stops is decided as before. A worker
  that sees a state inserted earlier in the same level reports it as known. That state was
  already checked by the worker that reported it first.
- On macOS, worker threads ask for the user-interactive QoS class.
- A level of 2,048 states or more goes to the workers even before the search has run for 50 ms.

### Fingerprint partitioning (RFD0007 in tsmodel) was not done

The plan included partitioning states among workers by fingerprint, as in SPIN or Murφ, with at
most 10 % overhead. It was not implemented, for three reasons:

- The coordinator design already keeps worlds on the thread that made them, and sends only
  fingerprints and the encodings of candidates.
- Partitioning would send every successor whose fingerprint another worker owns, about 7/8 of
  them. Today only candidates are sent, and about 85 % of successors are not candidates.
- Each worker has its own value table. Ids are not meaningful across threads, so a successor
  would have to be re-encoded for its owner.

The overhead of the parallel search compared with one thread is not within 10 %. On 8 workers,
the five models take 5.05 s of CPU against 2.70 s on one thread. Profiles show that the same
successor work costs about 1.4× more per state in a worker. The likely cause is caches: each
worker has its own value table and step cache, and together they compete for one L2.

## Validation

- `npm test` passes: node tests 48/48, community 21/21, workers 27/27. The new
  `test/stepcache.test.ts` runs 6 models, each with the step cache always on, off, and with the
  tree-walker.
- `scripts/engine-diff.mjs` compared 810 models: tlaplus/Examples models that TLC checks in
  5 s or less, the 12 BENCHMARK.md models, TLC's `test-model` directory, and the Feynman oracle
  configurations. It compares json and text output, stdout and stderr, against 28fd7c5.
  - One worker: 805 identical. EWD840 timed out only on 28fd7c5, and 4 timed out on both.
  - 8 workers, with `EVERYSTATE_PAR_MIN=1` so that every level is parallel, against 28fd7c5 on 8
    workers: 806 identical. EWD998Chan timed out only on 28fd7c5, and 3 timed out on both.
  - The step cache off against always: 793 of 798 identical. EWD840 timed out only with the
    cache off, and 4 timed out on both.
- `scripts/feynman-bench.ts` on the 125 configurations: 0 disagreements.
- Every benchmark run below agreed on status, distinct, generated and depth.
- Java was not available on this machine, so `diff-tlc.mjs` (live TLC) was not run.

## Measurements

The machine is an Apple M4 Pro with 8 performance and 4 efficiency cores and 48 GB of memory.
Each run is a whole process. Builds and worker counts are interleaved round by round. Each cell
is a median of 5 runs, or 3 for bench12. The raw runs are in `bench/search/*.json`. The tables
and charts are generated from them by `scripts/plot-bench.ts`; see `bench/search/README.md`.

### The five larger models, one worker (CPU s)

| model | distinct | 28fd7c5 | hashcons (afa9e05) | id cache (db119b1) | final (e1cf1ce) | final ratio | RSS MB before / after |
|---|---:|---:|---:|---:|---:|---:|---:|
| OrSet-fixed-f1 | 129,242 | 0.486 | 0.503 | 0.197 | 0.200 | 2.43× | 82 / 24 |
| OrSet-fixed-f4 | 524,832 | 2.04 | 2.16 | 0.731 | 0.761 | 2.67× | 314 / 86 |
| ReadRepair-fixed-f6 | 383,579 | 1.69 | 1.93 | 0.873 | 0.861 | 1.97× | 204 / 59 |
| LostUpdate-fixed-f6 | 420,646 | 1.38 | 1.51 | 0.644 | 0.676 | 2.03× | 201 / 55 |
| LeaseLock-fixed-f5 | 122,728 | 0.408 | 0.453 | 0.197 | 0.205 | 1.99× | 68 / 25 |
| **total** | | 6.00 | 6.55 | 2.64 | 2.70 | 2.22× | |

Interning alone (afa9e05) makes the search 9 % slower in CPU. It halves memory. Interning a
freshly built successor costs about as much as the identity comparisons save. The gain comes
when the cache and the search work on ids. From db119b1 to e1cf1ce, one worker got 2 % slower,
for two reasons:

- Integers are immediate, so the uncached path is cheaper. One unit of OrSet-fixed-f4 now loses
  its trial against the cache: 1,134 ns against 1,210 ns per state. With
  `EVERYSTATE_STEP_CACHE=always` the run takes 0.74 s.
- Code layout changed.

### The five larger models, 8 workers (wall s)

| model | 28fd7c5 | final | ratio | CPU s before / after |
|---|---:|---:|---:|---:|
| OrSet-fixed-f1 | 0.182 | 0.080 | 2.28× | 0.71 / 0.46 |
| OrSet-fixed-f4 | 0.528 | 0.237 | 2.23× | 3.18 / 1.59 |
| ReadRepair-fixed-f6 | 0.386 | 0.201 | 1.92× | 2.28 / 1.42 |
| LostUpdate-fixed-f6 | 0.320 | 0.175 | 1.83× | 1.76 / 1.21 |
| LeaseLock-fixed-f5 | 0.141 | 0.064 | 2.20× | 0.52 / 0.38 |
| **total** | 1.56 | 0.757 | 2.06× | 8.45 / 5.05 |

The default is one worker. Against the default of 28fd7c5, 8 workers on the final build are
7.9× faster in wall time (6.01 s to 0.757 s).

### The 12 BENCHMARK.md models (wall s, median of 3)

On one worker the total is 45.28 s before and 45.25 s after (1.00×). Every model is within 3 %:

- slower: SimpleRegular 0.97×, MCLamportMutex 0.97×, Paxos 0.98×, StaleShrinkV6Wait2x 0.98×;
- faster: MCBakery 1.05×, MCbtree 1.02×;
- the rest are within 1 %.

Memory drops on most models (SimpleRegular 155 → 58 MB, MCbtree 188 → 76 MB). It grows on
MCLamportMutex (528 → 599 MB), where every unit is measured as not paying.

On 8 workers the total is 16.88 s before and 9.97 s after (1.69×). GameOfLife goes from 7.27 s to
1.19 s. Paxos (0.96×) and TCommit are the only models that are not faster.

### The 125 Feynman configurations (CPU ms, median of 5)

The total is 1,708 ms on 28fd7c5 and 1,184 ms after (1.44×). The 11 configurations that take
20 ms or more go from 1,223 ms to 704 ms (1.74×). OrSet-fixed-f1 goes from 488 ms to 200 ms.

## Drawbacks

- In-place updates of a canonical value are no longer possible, because the table holds a
  reference to it. A model that updates large functions in place, and where the cache does not
  pay, does a little more copying.
- Each worker keeps its own value table and encoding memo. Memory on 8 workers is about the same
  as on 28fd7c5 for the five models, not lower. On TLC's Calculator model (31 million states of
  one integer), 8 workers peak at 3.1 GB, against 3.3 GB on 28fd7c5.
- When the merge has no room left in the fingerprint set, the rest of the level is merged at its
  end, without overlapping the workers. Making room before the level was measured: it saved about
  5 % of wall time on the five models, and cost Calculator 1.8 GB of memory.
- The adaptive trial that decides which units get the cache costs 2 to 3 % on OrSet-fixed-f4,
  and its verdicts depend on timing. Counts and traces do not depend on them.
- A table has at most 2^30 values. Beyond that, the search stops with an assertion.

## Rationale and alternatives

- **Intern only, without ids (step 1 alone).** This was measured: CPU 0.92×, memory 0.4×. It is
  only worth doing as the base for the id cache.
- **A shared, thread-safe value table.** One table would remove the per-worker duplication and
  the cache effects. It would need values that are `Send + Sync` (`Arc`, and atomic reference
  counts on every clone). That rewrites the evaluator and slows the one-thread path.
- **Fingerprint partitioning.** See above.
- **Reserving room in the fingerprint set before each level.** See Drawbacks.
- **Do nothing.** Actor models stay 2× slower and use 3× more memory on one worker, and
  parallel workers do not scale past about 1×.

## Prior art

- TLC keeps states as fingerprints plus a queue of states, and has no value table.
- Hash-consing is standard in BDD packages and in theorem provers. The epoch tag follows the
  "generation" trick, which avoids clearing node marks.
- SPIN and Murφ partition states by hash among workers (see above for why this is not done here).

## Unresolved questions

- Should `idmode` turn off during the search when every unit is measured as not paying? For
  SimpleRegular and MCLamportMutex, the 2 to 3 % they lose is in that case.
- Can a worker's table be seeded with the values of the frontier, so that its caches warm up
  together with the other workers' caches?

## Future possibilities

- Keep the frontier as rows of ids grouped by worker, so that a worker would not decode its
  parents. Ids would have to be stable across levels for that worker.
- Liveness and `-dump` on id rows. Both need the whole graph, and are not flat today.
