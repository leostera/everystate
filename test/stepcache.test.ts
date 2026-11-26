// The step cache and the search on value ids (src/stepcache.rs, src/hashcons.rs) must not change any
// result: every model below is checked with the cache given to every unit (EVERYSTATE_STEP_CACHE=always),
// without it, and by the tree-walker alone, and the complete -json output (status, counts, trace) must be
// the same. Each model is small, and shaped after a way the cache could go wrong.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';

const bin = path.resolve(import.meta.dirname, '../target/release/everystate' + (process.platform === 'win32' ? '.exe' : ''));
const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'everystate-stepcache-'));
process.on('exit', () => fs.rmSync(dir, { recursive: true, force: true }));

function check(name: string, env: Record<string, string>, extra: string[] = []) {
  const r = spawnSync(bin, ['-json', '-deadlock', ...extra, '-config', name + '.cfg', name + '.tla'], { cwd: dir, encoding: 'utf8', timeout: 120_000, env: { ...process.env, ...env } });
  return r.stdout.trim().split('\n').pop()!;
}

/** Writes the model and checks that the three evaluators agree; returns the result. */
function same(name: string, body: string, cfg: string, extra: string[] = []) {
  fs.writeFileSync(path.join(dir, name + '.tla'), `---- MODULE ${name} ----\n${body}\n====\n`);
  fs.writeFileSync(path.join(dir, name + '.cfg'), cfg + '\n');
  const always = check(name, { EVERYSTATE_STEP_CACHE: 'always' }, extra);
  const off = check(name, { EVERYSTATE_STEP_CACHE: 'off' }, extra);
  const tree = check(name, { EVERYSTATE_EVAL: 'tree' }, extra);
  assert.equal(always, off, `${name}: cache on every unit vs off`);
  assert.equal(off, tree, `${name}: compiled vs tree-walker`);
  return JSON.parse(always);
}

const jugs = `EXTENDS Integers
VARIABLES small, big
Init == small = 0 /\\ big = 0
FillSmall == small' = 3 /\\ big' = big
FillBig == big' = 5 /\\ small' = small
EmptySmall == small' = 0 /\\ big' = big
EmptyBig == big' = 0 /\\ small' = small
SmallToBig == IF big + small =< 5 THEN big' = big + small /\\ small' = 0
                                  ELSE big' = 5 /\\ small' = small - (5 - big)
BigToSmall == IF big + small =< 3 THEN big' = 0 /\\ small' = big + small
                                  ELSE big' = small - (3 - big) /\\ small' = 3
Next == FillSmall \\/ FillBig \\/ EmptySmall \\/ EmptyBig \\/ SmallToBig \\/ BigToSmall
NotFour == big # 4`;

test('an absolute new value that happens to equal the parent value is still absolute', () => {
  // EmptySmall stored in a state where small = 0 must still set small to 0 where it is 3
  const r = same('Jugs', jugs, 'INIT Init\nNEXT Next');
  assert.equal(r.distinct, 16);
  assert.equal(r.generated, 97);
});

test('a counterexample found through cached steps is the shortest one', () => {
  const r = same('JugsBad', jugs, 'INIT Init\nNEXT Next\nINVARIANT NotFour');
  assert.equal(r.status, 'invariant');
  assert.equal(r.trace.length, 7);
});

const bag = `EXTENDS Naturals, Sequences, Bags
CONSTANTS Faults
Nodes == {"a", "b"}
VARIABLES net, seen, log, faults
Init == net = EmptyBag /\\ seen = [n \\in Nodes |-> {}] /\\ log = [n \\in Nodes |-> <<>>] /\\ faults = 0
Send(n, k) == /\\ k \\notin seen[n] /\\ Len(log[n]) < 2
              /\\ net' = net (+) SetToBag({[to |-> n, k |-> k]})
              /\\ log' = [log EXCEPT ![n] = Append(@, k)]
              /\\ UNCHANGED <<seen, faults>>
Deliver(m) == /\\ BagIn(m, net) /\\ net' = net (-) SetToBag({m})
              /\\ seen' = [seen EXCEPT ![m.to] = @ \\cup {m.k}]
              /\\ UNCHANGED <<log, faults>>
Lose(m) == /\\ faults < Faults /\\ BagIn(m, net) /\\ net' = net (-) SetToBag({m}) /\\ faults' = faults + 1
           /\\ UNCHANGED <<seen, log>>
Next == \\/ \\E n \\in Nodes, k \\in 1..2 : Send(n, k)
        \\/ \\E m \\in DOMAIN net : Deliver(m) \\/ Lose(m)
SeenOk == \\A n \\in Nodes : seen[n] \\subseteq 1..2`;

test('messages in a bag: element reads, membership, EXCEPT paths, set and bag changes', () => {
  const r = same('BagNet', bag, 'CONSTANTS Faults = 1\nINIT Init\nNEXT Next\nINVARIANT SeenOk');
  assert.equal(r.status, 'ok');
  assert.ok(r.distinct > 100);
});

test('a variable holding a value that is not interned (an interval) keeps today\'s path', () => {
  const r = same(
    'Interval',
    `EXTENDS Integers
VARIABLES r, x
Init == r = 1..2 /\\ x = 0
Grow == x < 3 /\\ r' = 1..(x + 2) /\\ x' = x + 1
Same == x < 3 /\\ r' = r /\\ x' = x + 1
Shrink == x > 0 /\\ r' = {1} /\\ x' = x - 1
Next == Grow \\/ Same \\/ Shrink`,
    'INIT Init\nNEXT Next',
  );
  assert.equal(r.status, 'ok');
});

test('records, functions keyed by tuples, and sets of sets', () => {
  const r = same(
    'Shapes',
    `EXTENDS Integers
VARIABLES f, g, s
Init == f = [k \\in {<<1, 2>>, <<2, 1>>} |-> 0] /\\ g = [a |-> {}, b |-> {}] /\\ s = {}
Inc(k) == f[k] < 2 /\\ f' = [f EXCEPT ![k] = @ + 1] /\\ g' = [g EXCEPT !.a = @ \\cup {f[k]}] /\\ s' = s \\cup {g.a}
Swap == g' = [a |-> g.b, b |-> g.a] /\\ UNCHANGED <<f, s>>
Next == (\\E k \\in DOMAIN f : Inc(k)) \\/ Swap`,
    'INIT Init\nNEXT Next',
  );
  assert.equal(r.status, 'ok');
});

test('one worker and four agree on the bag model', () => {
  const one = check('BagNet', {});
  const four = check('BagNet', {}, ['-workers', '4']);
  assert.equal(one, four);
});
