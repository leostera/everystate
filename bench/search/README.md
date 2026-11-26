# Search benchmarks (RFD0001)

Raw results of `scripts/bench-search.ts` (schemaVersion 1: provenance of the harness, machine, builds
with their sha256 and commit, configuration, and every run). The `.md` tables and `.svg` charts are
generated from them; do not edit those by hand.

| file | what |
|---|---|
| `large5.json` | the five larger Feynman oracle models, 1 and 8 workers, 5 rounds: 28fd7c5, afa9e05 (interning), db119b1 (id cache), e1cf1ce (final) |
| `bench12.json` | the 12 models of BENCHMARK.md, 1 and 8 workers, 3 rounds: 28fd7c5 and e1cf1ce |
| `step12-early.json` | the first measurement after steps 1 and 2 (3 rounds), as reported then |
| `corpus125/*.json` | `scripts/feynman-bench.ts --json` on the 125 Feynman configurations (CPU ms, median of 5) |

Reproduce (binaries built from the named commits; `FEYNMAN_CFG` is `scripts/feynman-bench.ts --out DIR`'s
`DIR/cfg`, `EXAMPLES` a tlaplus/Examples checkout):

```sh
FEYNMAN_CFG=... bun scripts/bench-search.ts --out bench/search/large5.json --runs 5 --sets large5 --workers 1,8 \
  base=BIN@28fd7c5 hashcons=BIN@afa9e05 idcache=BIN@db119b1 parallel=BIN@e1cf1ce
EXAMPLES=... bun scripts/bench-search.ts --out bench/search/bench12.json --runs 3 --sets bench12 --workers 1,8 \
  base=BIN@28fd7c5 final=BIN@e1cf1ce
FEYNMAN=... EVERYSTATE=BIN bun scripts/feynman-bench.ts --runs 5 --json bench/search/corpus125/NAME.json
bun scripts/plot-bench.ts --base base --md bench/search/large5.md --svg bench/search/large5 bench/search/large5.json
bun scripts/plot-bench.ts --base base --md bench/search/bench12.md --svg bench/search/bench12 bench/search/bench12.json
```
