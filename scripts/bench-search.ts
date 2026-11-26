#!/usr/bin/env bun
// Whole-process benchmark of everystate builds on fixed model sets: wall and CPU seconds and peak RSS of
// every run, the builds and worker counts interleaved round by round so that drift of the machine affects
// them alike. Every run is checked against the others for the same model: status, distinct, generated and
// depth must agree, or the run is reported as a disagreement (exit status 1).
//
//   bun scripts/bench-search.ts --out FILE.json [--runs 5] [--sets large5,large11,bench12] [--workers 1,8]
//       [--only NAME[,NAME]] [--note TEXT] LABEL=BINARY[@COMMIT] [LABEL=BINARY[@COMMIT] ...]
//
//   LABEL      the name of the build in the results (e.g. `base`, `interned`)
//   BINARY     path of the everystate binary
//   COMMIT     the commit it was built from, recorded as provenance (`+dirty` if the tree was dirty)
//   --env K=V  set for every run (repeatable); EVERYSTATE_* variables of this process are not passed on
//
//   Model sets: large5 and large11 are the Feynman oracle configurations written by
//   `scripts/feynman-bench.ts --out DIR` (FEYNMAN_CFG=DIR/cfg); bench12 the 12 models of BENCHMARK.md in
//   tlaplus/Examples (EXAMPLES).
//
// The results file is rewritten after every run (schemaVersion 1): provenance, configuration and the raw
// runs. Tables and charts are made from it by scripts/plot-bench.ts.
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, readFileSync, renameSync, writeFileSync } from "node:fs";
import { arch, cpus, loadavg, platform, release, totalmem } from "node:os";
import { basename, join, resolve } from "node:path";
import { parseArgs } from "node:util";

type Build = { label: string; binary: string; commit: string | null; sha256: string };
type Model = { set: string; name: string; cwd: string; argv: string[] };
type Run = {
  round: number;
  set: string;
  model: string;
  build: string;
  workers: number;
  wallS: number;
  cpuS: number;
  rssMb: number;
  status: string | null;
  distinct: number | null;
  generated: number | null;
  depth: number | null;
  load1: number;
  at: string;
};

const { values, positionals } = parseArgs({
  allowPositionals: true,
  options: {
    out: { type: "string" },
    runs: { type: "string", default: "5" },
    sets: { type: "string", default: "large5" },
    workers: { type: "string", default: "1" },
    only: { type: "string" },
    note: { type: "string", default: "" },
    env: { type: "string", multiple: true, default: [] },
  },
});
if (!values.out) throw new Error("--out FILE.json is required");
const out = resolve(values.out);
const runs = Number(values.runs);
const workerCounts = values.workers!.split(",").map(Number);
const sets = values.sets!.split(",");
const only = values.only ? new Set(values.only.split(",")) : null;
const here = resolve(import.meta.dir, "..");

function parseBuild(arg: string): Build {
  const eq = arg.indexOf("=");
  if (eq < 1) throw new Error(`expected LABEL=BINARY[@COMMIT], got ${arg}`);
  const label = arg.slice(0, eq);
  const [bin, commit] = arg.slice(eq + 1).split("@");
  const binary = resolve(bin);
  if (!existsSync(binary)) throw new Error(`no binary at ${binary}`);
  const sha256 = createHash("sha256").update(readFileSync(binary)).digest("hex");
  return { label, binary, commit: commit ?? null, sha256 };
}
const builds = positionals.map(parseBuild);
if (builds.length === 0) throw new Error("no builds given");

function models(): Model[] {
  const cfg = process.env.FEYNMAN_CFG ?? "";
  const ex = process.env.EXAMPLES ?? "";
  const ms: Model[] = [];
  const feynman = (set: string, name: string) => {
    const mod = name.split("-")[0];
    ms.push({ set, name, cwd: join(cfg, set === "large5" ? "large" : "", name), argv: ["-deadlock", "-json", "-config", `${mod}.cfg`, `${mod}.tla`] });
  };
  if (sets.includes("large5")) for (const n of ["OrSet-fixed-f1", "OrSet-fixed-f4", "ReadRepair-fixed-f6", "LostUpdate-fixed-f6", "LeaseLock-fixed-f5"]) feynman("large5", n);
  if (sets.includes("large11"))
    for (const n of ["LeaseLock-fixed-f1", "LeaseLock-buggy-f1", "OrSet-fixed-f0", "OrSet-fixed-f1", "OrSet-buggy-f1", "ReadRepair-fixed-f0", "ReadRepair-fixed-f1", "ReadRepair-buggy-f0", "ReadRepair-buggy-f1", "LostUpdate-fixed-f1", "LostUpdate-buggy-f1"]) feynman("large11", n);
  if (sets.includes("bench12")) {
    const src = readFileSync(join(here, "scripts/bench.mjs"), "utf8");
    for (const [, c, s] of src.matchAll(/\['(specifications\/[^']+\.cfg)', '(specifications\/[^']+\.tla)'/g)) ms.push({ set: "bench12", name: basename(c, ".cfg"), cwd: ex, argv: ["-json", "-config", c, s] });
  }
  for (const m of ms) if (!existsSync(m.cwd)) throw new Error(`model directory missing: ${m.cwd} (set FEYNMAN_CFG / EXAMPLES)`);
  return only ? ms.filter((m) => only.has(m.name)) : ms;
}

function git(args: string[]): string | null {
  try {
    return execFileSync("git", args, { cwd: here, encoding: "utf8" }).trim();
  } catch {
    return null;
  }
}
function machine() {
  const sysctl = (k: string) => {
    try {
      return execFileSync("sysctl", ["-n", k], { encoding: "utf8" }).trim();
    } catch {
      return null;
    }
  };
  return {
    platform: platform(),
    release: release(),
    arch: arch(),
    cpu: cpus()[0]?.model ?? null,
    logicalCpus: cpus().length,
    performanceCores: sysctl("hw.perflevel0.physicalcpu"),
    efficiencyCores: sysctl("hw.perflevel1.physicalcpu"),
    memoryGb: Math.round(totalmem() / 2 ** 30),
  };
}

const env: Record<string, string> = {};
for (const [k, v] of Object.entries(process.env)) if (v !== undefined && !k.startsWith("EVERYSTATE_")) env[k] = v;
for (const kv of values.env!) {
  const i = kv.indexOf("=");
  env[kv.slice(0, i)] = kv.slice(i + 1);
}

const ms = models();
const doc = {
  schemaVersion: 1,
  generatedAt: new Date().toISOString(),
  harness: { script: "scripts/bench-search.ts", commit: git(["rev-parse", "HEAD"]), dirty: (git(["status", "--porcelain"]) ?? "") !== "" },
  machine: machine(),
  config: { runs, sets, workers: workerCounts, only: values.only ?? null, env: values.env, models: ms.map((m) => ({ set: m.set, name: m.name, argv: m.argv })) },
  builds,
  notes:
    (values.note ? values.note + " " : "") +
    "Whole process (start-up, parsing, search), one process at a time. wallS from spawn to exit; cpuS is user+system of the child (getrusage); rssMb the peak resident set. Builds and worker counts alternate within each round.",
  runs: [] as Run[],
};
function save() {
  writeFileSync(out + ".tmp", JSON.stringify(doc, null, 1));
  renameSync(out + ".tmp", out);
}

function runMeasured(b: Build, m: Model, workers: number, round: number): Run {
  const argv = workers > 1 ? ["-workers", String(workers), ...m.argv] : m.argv;
  const t0 = performance.now();
  const p = Bun.spawnSync({ cmd: [b.binary, ...argv], cwd: m.cwd, env, stdout: "pipe", stderr: "pipe" });
  const wallS = (performance.now() - t0) / 1000;
  const ru: any = p.resourceUsage;
  let j: any = {};
  try {
    j = JSON.parse(p.stdout.toString().trim().split("\n").at(-1)!);
  } catch {}
  return {
    round,
    set: m.set,
    model: m.name,
    build: b.label,
    workers,
    wallS: +wallS.toFixed(4),
    cpuS: +(Number(ru?.cpuTime?.total ?? NaN) / 1e6).toFixed(4),
    rssMb: Math.round(Number(ru?.maxRSS ?? NaN) / 2 ** 20),
    status: j.status ?? null,
    distinct: j.distinct ?? null,
    generated: j.generated ?? null,
    depth: j.depth ?? null,
    load1: +loadavg()[0].toFixed(2),
    at: new Date().toISOString(),
  };
}

const key = (r: { set: string; model: string }) => `${r.set}/${r.model}`;
const reference = new Map<string, Run>();
let disagreements = 0;
const total = runs * ms.length * builds.length * workerCounts.length;
let n = 0;
console.log(`${ms.length} models x ${builds.length} builds x workers ${workerCounts.join(",")} x ${runs} rounds = ${total} runs; out ${out}`);
for (let round = 0; round < runs; round++) {
  for (const m of ms) {
    for (const workers of workerCounts) {
      for (const b of builds) {
        const r = runMeasured(b, m, workers, round);
        doc.runs.push(r);
        save();
        n++;
        const ref = reference.get(key(r));
        let agree = "";
        if (!ref) reference.set(key(r), r);
        else if (ref.status !== r.status || ref.distinct !== r.distinct || ref.generated !== r.generated || ref.depth !== r.depth) {
          disagreements++;
          agree = `  DISAGREES with ${ref.build}/w${ref.workers}: ${ref.status} ${ref.distinct}/${ref.generated}/${ref.depth}`;
        }
        console.log(`[${String(n).padStart(4)}/${total}] r${round} ${m.name.padEnd(22)} ${b.label.padEnd(12)} w${String(workers).padEnd(2)} wall ${r.wallS.toFixed(2).padStart(6)} cpu ${r.cpuS.toFixed(2).padStart(6)} rss ${String(r.rssMb).padStart(5)} MB  ${r.status} ${r.distinct}/${r.generated}/${r.depth}  load ${r.load1}${agree}`);
      }
    }
  }
}
console.log(disagreements ? `${disagreements} disagreeing runs` : "all runs agree");
process.exit(disagreements ? 1 : 0);
