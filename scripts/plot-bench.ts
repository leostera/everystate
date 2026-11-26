#!/usr/bin/env bun
// Tables and charts from the results of scripts/bench-search.ts: per model and worker count, the median
// wall and CPU seconds and peak RSS of every build, with each build's ratio to the baseline next to the
// absolute numbers. Nothing here is measured; it only reads the results files.
//
//   bun scripts/plot-bench.ts --base LABEL [--md OUT.md] [--svg PREFIX] RESULTS.json [RESULTS.json ...]
//
//   --base LABEL  the build the others are compared with (ratio = baseline time / build time: above 1 is
//                 faster than the baseline)
//   --md OUT.md   write the tables there (default: stdout)
//   --svg PREFIX  write one bar chart of median wall seconds per worker count: PREFIX-w<N>.svg
//
// Several results files may be given (e.g. one per model set); their runs are pooled by (set, model,
// build, workers). A run that disagrees with the others on its model fails the whole report.
import { readFileSync, writeFileSync } from "node:fs";
import { parseArgs } from "node:util";

type Run = { set: string; model: string; build: string; workers: number; wallS: number; cpuS: number; rssMb: number; status: string | null; distinct: number | null; generated: number | null; depth: number | null };
type Results = { schemaVersion: number; generatedAt: string; machine: Record<string, unknown>; harness: { commit: string | null; dirty: boolean }; builds: { label: string; commit: string | null; sha256: string }[]; runs: Run[] };

const { values, positionals } = parseArgs({ allowPositionals: true, options: { base: { type: "string" }, md: { type: "string" }, svg: { type: "string" } } });
if (!values.base || positionals.length === 0) throw new Error("usage: plot-bench.ts --base LABEL [--md OUT.md] [--svg PREFIX] RESULTS.json...");
const files = positionals.map((p) => ({ path: p, r: JSON.parse(readFileSync(p, "utf8")) as Results }));
for (const f of files) if (f.r.schemaVersion !== 1) throw new Error(`${f.path}: schemaVersion ${f.r.schemaVersion}, expected 1`);

const runs = files.flatMap((f) => f.r.runs);
const builds = [...new Set(files.flatMap((f) => f.r.builds.map((b) => b.label)))];
if (!builds.includes(values.base)) throw new Error(`no build labelled ${values.base}`);
const ordered = [values.base, ...builds.filter((b) => b !== values.base)];
const models = [...new Map(runs.map((r) => [`${r.set}/${r.model}`, { set: r.set, model: r.model }])).values()];
const workers = [...new Set(runs.map((r) => r.workers))].sort((a, b) => a - b);

const median = (xs: number[]) => {
  const s = [...xs].sort((a, b) => a - b);
  const m = s.length >> 1;
  return s.length % 2 ? s[m] : (s[m - 1] + s[m]) / 2;
};
const pick = (set: string, model: string, build: string, w: number) => runs.filter((r) => r.set === set && r.model === model && r.build === build && r.workers === w);
type Cell = { wall: number; cpu: number; rss: number; n: number } | null;
const cell = (set: string, model: string, build: string, w: number): Cell => {
  const rs = pick(set, model, build, w);
  return rs.length ? { wall: median(rs.map((r) => r.wallS)), cpu: median(rs.map((r) => r.cpuS)), rss: median(rs.map((r) => r.rssMb)), n: rs.length } : null;
};

// every run of a model must report the same result
for (const { set, model } of models) {
  const key = (r: Run) => `${r.status}/${r.distinct}/${r.generated}/${r.depth}`;
  const keys = new Set(runs.filter((r) => r.set === set && r.model === model).map(key));
  if (keys.size !== 1) throw new Error(`${set}/${model}: runs disagree: ${[...keys].join(" vs ")}`);
}

const f2 = (x: number) => x.toFixed(x < 1 ? 3 : 2);
const ratio = (b: number, x: number) => `${(b / x).toFixed(2)}x`;
const lines: string[] = [];
const prov = files.map((f) => `- \`${f.path}\`: ${f.r.generatedAt}, harness ${f.r.harness.commit?.slice(0, 7) ?? "?"}${f.r.harness.dirty ? "+dirty" : ""}; builds ${f.r.builds.map((b) => `${b.label}=${b.commit ?? "?"}`).join(", ")}`);
lines.push(`Medians of ${[...new Set(models.map(({ set, model }) => cell(set, model, values.base!, workers[0])?.n ?? 0))].join("/")} runs per cell. Ratio = ${values.base} / build (above 1: faster than ${values.base}).`, "", ...prov, "");
for (const w of workers) {
  lines.push(`### ${w} worker${w === 1 ? "" : "s"}`, "");
  const head = ["model", "distinct", ...ordered.flatMap((b) => (b === values.base ? [`${b} wall s`, `${b} CPU s`, `${b} RSS MB`] : [`${b} wall s`, "wall ratio", `${b} CPU s`, "CPU ratio", `${b} RSS MB`]))];
  lines.push(`| ${head.join(" | ")} |`, `|${head.map((_, i) => (i === 0 ? "---" : "---:")).join("|")}|`);
  const total: Record<string, { wall: number; cpu: number }> = {};
  for (const { set, model } of models) {
    const base = cell(set, model, values.base, w);
    if (!base) continue;
    const distinct = runs.find((r) => r.set === set && r.model === model)?.distinct ?? 0;
    const row = [model, distinct.toLocaleString("en-US")];
    for (const b of ordered) {
      const c = cell(set, model, b, w);
      total[b] ??= { wall: 0, cpu: 0 };
      if (!c) {
        row.push(...(b === values.base ? ["", "", ""] : ["", "", "", "", ""]));
        continue;
      }
      total[b].wall += c.wall;
      total[b].cpu += c.cpu;
      if (b === values.base) row.push(f2(c.wall), f2(c.cpu), String(c.rss));
      else row.push(f2(c.wall), ratio(base.wall, c.wall), f2(c.cpu), ratio(base.cpu, c.cpu), String(c.rss));
    }
    lines.push(`| ${row.join(" | ")} |`);
  }
  const t = total[values.base];
  const row = ["**total**", ""];
  for (const b of ordered) {
    const x = total[b];
    if (b === values.base) row.push(f2(x.wall), f2(x.cpu), "");
    else row.push(f2(x.wall), ratio(t.wall, x.wall), f2(x.cpu), ratio(t.cpu, x.cpu), "");
  }
  lines.push(`| ${row.join(" | ")} |`, "");
}
const md = lines.join("\n");
if (values.md) writeFileSync(values.md, md + "\n");
else console.log(md);

// bar charts: per model, one bar per build, median wall seconds, the value printed on each bar
if (values.svg) {
  const palette = ["#8c8c8c", "#4e79a7", "#f28e2b", "#59a14f", "#e15759", "#76b7b2"];
  for (const w of workers) {
    const rows = models.map(({ set, model }) => ({ model, cells: ordered.map((b) => cell(set, model, b, w)) })).filter((r) => r.cells[0]);
    const max = Math.max(...rows.flatMap((r) => r.cells.map((c) => c?.wall ?? 0)));
    const barH = 14, gap = 10, left = 170, width = 460, top = 40;
    const groupH = ordered.length * barH + gap;
    const height = top + rows.length * groupH + 30;
    const esc = (s: string) => s.replace(/&/g, "&amp;").replace(/</g, "&lt;");
    const out: string[] = [`<svg xmlns="http://www.w3.org/2000/svg" width="${left + width + 90}" height="${height}" font-family="system-ui, sans-serif" font-size="11">`];
    out.push(`<text x="10" y="18" font-size="13" font-weight="600">Median wall seconds, ${w} worker${w === 1 ? "" : "s"} (lower is better)</text>`);
    ordered.forEach((b, i) => out.push(`<rect x="${10 + i * 120}" y="26" width="10" height="10" fill="${palette[i % palette.length]}"/><text x="${24 + i * 120}" y="35">${esc(b)}</text>`));
    rows.forEach((r, gi) => {
      const y0 = top + gi * groupH;
      out.push(`<text x="${left - 6}" y="${y0 + (ordered.length * barH) / 2 + 4}" text-anchor="end">${esc(r.model)}</text>`);
      r.cells.forEach((c, i) => {
        if (!c) return;
        const len = Math.max(1, (c.wall / max) * width);
        const y = y0 + i * barH;
        const base = r.cells[0]!.wall;
        const label = i === 0 ? `${f2(c.wall)} s` : `${f2(c.wall)} s (${ratio(base, c.wall)})`;
        out.push(`<rect x="${left}" y="${y}" width="${len.toFixed(1)}" height="${barH - 2}" fill="${palette[i % palette.length]}"/>`);
        out.push(`<text x="${left + len + 4}" y="${y + barH - 4}">${label}</text>`);
      });
    });
    out.push(`</svg>`);
    writeFileSync(`${values.svg}-w${w}.svg`, out.join("\n") + "\n");
  }
}
