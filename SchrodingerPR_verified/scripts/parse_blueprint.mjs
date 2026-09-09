import fs from "node:fs";

const source = fs.readFileSync(new URL("../paper_blueprint.tex", import.meta.url), "utf8");

const chapterRe = /^\\chapter\{(.*)\}\\label\{([^}]*)\}/gm;
const chapters = [];
for (const match of source.matchAll(chapterRe)) {
  chapters.push({ title: match[1], label: match[2], index: match.index });
}

const moduleByChapter = new Map([
  ["chap:setup", ["Setup.lean", -1]],
  ["chap:mixed-norms", ["ScalarMixedNorms.lean", 0]],
  ["chap:fourier", ["FourierSobolev.lean", 1]],
  ["chap:free-group", ["FreeSchrodinger.lean", 2]],
  ["chap:frac-int", ["FractionalIntegration.lean", 3]],
  ["chap:utilities", ["Utilities.lean", 12]],
  ["chap:strichartz", ["Strichartz1D.lean", 4]],
  ["chap:wellposed", ["CubicFlow.lean", 5]],
  ["chap:endpoint", ["EndpointRegularity.lean", 6]],
  ["chap:smoothing", ["LocalSmoothing1D.lean", 7]],
  ["chap:critical-calculus", ["CriticalQuadraticForms.lean", 8]],
  ["chap:current", ["DensityCurrent.lean", 9]],
  ["chap:wronskian-exterior", ["WronskianExterior.lean", 10]],
  ["chap:traces", ["DiagonalTrace.lean", 11]],
  ["chap:carleman", ["Carleman2D.lean", 13]],
  ["chap:halfspace", ["HalfspacePropagation.lean", 14]],
  ["chap:completion", ["PhaseRetrieval.lean", 15]],
]);

const kindPattern = "definition|convention|lemma|proposition|theorem|corollary";
const declarationRe = new RegExp(
  `\\\\begin\\{(${kindPattern})\\}(?:\\[([^\\]]*)\\])?([\\s\\S]*?)\\\\end\\{\\1\\}`,
  "g",
);

const rawDeclarations = [];
for (const match of source.matchAll(declarationRe)) {
  const body = match[3];
  const label = body.match(/\\label\{([^}]*)\}/)?.[1];
  if (!label) throw new Error(`Declaration at byte ${match.index} has no label`);
  const chapter = chapters.filter((item) => item.index < match.index).at(-1);
  if (!chapter || !moduleByChapter.has(chapter.label)) {
    throw new Error(`No module mapping for ${label} in ${chapter?.label ?? "no chapter"}`);
  }
  const statementUses = [...body.matchAll(/\\uses\{([^}]*)\}/g)]
    .flatMap((item) => item[1].split(","))
    .map((item) => item.trim())
    .filter(Boolean);
  rawDeclarations.push({
    label,
    kind: match[1],
    title: match[2] ?? "",
    start: match.index,
    end: match.index + match[0].length,
    chapter: chapter.label,
    statementUses,
  });
}

const declarations = rawDeclarations.map((declaration, index) => {
  const nextStart = rawDeclarations[index + 1]?.start ?? source.length;
  const tail = source.slice(declaration.end, nextStart);
  const proof = tail.match(/\\begin\{proof\}([\s\S]*?)\\end\{proof\}/)?.[1] ?? "";
  const proofUses = [...proof.matchAll(/\\uses\{([^}]*)\}/g)]
    .flatMap((item) => item[1].split(","))
    .map((item) => item.trim())
    .filter(Boolean);
  const pointer = proof.match(/% FULL PROOF:\s*([^\n\r]*)/)?.[1].trim() ?? "—";
  return { ...declaration, proofUses, pointer };
});

const byLabel = new Map(declarations.map((item) => [item.label, item]));
const missing = [];
for (const item of declarations) {
  for (const dependency of new Set([...item.statementUses, ...item.proofUses])) {
    if (!byLabel.has(dependency)) missing.push([item.label, dependency]);
  }
}

const incoming = new Map(declarations.map((item) => [item.label, 0]));
const outgoing = new Map(declarations.map((item) => [item.label, []]));
let edgeCount = 0;
for (const item of declarations) {
  const dependencies = new Set([...item.statementUses, ...item.proofUses].filter((x) => byLabel.has(x)));
  incoming.set(item.label, dependencies.size);
  edgeCount += dependencies.size;
  for (const dependency of dependencies) outgoing.get(dependency).push(item.label);
}

const sourceOrder = new Map(declarations.map((item, index) => [item.label, index]));
const ready = declarations.filter((item) => incoming.get(item.label) === 0).map((item) => item.label);
const topo = [];
while (ready.length > 0) {
  ready.sort((a, b) => sourceOrder.get(a) - sourceOrder.get(b));
  const label = ready.shift();
  topo.push(byLabel.get(label));
  for (const dependent of outgoing.get(label)) {
    incoming.set(dependent, incoming.get(dependent) - 1);
    if (incoming.get(dependent) === 0) ready.push(dependent);
  }
}
const cyclic = declarations.filter((item) => incoming.get(item.label) > 0);

const buildOrder = [
  "chap:setup",
  "chap:mixed-norms",
  "chap:fourier",
  "chap:free-group",
  "chap:frac-int",
  "chap:utilities",
  "chap:strichartz",
  "chap:wellposed",
  "chap:endpoint",
  "chap:smoothing",
  "chap:critical-calculus",
  "chap:current",
  "chap:wronskian-exterior",
  "chap:traces",
  "chap:carleman",
  "chap:halfspace",
  "chap:completion",
];

const buildRank = new Map(buildOrder.map((chapter, index) => [chapter, index]));
const moduleOrderViolations = [];
for (const item of declarations) {
  for (const dependency of new Set([...item.statementUses, ...item.proofUses])) {
    const predecessor = byLabel.get(dependency);
    if (predecessor && buildRank.get(predecessor.chapter) > buildRank.get(item.chapter)) {
      moduleOrderViolations.push([item, predecessor]);
    }
  }
}

const formatUses = (uses) => uses.length === 0 ? "—" : uses.map((x) => `\`${x}\``).join(", ");

console.log("# Blueprint build order\n");
console.log("Generated mechanically from `paper_blueprint.tex`. Statement and proof `\\uses` are kept separate.");
console.log(`\n- Numbered declarations: **${declarations.length}**`);
console.log(`- Dependency edges: **${edgeCount}**`);
console.log(`- Missing dependency labels: **${missing.length}**`);
console.log(`- Topologically emitted declarations: **${topo.length}**`);
console.log(`- Cyclic declarations: **${cyclic.length}**`);
console.log(`- Appendix module-order violations: **${moduleOrderViolations.length}**`);
console.log(`- DAG verdict: **${cyclic.length === 0 && missing.length === 0 ? "acyclic and closed" : "requires attention"}**`);

if (missing.length > 0) {
  console.log("\n## Missing labels\n");
  for (const [from, to] of missing) console.log(`- \`${from}\` → \`${to}\``);
}
if (cyclic.length > 0) {
  console.log("\n## Cycle residue\n");
  for (const item of cyclic) console.log(`- \`${item.label}\``);
}
if (moduleOrderViolations.length > 0) {
  console.log("\n## Appendix module-order exceptions\n");
  console.log("The declaration DAG remains acyclic, but these source-level `\\uses` edges point from an earlier appendix module to a later one. The implementation must make the utility generic, relocate it, or refine imports without introducing a cycle.\n");
  for (const [item, predecessor] of moduleOrderViolations) {
    console.log(`- \`${item.label}\` (${moduleByChapter.get(item.chapter)[0]}) uses \`${predecessor.label}\` (${moduleByChapter.get(predecessor.chapter)[0]}).`);
  }
}

console.log("\n## Leaves-first order grouped by Lean module\n");
for (const chapter of buildOrder) {
  const [file, number] = moduleByChapter.get(chapter);
  const chapterTitle = chapters.find((item) => item.label === chapter)?.title ?? chapter;
  const members = topo.filter((item) => item.chapter === chapter);
  console.log(`### ${number < 0 ? "Setup" : `Module ${number}`} — \`Lean_Code/${file}\``);
  console.log(`\nBlueprint chapter: \`${chapter}\` (${chapterTitle}). Declarations: ${members.length}.\n`);
  console.log("| # | Kind | Label | Statement uses | Proof uses | Full proof pointer |");
  console.log("|---:|---|---|---|---|---|");
  members.forEach((item, index) => {
    console.log(`| ${index + 1} | ${item.kind} | \`${item.label}\` | ${formatUses(item.statementUses)} | ${formatUses(item.proofUses)} | ${item.pointer} |`);
  });
  console.log("");
}
