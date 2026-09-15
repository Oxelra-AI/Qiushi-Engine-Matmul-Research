import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const paper = fileURLToPath(new URL('../', import.meta.url));
const read = name => fs.readFileSync(path.join(paper, name), 'utf8');
const catalogue = JSON.parse(read('data/frozen-catalogue.json'));
const results = {};

function span(basis) {
  let values = [0];
  for (const a of basis) values = [...new Set([...values, ...values.map(b => a ^ b)])];
  return values.sort((a, b) => a - b);
}
function rank(a) {
  return Math.log2(span([a & 7, (a >> 3) & 7, (a >> 6) & 7]).length);
}
function transpose(a) {
  let b = 0;
  for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++)
    b |= ((a >> (3 * i + j)) & 1) << (3 * j + i);
  return b;
}
function multiply(a, b) {
  let c = 0;
  for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) {
    let bit = 0;
    for (let k = 0; k < 3; k++) bit ^= ((a >> (3 * i + k)) & 1) & ((b >> (3 * k + j)) & 1);
    c |= bit << (3 * i + j);
  }
  return c;
}
const ranks = Array.from({ length: 512 }, (_, a) => rank(a));
const gl = ranks.flatMap((r, a) => r === 3 ? [a] : []);
assert.equal(gl.length, 168);
const multiplication = Array.from({ length: 512 }, (_, a) =>
  Uint16Array.from({ length: 512 }, (_, b) => multiply(a, b)));
const action = (a, p, q) => multiplication[multiplication[p][a]][q];
const planeKey = (a, b) => [a, b, a ^ b].sort((u, v) => u - v).join(',');

for (const { index, basis, lower_bound } of catalogue) {
  assert.equal(span(basis).length, 2 ** basis.length, `dependent basis ${index}`);
  assert(Number.isInteger(lower_bound) && lower_bound >= 0);
}
const printed = new Map([...read('data/frozen-catalogue.tex').matchAll(/(\d+) & \$\(([^)]*)\)\$ & (\d+)/g)]
  .map(m => [Number(m[1]), { basis: m[2] ? m[2].split(',').map(Number) : [], lower_bound: Number(m[3]) }]));
assert.equal(printed.size, 496);
for (const { index, basis, lower_bound } of catalogue)
  assert.deepEqual(printed.get(index), { basis, lower_bound });
results.catalogue_entries = 496;

const sourceExamples = JSON.parse(read('data/source-examples.json'));
function parity(x) {
  let p = 0;
  for (; x; x >>= 1) p ^= x & 1;
  return p;
}
const dot = (a, b) => parity(a & b);
const kernel = functionals => Array.from({ length: 512 }, (_, x) => x)
  .filter(x => functionals.every(l => dot(l, x) === 0));
for (const example of Object.values(sourceExamples)) {
  assert.deepEqual(kernel(example.annihilator_codes), span(catalogue[example.catalogue_index].basis));
  assert.equal(catalogue[example.catalogue_index].lower_bound, example.result);
}
const cc = sourceExamples.contraction_cover;
const [f, g] = cc.annihilator_codes;
const threeFunctionals = [f, g, f ^ g];
assert.deepEqual(threeFunctionals.map(l => 3 * ranks[l]), cc.hyperplane_bounds);
for (let x = 0; x < 512; x++) assert(threeFunctionals.some(l => dot(l, x) === 0));
assert.equal(cc.hyperplane_bounds.reduce((a, b) => a + b, 0) / 2, cc.result);
results.three_hyperplane_source_bound = cc.result;

const sub = sourceExamples.substitution;
const slice = (b, c, component) => b % 3 === c % 3
  ? (sub.annihilator_codes[component] >> (3 * Math.floor(c / 3) + Math.floor(b / 3))) & 1
  : 0;
// Check the two hypotheses of the substitution lemma on the displayed coordinates.
for (let z = 1; z < 64; z++) {
  assert(Array.from({ length: 9 }, (_, c) => c).some(c => [0, 1].some(q =>
    sub.selected_rows.reduce((v, b, l) => v ^ (((z >> l) & 1) * slice(b, c, q)), 0) !== 0)));
}
for (let y = 1; y < 64; y++) {
  const evaluation = (b, q) => sub.selected_columns.reduce((v, c, j) =>
    v ^ (((y >> j) & 1) * slice(b, c, q)), 0);
  assert([0, 1].some(q => sub.selected_rows.every(b => evaluation(b, q) === 0)
    && Array.from({ length: 9 }, (_, b) => b).some(b => evaluation(b, q) !== 0)));
}
assert.equal(sub.selected_rows.length + sub.selected_columns.length, sub.result);
results.substitution_independence_cases = 63;
results.substitution_survival_cases = 63;

const cover = sourceExamples.weighted_cover;
assert.equal(cover.source_equations.length, cover.weights.length);
assert.equal(cover.source_bounds.length, cover.weights.length);
let minCoverage = Infinity;
for (let x = 0; x < 64; x++) {
  const weight = cover.source_equations.reduce((s, equations, i) =>
    s + (equations.every(e => dot(e, x) === 0) ? cover.weights[i] : 0), 0);
  minCoverage = Math.min(minCoverage, weight);
}
assert.equal(minCoverage, cover.coverage);
const totalWeight = cover.weights.reduce((s, w) => s + w, 0);
const weightedBounds = cover.weights.reduce((s, w, i) => s + w * cover.source_bounds[i], 0);
assert.equal(totalWeight, 32);
assert.equal(weightedBounds, 480);
assert.equal(Math.ceil(weightedBounds / (totalWeight - cover.coverage)), cover.result);
for (let i = 10; i < cover.source_equations.length; i++) {
  const mask = cover.source_equations[i][0];
  const l = cover.annihilator_codes.reduce((v, a, j) => v ^ (((mask >> j) & 1) ? a : 0), 0);
  assert.equal(3 * ranks[l], cover.source_bounds[i]);
}
results.weighted_source_cover_classes = 64;
results.weighted_source_bound = cover.result;

const continuation = JSON.parse(read('data/continuation-sample.json'));
const sources = JSON.parse(read('data/artifact-sources.json'));
assert.equal(continuation.revision, sources.research_archive.revision);
assert(/^[a-f0-9]{40}$/.test(sources.formalization.revision));
const formalizationRelease = `${sources.formalization.repository}/releases/tag/${sources.formalization.release_tag}`;
assert.equal(sources.formalization.release_url, formalizationRelease);
const formalizationCitation = read('references.bib').match(/@misc\{qiushi-lean,[\s\S]*?\n\}/)?.[0];
assert(formalizationCitation?.includes(`\\href{${formalizationRelease}}{`), 'formalization citation and release differ');
const formalizationRecord = JSON.parse(read(sources.formalization.manuscript_verification_record));
assert.equal(sources.formalization.registered_source_digest, formalizationRecord.source_build.source_digest);
assert.equal(sources.formalization.toolchain, formalizationRecord.toolchain);
assert.equal(sources.formalization.mathlib_revision, formalizationRecord.mathlib_revision);
const development = read('sections/development.tex');
const close = (a, b) => assert(Math.abs(a - b) <= 1e-12 * Math.max(1, Math.abs(b)));
function scientificTex(x) {
  const [coefficient, exponent] = x.toExponential(3).split('e');
  const power = Number(exponent);
  return `${coefficient}\\times10${power >= 0 && power <= 9 ? `^${power}` : `^{${power}}`}`;
}
for (const row of continuation.samples) {
  const outputNorm = row.pairing_norm * row.absorbed_output_norm;
  close(outputNorm, row.unit_pairing_output_norm);
  const error = row.sigma_min * outputNorm / Math.abs(row.lambda_k);
  close(error, row.deletion_error);
  assert(Number.isFinite(row.target_residual) && row.target_residual > 0 && row.target_residual < 4e-12);
  const printedRow = `${row.t} & $${scientificTex(row.sigma_min)}$ & $${Math.abs(row.lambda_k).toFixed(4)}$ & $${scientificTex(outputNorm)}$ & $${error.toFixed(3)}$ & $${scientificTex(row.target_residual)}$`;
  assert(development.includes(printedRow), `continuation table mismatch at ${row.t}`);
}
results.continuation_samples = continuation.samples.length;

const allPlanes = new Set();
const allHigh = new Set();
for (let a = 1; a < 512; a++) for (let b = a + 1; b < 512; b++) {
  const c = a ^ b;
  if (c <= b) continue;
  const key = planeKey(a, b);
  allPlanes.add(key);
  if (ranks[a] >= 2 && ranks[b] >= 2 && ranks[c] >= 2) allHigh.add(key);
}
assert.equal(allPlanes.size, 43435);
assert.equal(allHigh.size, 32018);
const covered = new Set();
const lineCoverCounts = { 17: 0, 18: 0 };
const highSizes = [98, 2352, 1176, 3528, 14112, 4704, 4704, 1344];
for (let index = 478; index <= 491; index++) {
  const [a, b] = catalogue[index].basis;
  const orbit = new Set();
  for (const p of gl) for (const q of gl) {
    orbit.add(planeKey(action(a, p, q), action(b, p, q)));
    orbit.add(planeKey(action(transpose(a), p, q), action(transpose(b), p, q)));
  }
  if (index >= 484) assert.equal(orbit.size, highSizes[index - 484]);
  for (const key of orbit) {
    assert(!covered.has(key), `overlapping two-plane orbits at ${index}`);
    assert(allPlanes.has(key));
    assert.equal(allHigh.has(key), index >= 484);
    if (key.split(',').map(Number).includes(1)) {
      assert(index <= 483);
      lineCoverCounts[index <= 479 ? 17 : 18]++;
    }
    covered.add(key);
  }
}
assert.equal(covered.size, allPlanes.size);
results.two_plane_orbits = 14;
results.two_planes = allPlanes.size;
results.all_high_planes = allHigh.size;
assert.deepEqual(lineCoverCounts, { 17: 15, 18: 240 });
assert.equal(Math.ceil((15 * 17 + 240 * 18) / 254), 19);
results.rank_one_line_cover = { planes: 255, bounds: lineCoverCounts, resulting_bound: 19 };
const p414 = 161, q414 = 84;
assert.equal(ranks[p414], 3);
assert.equal(multiply(q414, q414), 273);
for (const [preimage, target] of [[136, 272], [1, 4], [2, 2]]) {
  assert(span(catalogue[262].basis).includes(preimage));
  assert.equal(action(preimage, transpose(p414), transpose(q414)), target);
}
for (const [index, basis] of [[414, [272, 4, 2]], [415, [273, 4, 2]], [416, [272, 4, 1]]]) {
  const key = span(basis).join(',');
  assert(gl.some(p => gl.some(q =>
    span(catalogue[index].basis.map(a => action(a, p, q))).join(',') === key)),
  `normalized affine source does not match orbit ${index}`);
}
results.affine_source_containment_generators = 3;
results.normalized_affine_source_orbits = 3;

const hyperplanes = [
  [272, 4, 2], [273, 4, 2], [272, 4, 1], [274, 4, 1],
  [272, 4, 3], [273, 4, 3], [272, 2, 1], [276, 2, 1],
  [272, 5, 2], [273, 5, 2], [272, 6, 1], [274, 6, 1],
  [272, 5, 3], [273, 5, 3],
];
const s = new Set(span([272, 4, 2, 1]));
const coset = Array.from({ length: 8 }, (_, w) => 272 ^ w);
assert.deepEqual(coset.map(a => ranks[a]).sort(), [2, 2, 2, 2, 3, 3, 3, 3]);
const hyperKeys = new Set();
for (const h of hyperplanes) {
  const members = span(h);
  assert.equal(members.length, 8);
  assert(members.every(a => s.has(a)));
  assert.equal(members.filter(a => coset.includes(a)).length, 4);
  hyperKeys.add(members.join(','));
}
assert.equal(hyperKeys.size, 14);
let fiveSets = 0;
for (let mask = 0; mask < 256; mask++) {
  const points = coset.filter((_, i) => (mask >> i) & 1);
  if (points.length !== 5) continue;
  assert(hyperplanes.some(h => span(h).filter(a => points.includes(a)).length === 4));
  fiveSets++;
}
assert.equal(fiveSets, 56);
results.affine_hyperplanes = hyperKeys.size;
results.five_point_sets_checked = fiveSets;

const triples = new Map();
for (const line of read('sections/upper-bound.tex').split('\n')) {
  if (!/^\d+ &/.test(line)) continue;
  const nums = line.replace(/\\\\.*/, '').split('&').map(x => x.trim()).filter(Boolean).map(Number);
  for (let i = 0; i < nums.length; i += 4) triples.set(nums[i], nums.slice(i + 1, i + 4));
}
assert.equal(triples.size, 23);
for (let a = 0; a < 9; a++) for (let b = 0; b < 9; b++) for (let c = 0; c < 9; c++) {
  let actual = 0;
  for (const [A, B, C] of triples.values()) actual ^= ((A >> a) & 1) & ((B >> b) & 1) & ((C >> c) & 1);
  const expected = Number(Math.floor(b / 3) === a % 3 && Math.floor(c / 3) === Math.floor(a / 3) && c % 3 === b % 3);
  assert.equal(actual, expected, `upper witness coordinate ${a},${b},${c}`);
}
results.upper_bound_coordinates = 729;

const texFiles = ['main.tex', ...fs.readdirSync(path.join(paper, 'sections')).map(x => `sections/${x}`)];
const tex = texFiles.map(read).join('\n');
const bibliography = read('references.bib');
const bibKeys = [...bibliography.matchAll(/@\w+\{([^,]+),/g)].map(m => m[1]);
const bib = new Set(bibKeys);
assert.equal(bib.size, bibKeys.length, 'duplicate bibliography key');
const citedKeys = new Set();
for (const match of tex.matchAll(/\\cite(?:\[[^\]]*\])?\{([^}]+)\}/g))
  for (const key of match[1].split(',')) {
    assert(bib.has(key), `missing citation ${key}`);
    citedKeys.add(key);
  }
assert.deepEqual([...citedKeys].sort(), [...bib].sort(), 'uncited bibliography entry');
const resolvedKeys = [...read('main.bbl').matchAll(/\\bibitem\{([^}]+)\}/g)].map(m => m[1]);
assert.deepEqual([...resolvedKeys].sort(), [...bib].sort(), 'resolved bibliography differs');
const fixedBibliographyLinks = [...bibliography.matchAll(/\\href\{(https:\/\/github\.com\/[^}]+)\}/g)].map(m => m[1]);
assert.equal(fixedBibliographyLinks.length, 4);
for (const link of fixedBibliographyLinks) {
  if (link === formalizationRelease) continue;
  const parts = new URL(link).pathname.split('/').filter(Boolean);
  assert(['blob', 'tree'].includes(parts[2]));
  assert(/^[a-f0-9]{40}$/.test(parts[3]), `unfixed bibliography artifact: ${link}`);
}
assert(fixedBibliographyLinks.includes(`${sources.research_archive.repository}/blob/${sources.research_archive.revision}/${sources.research_archive.report}`));
assert(fixedBibliographyLinks.includes(`${sources.continuation_start.repository}/tree/${sources.continuation_start.revision}`));
const visibleSources = (tex + '\n' + bibliography).replace(/\\href\{[^}]*\}/g, '');
assert(!/\b[0-9a-f]{40}\b/.test(visibleSources), 'commit identifier in printed manuscript text');
results.cited_entries = citedKeys.size;
results.resolved_bibliography_entries = resolvedKeys.length;
results.pinned_bibliography_links = fixedBibliographyLinks.length;
assert(!/TODO|TBD|PLACEHOLDER|\\(?:include|input)\{\.\./.test(tex));
assert(!/e_3|w_1=1|e_1w\^T/.test(tex), 'inconsistent coordinate indices');
const artifactLinks = [...tex.matchAll(/\\href\{(https:\/\/github\.com\/[^}]+)\}/g)].map(m => m[1]);
for (const link of artifactLinks) {
  const url = new URL(link);
  const parts = url.pathname.split('/').filter(Boolean);
  assert.equal(parts[2], 'blob');
  if (parts[4] === sources.formalization.directory) {
    assert.equal(parts[3], sources.formalization.release_tag, 'formalization link and release differ');
  } else {
    assert(/^[a-f0-9]{40}$/.test(parts[3]), `unfixed research artifact: ${link}`);
  }
}
results.pinned_artifact_links = artifactLinks.length;
results.formalization_revision = sources.formalization.revision;
results.formalization_release = formalizationRelease;
const log = read('main.log') + '\n' + read('main.blg');
assert(!/Overfull|Underfull|Warning:|warning \(|undefined|LaTeX Error|^!/m.test(log));
results.bibliography_entries = bib.size;
results.latex_bibtex_warnings = 0;
results.overfull_boxes = 0;
results.underfull_boxes = 0;
results.final_tex_log = 'No LaTeX or BibTeX warnings, overfull or underfull boxes, undefined references, or errors';
results.note = 'Manuscript data and typesetting checks only; not a new Lean kernel replay.';
fs.mkdirSync(path.join(paper, 'build'), { recursive: true });
fs.writeFileSync(path.join(paper, 'build', 'manuscript-checks.json'), JSON.stringify(results, null, 2) + '\n');
console.log(JSON.stringify(results, null, 2));
