import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import crypto from 'node:crypto';

const paper = fileURLToPath(new URL('../', import.meta.url));
const project = path.dirname(paper.replace(/\/$/, ''));
const formal = path.join(project, 'formalization');
const data = path.join(paper, 'data');
const readJson = name => JSON.parse(fs.readFileSync(path.join(formal, name), 'utf8'));
const registry = readJson('FrozenRegistry/checked.json').entries.sort((a, b) => a.index - b.index);
assert.equal(registry.length, 496);

// The frozen Lean fixture uses literal nested matches, in blocks of 32.
const lean = fs.readFileSync(path.join(formal, 'QiushiFrozenWangData.lean'), 'utf8');
function literalMatch(name, next) {
  const body = lean.split(`def ${name} `)[1].split(`def ${next} `)[0];
  const result = new Map();
  let block;
  for (const line of body.split('\n')) {
    const outer = line.match(/^  \| (\d+) =>$/);
    if (outer) block = Number(outer[1]);
    const inner = line.match(/^    \| (\d+) => (.+)$/);
    if (inner) {
      assert.notEqual(block, undefined);
      const index = 32 * block + Number(inner[1]);
      assert(!result.has(index));
      result.set(index, JSON.parse(inner[2]));
    }
  }
  assert.equal(result.size, 496);
  return result;
}
const bases = literalMatch('frozenWangBasis', 'frozenWangLower');
const labels = literalMatch('frozenWangLower', 'frozenWangTable');
const catalogue = registry.map(({ index, basis, lb }, i) => {
  assert.equal(index, i);
  assert.deepEqual(basis, bases.get(i));
  assert.equal(lb, labels.get(i));
  return { index, basis, lower_bound: lb };
});
fs.mkdirSync(data, { recursive: true });
fs.writeFileSync(path.join(data, 'frozen-catalogue.json'), JSON.stringify(catalogue, null, 2) + '\n');

const row = entry => `${entry.index} & $(${entry.basis.join(',')})$ & ${entry.lower_bound}`;
const catalogueTex = [
  '% Generated from the checked frozen registry; see tools/prepare-data.mjs.',
  '\\begingroup',
  '\\small',
  '\\setlength{\\tabcolsep}{4pt}',
  '\\renewcommand{\\arraystretch}{1.08}',
  '\\begin{longtable}{@{}rlr@{\\hspace{12mm}}rlr@{}}',
  '\\caption{All $496$ frozen representative bases and labels.}\\label{tab:catalogue}\\\\',
  '\\toprule',
  '$i$ & Basis of $W_i$ & $\\ell_i$ & $i$ & Basis of $W_i$ & $\\ell_i$\\\\',
  '\\midrule\\endfirsthead',
  '\\multicolumn{6}{c}{\\tablename\\ \\thetable: continued}\\\\',
  '\\toprule',
  '$i$ & Basis of $W_i$ & $\\ell_i$ & $i$ & Basis of $W_i$ & $\\ell_i$\\\\',
  '\\midrule\\endhead',
  '\\midrule\\multicolumn{6}{r}{Continued on the next page}\\\\\\endfoot',
  '\\bottomrule\\endlastfoot',
];
for (let i = 0; i < 248; i++) catalogueTex.push(`${row(catalogue[i])} & ${row(catalogue[i + 248])}\\\\`);
catalogueTex.push('\\end{longtable}', '\\endgroup', '');
fs.writeFileSync(path.join(data, 'frozen-catalogue.tex'), catalogueTex.join('\n'));

const summaries = [];
for (let i = 484; i <= 491; i++) {
  const table = readJson(`certificates/${i}/tables.json`);
  const branches = readJson(`certificates/${i}/branch.json`);
  assert.deepEqual(table.basis, catalogue[i].basis);
  assert.equal(table.target, 18);
  assert.equal(table.n_live + table.n_dead, 127);
  assert.equal(table.source_rows.length, table.n_occ);
  assert.equal(table.dead_witnesses.length, table.n_dead);
  assert.equal(branches.branch.certs.length, table.n_leaves);
  summaries.push({ index: i, live: table.n_live, source_rows: table.n_occ,
    zero_rows: table.n_dead, leaves: table.n_leaves });
}
assert.equal(summaries.reduce((s, x) => s + x.source_rows + x.zero_rows, 0), 5917);
fs.writeFileSync(path.join(data, 'branch-summary.json'), JSON.stringify(summaries, null, 2) + '\n');
const branchTex = [
  '% Generated statistics of the integer branch certificates, not DRAT.',
  '\\begin{table}[htbp]', '\\centering',
  '\\caption{Integer branch certificates after zero-weight elimination.}',
  '\\label{tab:branches}', '\\begin{tabular}{rrrrr}', '\\toprule',
  'Plane & Live variables & Source rows & Zero-forcing rows & Leaves\\\\', '\\midrule',
  ...summaries.map(x => `${x.index} & ${x.live} & ${x.source_rows.toLocaleString('en-US').replace(',', '{,}')} & ${x.zero_rows} & ${x.leaves}\\\\`),
  '\\bottomrule', '\\end{tabular}', '\\end{table}', '',
];
fs.writeFileSync(path.join(data, 'branch-summary.tex'), branchTex.join('\n'));

const verification = readJson('verification-results.json');
const manifest = readJson('verification.json');
assert.equal(verification.status, 'pass');
assert.equal(verification.source_build.registered_modules, 13438);
assert.equal(manifest.groups.reduce((s, g) => s + g.roots.length, 0), 89);
assert.equal(manifest.groups.length, 6);
assert.equal(verification.root_manifest_sha256,
  crypto.createHash('sha256').update(fs.readFileSync(path.join(formal, 'verification.json'))).digest('hex'));
fs.writeFileSync(path.join(data, 'formalization-verification.json'), JSON.stringify(verification, null, 2) + '\n');
console.log('Prepared 496 exact catalogue entries, 8 branch summaries, and the recorded verification metadata.');
