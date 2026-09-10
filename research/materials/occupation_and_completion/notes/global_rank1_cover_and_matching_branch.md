# global rank-1 geometry cover for the Wang F2 support route

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

The fixed-E11 branch split used earlier chose an arbitrary second point after the rank-1 anchor. The review observation changes the correct global organization of the remaining rank-20 A-support problem: choose the anchor pair using the geometry of the entire selected rank-1 subset, not by a fixed second-orbit descent. This note records the executable checks and the new computational evidence.

The strict research status is unchanged: no rank-22 exact algorithm and no rank-23 optimality proof has been obtained. All CP-SAT results below are search/proof-target evidence only.

## Checked finite geometry

Script: [rank1_geometry_cover.py](../code/rank1_geometry_cover.py).
Output: [rank1_geometry_cover.json](../results/global_cover/rank1_geometry_cover.json).

Verified facts over `F2`:

- There are exactly 49 rank-1 projective A-points, each uniquely represented as `u v^T` with `u,v in F2^3\{0}`.
- Among the `C(49,2)=1176` unordered rank-1 pairs, 294 pairs are adjacent in the Segre grid, meaning they share the left vector `u` or the right vector `v`.
- The full `GL(3,2) x GL(3,2) semidirect transpose` action sends the pair `{E11,E12}` to exactly these 294 adjacent pairs: `orbit_of_E11_E12_equals_all_adjacent_pairs=true`.
- The nonadjacent pairs are exactly the orbit of `{E11,E22}` and number 882.
- Under `Stab(E11)`, the first orbit representative is `rep2 = E12`, with no earlier-orbit exclusions: the orbit order begins `[2,10,16,17,20,84,160,161]`.
- A rank-1 subset with no adjacent pair is a matching in the `7x7` Segre grid; the exact maximum matching size is 7.

Therefore any rank-20 support with at least two adjacent rank-1 A-factors can be normalized to the fixed `E11+E12` branch (`rep2`). If a support has no adjacent rank-1 pair, after fixing one rank-1 point to `E11` its rank-1 subset satisfies explicit matching constraints and has `k <= 7`.

## New global covering structure

The old fixed-second branch split remains valid as a conditional computation, but it is not the best global cover.

For a hypothetical Boolean A-support of length 20 satisfying Wang occupation:

1. First use the verified no-rank-1 branch exclusion to fix some rank-1 A-point to `E11`.
2. If the rank-1 subset contains an adjacent pair, re-anchor the whole support so that pair is `{E11,E12}`. The support lies in the `rep2` branch. This covers all high-k cases `k >= 8` automatically because a matching has size at most 7.
3. If no adjacent pair exists, impose the global matching constraints on the rank-1 variables and only test `k=1..7`.

Thus high-k rep10/rep16 descents are no longer needed for global coverage, though their old CP-SAT and proof-target files remain valid under their original assumptions. The proof obligations become:

- close rep2 for the adjacent-pair branch, especially high `k` first (`k >= 8`, with current guided work at `k=17` and new singleton survey submitted at `k=16`);
- close the nonadjacent matching branch for `k=1..7` using explicit matching constraints and Wang rows;
- retain exact field scope: this is only an `F2` support route toward `R_F2 >= 21`, not a characteristic-zero rank-23 optimality proof.

## Matching branch evidence from this ARTIFACT

Script: [matching_branch_cpsat.py](../code/matching_branch_cpsat.py).
Initial output directory: `workspace/data/matching_branch/`.

Using variables for all 511 nonzero A-projective points, fixing `E11`, imposing exact rank-1 count `k`, enforcing left/right matching constraints among the 49 rank-1 points, and adding dim-1 plus through-`E11` dim-4/6 Wang rows (`194,310` effective rows):

- `k=1`: CP-SAT `UNKNOWN` after 120 s.
- `k=2`: CP-SAT `OPTIMAL`, support with rank histogram `{1:2, 2:18}` at [matching_exact_k02_dims1_through46.json](../results/matching_branch/dim1_through46/matching_exact_k02_dims1_through46.json).
- `k=3`: `UNKNOWN` after 120 s.
- `k=4`: `UNKNOWN` after 120 s.
- `k=5`: `UNKNOWN` after 120 s.
- `k=6`: CP-SAT `OPTIMAL`, support with rank histogram `{1:6, 2:14}` at [matching_exact_k06_dims1_through46.json](../results/matching_branch/dim1_through46/matching_exact_k06_dims1_through46.json).
- `k=7`: `UNKNOWN` after about 89 s.

Full expanded LUT scans of the two row-family supports:

- [full_lut_scan_k02.json](../results/matching_branch/full_lut_scan_k02.json): 8,283,458 keys checked, 10,240 violations, maximum excess 5. Violations are mostly rows not containing `E11` (`none: 10187`, `1: 53`).
- [full_lut_scan_k06.json](../results/matching_branch/full_lut_scan_k06.json): 8,283,458 keys checked, 8,036 violations, maximum excess 4. Violations are mostly rows not containing `E11` (`none: 7988`, `1: 48`).

Adding all dim-2 and dim-3 rows to the matching model for the formerly feasible counts (`include_dims=1,2,3`, through-`E11` dim-4/6, `1,025,682` Wang rows) gave:

- `k=2`: CP-SAT `UNKNOWN` after 300 s, output [matching_exact_k02_dims123_through46.json](../results/matching_branch/dim123_through46/matching_exact_k02_dims123_through46.json).
- `k=6`: CP-SAT `UNKNOWN` after 300 s, output [matching_exact_k06_dims123_through46.json](../results/matching_branch/dim123_through46/matching_exact_k06_dims123_through46.json).

Interpretation: the matching branch is not trivially closed by the through-anchor row family. Its weak supports violate many full LUT rows, so a lazy full-LUT or seeded-row approach is needed.

## New matching lazy full-LUT instrument

Script: [matching_lazy_full_lut.py](../code/matching_lazy_full_lut.py).
Pilot output: [lazy_full_k02.json](../results/matching_branch/lazy_full_k02.json).

This script solves the matching branch, scans each support candidate against all 8.28M LUT rows using repaired vectorized membership, and adds violated rows. A short `k=2` pilot with the large through-anchor row family returned CP-SAT `UNKNOWN` on the first solve after 120 s, before producing a candidate. This shows that the broad initial row family can already be hard; the next better use is likely seeded cuts from actual violation scans or more targeted row families, not blindly increasing time.

## Managed tasks and resource decisions

- `s24_t20_tool1` rep2/k17 exhaustive canonical pairs timed out after 7200 s. Its stdout shows a large prefix of pair classes all `INFEASIBLE`, but the durable JSON summary file is empty; it cannot be used as a complete result or proof. The guided rep2/k17 search is a better instrument.
- `s25_t11_tool2` rep16/k15 exhaustive pairs was cancelled after the global cover made high-k rep16 noncentral for global coverage. Its stdout shows partial progress with some feasible pair relaxations, but it remains only conditional rep16 evidence.
- `s26_t51_tool1` guarded rep2/k17 guided full-high search remains relevant and is still running at the time of this note.
- `s27_t23_tool1` submitted a rep2/k16 singleton survivor survey to support high-k adjacent-pair work.

## Proof discipline

The global cover itself is finite combinatorics plus verified implemented group action. It does not prove a lower bound. To use it for a theorem over `F2`, later work must provide independently checkable infeasibility for:

1. the adjacent-pair branch represented by `rep2` for all relevant `k`, or a stronger full branch proof;
2. the nonadjacent matching branch for `k=1..7` with matching constraints;
3. any imported CP-SAT singleton/pair/hyperedge implication, with source exact `k0`, branch, fixed permanent points, and orbit images preserved as related analysis requested.

Do not transfer conditional rep10/rep16 learned constraints to rep2 or matching cases. The gain is re-anchoring whole supports under the global symmetry, not moving local exclusions between incompatible fixed-second branches.
