# Safe domain-propagation repair and ladder calibration

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Context

analysis's domain-propagation DFS outputs are invalid as evidence. research_record found two false-UNSAT bugs:

1. `small_remain < cap - small_count` treated unused Wang capacity as if it had to be filled. Wang rows are only upper bounds.
2. `select_point` could return after incrementing only some incident counters while restoration decremented all incident counters, causing unsigned underflow.

The earlier nonexistence claim was retracted because of these two implementation errors.

## Safe implementation

New implementation: [wang_domain_dfs_safe.cpp](../code/wang_domain_dfs_safe.cpp).

Mathematical semantics: choose a distinct support of size `target`. For every Wang row, occupancy in that row is at most `cap`. The only forward propagation is:

- when `count(row) == cap(row)`, remove remaining available points in that row from the domain.

No lower-fill rule remains. Counter increments are completed before saturation propagation and every selected point is restored exactly once. Domain removals update `small_remain` only for accounting; no feasibility decision uses `small_remain < cap-count`.

The binary reads both `E11WANG1` (4x64 masks, 255 points) and `WANG512\x01` (8x64 masks, 511 points). It has `--force-prefix` and `--force-only` for solution-preservation tests, `--max-solutions` to stop deliberately after finding candidates, and used-row logging (`--used-output`). After patching, deliberate early solution stops are no longer labelled complete.

## Regression and positive controls

Toy counterexample from research_record:

- constraints: `{1,2}` cap 1, `{2,3}` cap 2;
- target 2;
- known feasible support `{1,3}`.

Files:

- `workspace/data/wang_native/toy/toy_upper_bound.e11wang1.bin`
- [toy_safe_force_13_after_patch.json](../results/wang_native/toy/toy_safe_force_13_after_patch.json)

Result: forced `{1,3}` accepted at full depth with `solutions=1`, `complete=true`.

Known E11 rank-21 all-distinct control:

- pool row 146 from `data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy`;
- support file [e11_poolrow146_distinct21_support.json](../../occupation_and_completion/results/wang_native/controls/e11_poolrow146_distinct21_support.json);
- Wang check at length 21 over cap<=5 rows: accepted ([e11_poolrow146_len21_wangcheck.json](../results/wang_native/ladder_safe/e11_poolrow146_len21_wangcheck.json));
- native force-only result: [e11_poolrow146_len21_force_after_patch.json](../results/wang_native/ladder_safe/e11_poolrow146_len21_force_after_patch.json), `solutions=1`, `max_depth=21`.

Known full rank-23 text scheme:

- source `data/flip_cpd_inspect/src/khoruzhii-flip-cpd-9eeb17f/data/schemes_paper/gg-333-rank23-rec-0-0-0-z.txt`;
- exact parse verifies full `T_{333}` over F2 with diff 0: [full_rank23_text_verify.json](../results/wang_native/controls/full_rank23_text_verify.json);
- support is Wang-accepted at length 23 over cap<=5 full rows: [full_rank23_text_len23_wangcheck.json](../results/wang_native/ladder_safe/full_rank23_text_len23_wangcheck.json).

## Ladder and corrected interpretation

Prepared E11 length-specific cap<=5 rows:

- `workspace/data/wang_native/e11_ladder/e11_wang_cap5_len19.bin`, 338840 rows;
- `workspace/data/wang_native/e11_ladder/e11_wang_cap5_len20.bin`, 257300 rows;
- `workspace/data/wang_native/e11_ladder/e11_wang_cap5_len21.bin`, 118398 rows.

E11 no-force calibrated runs:

- length 21 quickly finds candidates, as required by known decompositions. Latest one-candidate run: [e11_len21_noforce_safe_after_patch_one_candidate.json](../results/wang_native/ladder_safe/e11_len21_noforce_safe_after_patch_one_candidate.json), `solutions=1`, `max_depth=21`, `early_solution_stop=true`, `complete=false` (not exhaustive).
- length 19 with safe propagation does **not** close: [e11_len19_noforce_safe_after_timeoutpatch_20s.json](../results/wang_native/ladder_safe/e11_len19_noforce_safe_after_timeoutpatch_20s.json), `timeout=true`, `solutions=0`, `max_depth=16`, `dfs_calls=104895`. This is only a timeout/prefix profile, not an exclusion.
- an attempted length 20 safe run timed out before writing output under the previous timeout interval. It needs prefix decomposition.

Full tensor length 20 over all 511 A-functionals:

- new proper WANG512 file: `workspace/data/wang_native/full_tensor/full_wang512_cap5_len20_all_dim3.bin` with 831981 dim<=3 cap<=5 rows.
- safe DFS over those rows immediately finds many supports; earlier analysis `rank>=2` empty-in-0.0s was a broken-run artifact, not a robust phenomenon.
- file [full_len20_all_dim3_safe_after_patch_one_candidate.json](../results/wang_native/ladder_safe/full_len20_all_dim3_safe_after_patch_one_candidate.json) records one candidate with `early_solution_stop=true`; the older 101-candidate run is `full_len20_all_dim3_safe_120s.json`.
- complete-Wang checking of the first candidates in `full_len20_dim3_solutions_complete_wang_check.json` found zero complete-Wang survivors among the first 10 checked; each had hundreds of high-dimensional violations. Thus dim<=3 rows are insufficient, while high-dimensional rows contain real additional force.

CEGAR row addition:

- script [full_wang_cegar.py](../../occupation_and_completion/code/full_wang_cegar.py) starts from dim<=3 rows, asks the safe DFS for one support, checks it against the complete LUT, and adds violated high-dimensional rows.
- first three iterations found candidates quickly; iteration 3 (after adding 240 high-dimensional rows, 832221 total selected rows) exceeded the Python subprocess timeout and did not write a final summary. Files under `workspace/data/wang_native/full_tensor_cegar/` preserve the completed iteration outputs.
- This is useful process evidence: adding a small number of high-dimensional rows changes the search from instant-candidate to genuinely hard, so the next route should use prefix decomposition and row-selection strategy, not infer emptiness.

## Wang paper interpretation

Reading Wang's paper, lines 263--372, shows that the published lower-bound program is not exhaustive A-support enumeration against all occupation inequalities. It is dynamic programming over restriction subspace orbits using flattening, forced-product, degenerate-restriction inheritance, and substitution/backtracking certificates. Therefore an exhaustive integral support exclusion against the LUT would be a stronger derived computation and would not automatically contradict the published lower bound 20. However, because our support rows depend on Wang lower-bound values, any theorem needs a compact set of used rows and independent verification of those row lower bounds or certificates.

## Current conclusion

The corrected implementation invalidates the analysis apparent breakthroughs. The safe enumerator passes the toy and known-support preservation tests, but the actual target searches are open:

- no E11 rank-19 support exclusion has been completed;
- no full length-20 support exclusion has been completed;
- no rank-22 construction or rank-21 lower bound has been obtained.

The promising direction is now a checked exhaustive-support computation with: (i) solution-preserving ladder controls; (ii) used-row logging; (iii) compact high-dimensional row selection; (iv) prefix decomposition; and (v) independent peer reimplementation.

## Late analysis corrections after review verification

review verifier result: `independent-verification-record`.

Important hazards identified and repaired or recorded:

1. `full_wang_cegar.py` originally labelled `solutions==0` as `selected_subset_excludes` without requiring an exhaustive DFS result. This could have turned a timeout into a false exclusion. It was patched so an exclusion label requires `complete=true`, `timeout=false`, `early_solution_stop=false`, no subprocess timeout, and `solutions=0`; otherwise zero solutions seen is recorded as `unfinished_no_solution_seen`.

2. A rerun of CEGAR after the patch (`python workspace/scripts/full_wang_cegar.py --length 20 --iterations 4 --timeout 20 --add-per-iter 80 --initial-max-dim 3 --initial-max-cap 5`) saved [cegar_summary.json](../../structural_obstruction/results/wang_native/full_tensor_cegar/cegar_summary.json). Iteration 3, with 832221 selected rows (831981 small + 240 high-dimensional big rows), timed out at 20.427s with no solution seen, max depth 17, 32768 DFS calls, and is correctly labelled `unfinished_no_solution_seen`. This is not an exclusion.

3. Full length-20 line caps were independently checked in [verify_full_len20_line_caps.py](../code/verify_full_len20_line_caps.py), output [full_len20_line_caps.json](../results/wang_validation/full_len20_line_caps.json): all 511 one-dimensional full A-subspaces have LUT LB 19 and cap20 1, split by matrix rank as 49 rank-1, 294 rank-2, 168 rank-3. Therefore any full length-20 Wang-admissible A-multiset is automatically a distinct support. This justifies a distinct-set enumerator for the full length-20 target, conditional on the LUT row semantics and LB values. It does **not** remove the E11 rank-19 multiset issue, because E11 line caps at length 19 allow six repeated quotient directions.

4. The available full rank-23 scheme parsed from text verifies as a full `T_{333}` rank-23 scheme over F2 ([full_rank23_text_verify.json](../results/wang_native/controls/full_rank23_text_verify.json)) and its A-support passes cap<=5 Wang at length 23 (`full_rank23_text_len23_wangcheck.json`), but its A-side has one repeated direction. A scan of nearby rank23 `.npy` corpus files did not find a verified all-distinct-A rank-23 control ([full_rank23_corpus_scan.json](../results/wang_native/controls/full_rank23_corpus_scan.json)). For high-n full positive controls, future work should either add a multiset-capable force review or find another verified all-distinct rank-23 scheme.

5. The review review confirmed the safe C++ no longer contains the two known analysis false-UNSAT mechanisms and that force-prefix tests are meaningful when the complete sorted support is forced. It also warned that `--force-prefix` is lexicographic-prefix semantics, not arbitrary subset forcing; prefix decomposition must use the same semantics for coverage.
