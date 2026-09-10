# three-orbit quotient soundness, controls, and exact quotient search surfaces

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

Active goal: tighten the F2 3x3 matrix multiplication rank gap by either a rank <=22 exact decomposition or a rank >=21 theorem. This ARTIFACT did **not** obtain either final result. It repaired and calibrated the three-orbit quotient framework introduced in analysis.

## 1. Quotient line caps and multiset scope

Script: [quotient_line_caps_and_controls.py](../code/quotient_line_caps_and_controls.py).
Result: [quotient_line_caps_and_controls.json](../results/wang_native/three_orbit_controls/quotient_line_caps_and_controls.json).

For a full rank-20 decomposition, quotienting by any nonzero A-factor leaves a length-19 quotient problem. Under the GL3 x GL3 action on nonzero 3x3 F2 matrices there are three pivot orbits:

- rank1 pivot `1` (E00 / the E11-type quotient after coordinate choice),
- rank2 pivot `17` (E00+E11),
- rank3 pivot `273` (I3).

The decisive multiset test is the Wang cap of every quotient line, equivalently every 2D original subspace containing the pivot, at quotient target n=19.

Exact line-cap results:

```text
rank1/E11: cap histogram {1:249, 2:6}; six repeatable quotient directions remain.
rank2:     cap histogram {1:255}; all 255 quotient lines have LB=18, cap=1.
rank3:     cap histogram {1:255}; all 255 quotient lines have LB=18, cap=1.
```

Therefore distinct-support enumeration is complete for rank2 and rank3 quotient target 19 (any repeated quotient point would put occupancy 2 in a cap-1 quotient line). It is not complete for rank1/E11; the earlier six repeated directions remain and need residual-cap branches or a true weighted search.

Monotonicity note: if target n increases by 1, every cap n-LB increases by 1, and adding a point raises each row occupancy by at most 1. Thus excluding length-19 multisets excludes shorter supports; zero projected terms after quotienting do not require separate handling in the lower-bound branch because a shorter nonzero quotient support is no harder than length 19.

## 2. Multi-bit quotient tensor convention repaired

While computing rank3 quotient slice ranks, a real utility bug was found: for multi-bit pivots such as `273=I3`, projecting an original A-coordinate vector can yield a multi-bit quotient vector. The quotient tensor construction must XOR that original slice into every quotient coordinate bit appearing in the projection, not assume the image is a single quotient basis vector.

Patched function: `quotient_tensor(pivot)` in [quotient_line_caps_and_controls.py](../code/quotient_line_caps_and_controls.py).

After repair:

```text
pivot 1:   tensor nnz 24; slice ranks [3,3,3,3,3,3,3,3]
pivot 17:  tensor nnz 27; slice ranks [6,3,3,3,3,3,3,3]
pivot 273: tensor nnz 30; slice ranks [6,3,3,3,6,3,3,3]
```

The quotient row-preparation projection itself was not changed by this bug; it affects semantic tensor reconstruction and exact Brent CNF generation for rank2/rank3 quotient tensors.

## 3. Positive controls for quotient row/DFS machinery

The previous analysis handoff had no rank2/rank3 positive controls. This ARTIFACT built several.

### Rank2 quotient from the verified rank-23 text scheme

Source full scheme: `data/flip_cpd_inspect/src/khoruzhii-flip-cpd-9eeb17f/data/schemes_paper/gg-333-rank23-rec-0-0-0-z.txt`, verified over F2 in analysis.

The script mapped rank-2 A-factors to pivot 17 using the MM tensor stabilizer
`A -> P^T A Q^{-T}`, `B -> Q^T B`, `C -> P^{-1} C` (with R=I), then projected the selected pivot term away. It produced a verified rank-22 decomposition of the rank2 quotient tensor and the quotient A-multiset passed all rank2 quotient Wang rows at n=22.

File: [rank2_quotient_rank22_control.json](../../occupation_and_completion/results/wang_native/three_orbit_controls/rank2_quotient_rank22_control.json).

However the projected A-multiset has duplicates. Exhaustive search over all 672 mappings from the seven rank-2 A-terms to pivot 17 found no distinct projected support; best duplicate count remained 2.

File: [rank2_all_mapping_search.json](../../occupation_and_completion/results/wang_native/three_orbit_controls/rank2_all_mapping_search.json).

Thus this is a strong semantic quotient-decomposition control, but not by itself a distinct DFS force-control.

### Distinct hill-climb controls accepted by safe DFS

Generated binaries:

- `workspace/data/wang_native/quotient_binaries/e11_all_n21.bin`
- `workspace/data/wang_native/quotient_binaries/rank2_all_n22.bin`
- `workspace/data/wang_native/quotient_binaries/rank3_all_n23.bin`

Hill-climber calibration:

- E11 n=21: [hillclimb_e11_n21_pilot.json](../results/wang_native/stochastic_min/hillclimb_e11_n21_pilot.json) found zero violations in 2 restarts, elapsed 104.6s, support `[8,12,16,18,27,40,53,95,117,136,137,138,139,144,146,192,216,217,221,230,249]`.
- Rank2 n=22: [hillclimb_rank2_n22_pilot.json](../../occupation_and_completion/results/wang_native/stochastic_min/hillclimb_rank2_n22_pilot.json) found zero violations in 1 restart, elapsed 46.2s, support `[3,23,26,29,32,36,48,50,128,130,138,139,142,160,177,181,191,192,198,216,224,241]`.
- Rank3 n=23: [hillclimb_rank3_n23_pilot.json](../results/wang_native/stochastic_min/hillclimb_rank3_n23_pilot.json) found zero violations in 1 restart, elapsed 32.4s, support `[9,21,36,37,38,39,52,53,81,83,85,86,109,144,159,183,189,202,209,212,227,240,252]`.

All three distinct supports were force-tested through `workspace/scripts/wang_domain_dfs_safe` at the corresponding target and accepted at full depth:

- [force_hillclimb_supports_summary.json](../../occupation_and_completion/results/wang_native/stochastic_min/force_controls/force_hillclimb_supports_summary.json) for E11 n=21 and rank2 n=22;
- [rank3_n23_hill_zero_force_summary.json](../results/wang_native/stochastic_min/force_controls/rank3_n23_hill_zero_force_summary.json) for rank3 n=23.

Rank3 still lacks a rank-22 positive control. The verified rank-23 text scheme and the research_record `validation_full_cn122_rank23.json` scheme have no rank-3 factors in any tensor slot, so the term-dropping construction cannot produce a rank3 n=22 control from those sources.

Projection of the full rank-23 text scheme without dropping any term gives valid quotient decompositions at rank 23 for all three pivots and they pass Wang rows at their own lengths, but these controls have duplicate A-directions:

- [projected_rank23_quotient_controls_summary.json](../results/wang_native/three_orbit_controls/projected_rank23_quotient_controls_summary.json) reports rank1 duplicate count 5, rank2 duplicate count 2, rank3 duplicate count 1.

## 4. Calibrated minimizer and n=19 diagnostics

A key evidence correction: the random violation samples from analysis are not a violation floor. They are only crude search-landscape diagnostics. This ARTIFACT instead used the greedy hill-climber in a setting where success is known. It reached zero at E11 n=21, rank2 n=22, and rank3 n=23, so the mechanism is at least capable of finding admissible distinct supports when they exist in these tested regimes.

Short n=19 pilots remain diagnostic only:

- E11 n=19: [hillclimb_e11_n19_pilot.json](../results/wang_native/stochastic_min/hillclimb_e11_n19_pilot.json), best 8 violated rows after two restarts / 186.7s.
- Rank2 n=19: [hillclimb_rank2_n19_pilot.json](../../occupation_and_completion/results/wang_native/stochastic_min/hillclimb_rank2_n19_pilot.json), best 50 violated rows after one restart / 121.8s.
- Rank3 n=19: [hillclimb_rank3_n19_pilot.json](../results/wang_native/stochastic_min/hillclimb_rank3_n19_pilot.json), best 93 violated rows after one restart / 123.0s.

Safe DFS 60s profiles over all-cap quotient rows:

- Rank2 n=19: [rank2_n19_safe_dfs_60s.json](../../occupation_and_completion/results/wang_native/three_orbit_controls/rank2_n19_safe_dfs_60s.json), timeout, max depth 15, 188416 calls, no solution seen.
- Rank3 n=19: [rank3_n19_safe_dfs_60s.json](../results/wang_native/three_orbit_controls/rank3_n19_safe_dfs_60s.json), timeout, max depth 16, 131072 calls, no solution seen.

These are not exclusions. They only show that the corrected propagation search remains hard and that no fast false-UNSAT occurred.

## 5. Exact quotient Brent CNF surfaces

Script: [quotient_core_sat.py](../code/quotient_core_sat.py).

This generic exact SAT encoder targets `T333/span(p)` directly, without Wang rows. It creates rank-r Brent equations for u in F2^8 and v,w in F2^9. It adds only sound slice-capacity clauses using the actual matrix ranks of each quotient slice.

Positive validation:

- `workspace/data/quotient_sat/rank2_q_rank22_control.cnf` with known units from the rank2 quotient rank-22 control validates all clauses (`known_validation_ok: true`). It has 30,167 variables and 141,275 clauses.
- `workspace/data/quotient_sat/rank3_q_rank23_projected_control.cnf` with known units from the projected rank3 rank-23 control validates all clauses (`known_validation_ok: true`). It has 31,568 variables and 199,640 clauses.

Generated exact search CNFs:

- `workspace/data/quotient_sat/rank2_q_rank19.cnf`: 25,964 variables, 107,101 clauses.
- `workspace/data/quotient_sat/rank2_q_rank20.cnf`: 27,365 variables, 117,071 clauses.
- `workspace/data/quotient_sat/rank3_q_rank19.cnf`: 25,964 variables, 123,574 clauses.
- `workspace/data/quotient_sat/rank3_q_rank20.cnf`: 27,365 variables, 138,560 clauses.

CaDiCaL 60s pilots on all four returned UNKNOWN. They produce no mathematical conclusion and no witness, but they establish ready exact constructive surfaces for future longer/symmetry-enhanced runs.

## 6. Current implication status

The three-orbit lower-bound architecture is still attractive but not complete:

- To prove full `R_F2(T333) >= 21`, one can show that for each pivot orbit (rank1, rank2, rank3), the quotient `T333/span(p)` has no length-19 decomposition. The rank2 and rank3 quotient target-19 searches may use distinct supports because all line caps are 1. The rank1/E11 target must handle six repeatable directions.
- No quotient target-19 exclusion has been completed. All n=19 solver/DFS/hill-climb outputs here are only diagnostics.
- For construction, any exact rank-19 quotient decomposition for any pivot would lift to a full rank<=22 scheme by adding a rank-3 complement contraction. This witness path needs no Wang LUT trust. The new `quotient_core_sat.py` surfaces make rank2/rank3 quotient constructive search possible in parallel with E11.

Most important next work: build proof-producing or independently replayable support-exclusion machinery for rank2/rank3 distinct target-19 quotients (possibly easier than E11), while continuing exact Brent witness search. Also find or generate a rank3 rank-22 positive control if possible; rank3 currently has only a n=23 control.
