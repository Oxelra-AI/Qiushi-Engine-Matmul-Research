# S_min universality and exact fixed-A coset exclusions

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Key structural theorem: S_min cover universality

For any 4-dimensional E11 A-subspace V, define S_min = span{Q_V[k,:,:] : k=0,...,3} (the span of the 4 quotient tensor A-slices). Since S_min ⊆ S for any quotient CPD with matrix subspace S = span{M_j}, and m_phi(S) ≤ m_phi(S_min), the S_min cover condition is the *hardest* version: if it passes, every quotient CPD also passes.

**Result**: ALL 620 four-dimensional V-orbit representatives pass the S_min cover condition. Distribution of minimum feasible residual budget:
- 251 orbits: best_feasible_s = 6 (need quotient rank ≤ 13)
- 309 orbits: best_feasible_s = 8 (need quotient rank ≤ 11)
- 60 orbits: best_feasible_s = 9 (need quotient rank ≤ 10)

**Implication**: The contraction-coset m_phi obstruction CANNOT universally block the E11 rank-19 quotient-lift approach for any V-orbit. The obstruction, if it exists, must come from the actual tensor decomposition (rank-one constraint), not the covering condition.

File: [vs_smin_all620.json](../results/vs_smin/vs_smin_all620.json)

## Orbit 445 exhaustive fixed-A coset exclusion

Orbit 445: prefix [1,2,8,64], flat_lb=6, quotient nnz=12, sum_m=54 with S_min.

flip-cpd achieved quotient rank 11 (542 schemes, failed at rank 10).
Pool: [mod2-rank11a.npy](../../exact_baselines/arrays/quotient_workspaces/q_1_2_8_64/data/schemes_modp/q_1_2_8_64/mod2-rank11a.npy)

For rank 11, residual budget s=8. The actual m_phi from rank-11 CPDs (all 20 tested) has sum_m=54, 8s=64, cover feasible. Exactly 12 valid integer cover assignments exist (enumerated exhaustively):
```
[2,2,3,4,5,8,9,12], [2,2,3,4,5,8,9,13], [2,2,3,4,5,8,12,13],
[2,2,3,4,5,9,12,13], [2,2,3,4,8,9,12,13], [2,2,3,5,8,9,12,13],
[2,3,3,4,5,8,9,12], [2,3,3,4,5,8,9,13], [2,3,3,4,5,8,12,13],
[2,3,3,4,5,9,12,13], [2,3,3,4,8,9,12,13], [2,3,3,5,8,9,12,13]
```

Fixed-A coset SAT with `e11_fixed_a_coset_lift_sat.py` (836 variables, 324 XOR constraints per instance): ALL 12 covers × 542 schemes = 6504 instances UNSAT, total time ~132s. The bottleneck is the rank-one constraint on B⊗C matrices—relaxing it makes all instances trivially satisfiable.

General (unrestricted A) coset SAT on scheme 0 with 600s timeout: UNKNOWN (3460 variables, too large for CryptoMiniSat).

Files: [orbit445_valid_covers.json](../../structural_obstruction/results/coset_lift_results/orbit445_valid_covers.json), `orbit445_r11_fixedA/`

## Orbits 455, 509: quotient rank gap

Orbit 455 (prefix [1,2,80,152], sum_m=45, best_s=6, nnz=21): flip-cpd achieved rank 14, failed at 13. Need q≤13 for s=6 cover. Actual m_phi from rank-14 CPDs: sum_m=42-45 vs 8s=40, cover fails at s=5.

Orbit 509 (prefix [1,6,8,64], sum_m=48, best_s=6, nnz=15): flip-cpd achieved rank 14, failed at 13.

These orbits have the best S_min profiles but their quotient tensors appear to have rank ≥14, creating a 1-unit gap with the needed q≤13.

## related analysis Wang LUT cross-check

related analysis's `wang_subspace_lut.pkl` SHA256 `4704acba23a97d40aa65d5a65222dcb679461fdccf3e41dbeed2a634894a3b33` matches. Metadata shows 8,283,458 subspaces in 496 orbits under a 56,448-element action, consistent with GL(3,2)×GL(3,2)⋊C2 on T333 tensor subspaces. Dimension distribution matches Gaussian binomial coefficients for F_2^9.

## Tools built

- `e11_vs_smin_scan.py`: S_min cover analysis across all V-orbits (LP-optimized)
- `e11_fixed_a_coset_lift_sat.py`: Fixed-A-assignment coset SAT (836 vars, ~0.02s/instance)
- `e11_make_quotient_workspace.py`: Generate quotient tensor and flip-cpd workspace

## Research state

The quotient-lift route is structurally feasible (S_min doesn't block) but computationally blocked: available flip-cpd pools don't contain the right quotient CPDs. The rank-one constraint is the true bottleneck, not the covering condition. The E11 rank-19 question remains open. Fixed-A B/C exact solving is ready for any fully Wang-admissible support related analysis exposes.
