# Computational synthesis — regularized optimization and Koszul analysis

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Key results

### 1. Regularized real optimization (ALS + LM with L2 regularization)

From cn122 drop=1 (the best starting point from analysis):

| λ       | Brent rel | Amplitude   | nfev | optimality | Time  |
|---------|-----------|-------------|------|------------|-------|
| 0       | 4.54e-05  | 33,037,343  | 5000 | 6.27e-04   | 533s  |
| 1e-08   | 6.33e-04  | 1,951,300   | 1041 | 9.06e-06   | 227s  |
| 1e-06   | 3.49e-03  | 344,341     | 521  | 3.05e-05   | 106s  |
| 1e-04   | 2.30e-02  | 69,740      | 95   | 4.16e-06   | 18s   |

Reference: cn122 exact rank-23 has amplitude ≈ 82.15.

**Scientific interpretation**: The residual-amplitude tradeoff is monotonic and
dramatic: lower residual requires exponentially larger factor norms. The
unregularized case (λ=0) achieves rel=4.5e-05 by allowing amplitude 33M (400,000×
the exact rank-23 amplitude). With ANY positive regularization, the optimizer
converges to a local minimum with:
- Nonzero Brent residual
- Bounded factors (proportional to 1/λ)
- Very small gradient (optimality 1e-05 to 1e-06), confirming true convergence

This establishes that the residual decrease observed in earlier analysis is ENTIRELY
due to cancellation degeneration toward a border-rank point, not approach to a
finite rank-22 decomposition. No bounded rank-22 basin of attraction exists
near the cn122 one-term deletion.

The unregularized result (4.5e-05) is 5× better than analysis's best (2.23e-04)
because the proven v3 Jacobian is more efficient per evaluation.

### 2. Koszul/exterior flattening bounds for M_⟨3,3,2⟩

All exterior Koszul flattenings for M_⟨3,3,2⟩ ∈ K^9 ⊗ K^6 ⊗ K^6 computed.
Best self-contained bound: **R(M_⟨3,3,2⟩) ≥ 11** from mode-1 (exterior on
B=K^6) degree d=2: rank(φ)=54, C(5,1)=5, ceil(54/5)=11.

Other notable entries:
- Mode 0, d=4-6: R ≥ 9 (exterior on A=K^9)
- Mode 1, d=3: R ≥ 11 (rank=105, C(5,2)=10)
- Mode 2, d=4-5: R ≥ 11 (dual of mode 1)

**The gap 11 → 14 cannot be closed by exterior flattenings alone**. Bläser's
substitution method (J. Complexity 19(1), 2003, 43-60) is the unique source of
R ≥ 14.

### 3. Critical Bläser dependency analysis

From the analysis arrangement data: 36 of 6424 noncentral flats have certified
block-rank sum exactly 23 (minimum). These 36 all contain a (2,3,3)=(M_⟨3,3,2⟩)
block with lb=14. Replacing 14 with Koszul bound 11 gives sum 20, which does
NOT exclude those patterns.

**The nontransverse exclusion is load-bearing on exactly R(M_⟨3,3,2⟩) ≥ 14.**
With any weaker bound, 36 patterns survive and the exclusion is incomplete.

### 4. M_⟨3,3,2⟩ over F₂: SAT status

CryptoMiniSat5 with native XOR encoding (5187 vars, 15444 AND + 324 XOR clauses)
returned UNKNOWN after 300s for rank 13. This is neither evidence for nor against
R_F₂(M_⟨3,3,2⟩) ≥ 14.

### 5. Modular Newton analysis

I established that Newton's method over F_p does NOT have metric-based convergence:
the "perturbation" δθ ∈ F_p has no concept of "small," so Newton steps from any
non-exact starting point produce random-looking iterates. This is a fundamental
limitation, not an implementation bug. Over F_p, only Hensel lifting from an
existing mod-p solution can provide convergence, and we have no such starting
point for T₃₃₃.

### 6. related analysis F₂ status correction

related analysis retracted the R_F₂(T₃₃₃) ≥ 21 claim (record) due to a PySAT
CardEnc sequential-counter variable collision. Status returns to:
**20 ≤ R_F₂(T₃₃₃) ≤ 23**, with reps 2,10,16 of the fixed-E11 branches
still open.

## Research state summary

The characteristic-zero rank-22 question decomposes into:

1. **Nontransverse exclusion** (earlier analysis): COMPLETE modulo Bläser's
   R(M_⟨3,3,2⟩) ≥ 14 (J. Complexity 19(1), 2003, 43-60). All 6424 noncentral
   semisimple termwise-aligned flats have certified block-rank sum ≥ 23.
   Non-full-span excluded by T₃₃₃ flattening rank 9. Self-contained Koszul
   bound reaches only 11, leaving a gap of 3 that requires Bläser's
   substitution method.

2. **Transverse full-span rank-22 charts**: Unsolved. The regularized optimizer
   confirms that no bounded rank-22 decomposition exists near cn122 truncations.
   The gauge-fixed and projected-kernel systems are calibrated but have no
   exact roots for T₃₃₃. Lower-UV-rank strata remain separate.

3. **F₂ branch**: 20 ≤ R_F₂ ≤ 23, with the Wang certificate giving 20 and
   cn122 giving 23. The E11 restricted-core rank-19 construction search
   failed. Fixed-E11 exact-18 branch closed by DRAT, but k=1..17 branches
   for reps 2,10,16 remain open.

## Files

- [koszul_flattening_bounds.json](../../symmetry_and_residuals/results/M332_bounds/koszul_flattening_bounds.json): all Koszul bounds
- `data/regularized_optimizer/`: optimizer results (partial, from bg task)
- `data/M332_sat/M332_rank13.cnf`: SAT encoding
- [koszul_M332.py](../../symmetry_and_residuals/code/koszul_M332.py): Koszul computation
- [regularized_optimizer_v2.py](../code/regularized_optimizer_v2.py): regularized optimizer
- [M332_f2_sat.py](../code/M332_f2_sat.py): F₂ SAT encoding
- [modular_newton_homotopy.py](../code/modular_newton_homotopy.py): modular Newton (abandoned)
