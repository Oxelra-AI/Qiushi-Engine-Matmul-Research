# Route synthesis after nontransverse exclusion and numerical optimization

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Current characteristic-zero status

### What is established

1. **Nontransverse stratum excluded** (earlier analysis).
   Subject to Bläser's small-format input R(M_⟨3,3,2⟩) ≥ 14 (cited from Bläser 2003 via Landsberg; formula 2nm−m+2n−2 at n=3,m=2):
   - The nonsemisimple alignment lemma forces semisimplicity of the stabilizer difference operators in any full-span termwise-aligned decomposition.
   - The exact semisimple arrangement enumeration over the 9 eigenvalue variables finds 6424 noncentral flats with minimum certified block-rank sum 23.
   - Therefore no full-span, noncentral, termwise-aligned rank-22 decomposition of T₃₃₃ exists over characteristic zero.

   Combined with the non-full-span exclusion (each T₃₃₃ flattening has rank 9, forcing full span), this removes the entire nontransverse stratum.

2. **Transverse gauge chart calibrated** (earlier analysis).
   - Random rank-22 controls: J+G rank 594 (isolated points), shortened J rank 352, gauge rank 68.
   - At T₃₃₃ (if rank 22): Terracini defect forces J rank ≤ 526, shortened ≤ 328.
   - The 24-dim defect is compensated by the 24-dim noncentral stabilizer: quotient moduli remain 0-dimensional.
   - First-order dimension counting cannot prove rank ≥ 23.

3. **Projected-kernel model calibrated** (analysis).
   - Sparse 72×81 map π with rank(πX) = 13 equivalence for rank-22.
   - Random controls pass; cn122 and all one-term truncations fail (rank 14).
   - Lower-UV-rank strata correspond to rank(πX) ≤ 12.

4. **ALS/Newton over F_p ruled out** (analysis).
   - No metric over F_p → ALS has no convergence mechanism.
   - Confirmed: 3000+ random starts, 200 homotopy tries, all zero successes including positive controls.

### Numerical optimization (analysis, new)

First real-valued (ℝ) optimization of the rank-22 decomposition problem for T₃₃₃.

**ALS over ℝ** (123 starts: 100 random + 23 cn122 truncations, 2000 iterations each):
- Best rank-22: drop_term=1 → 1.979e-02 relative residual
- Best random: 2.838e-02
- For calibration: rank-23 random starts → best 8.787e-03 (NEVER converges to 0)
- rank-23 from cn122 exact → ~5e-12 (immediate)

**Levenberg-Marquardt polish** (scipy.optimize.least_squares with analytical Jacobian):
- Jacobian verified (max error 1.6e-08 vs finite differences)
- Generic Jacobian rank at random UV point: 550 (matches modular computation)
- drop_1 start: ALS 1.979e-02 → LM **5.469e-04** (2000 nfev, still decreasing)
- random_60: 2.838e-02 → 2.779e-03
- random_81: 3.005e-02 → 3.160e-03

**Crucial calibration**: ALS+LM at rank-23 from random starts does NOT converge to 0 for T₃₃₃ (best ~8.8e-03 from ALS alone). This means non-convergence at rank-22 CANNOT be interpreted as evidence for rank > 22. The loss surface of T₃₃₃ is highly non-convex with many local minima at both rank 22 and rank 23.

**Extended LM result (10000 nfev, v4)**: The best starting point (cn122 drop=1) improved further:
- 2000 nfev: 5.469e-04
- 10000 nfev: **2.231e-04** (cost=6.72e-07, optimality=2.90e-03, still not converged)

The optimizer is making steady progress but at a sublinear rate: 2.45× improvement with 5× more evaluations. The nonzero optimality (2.9e-03) means the gradient is still nonzero — the optimizer has not reached a stationary point. This could mean either:
(a) approaching a rank-22 solution through a narrow valley (would eventually converge to 0), or
(b) approaching a saddle point or local minimum above 0.

**Critical missing comparison**: The rank-23 LM comparison and random-tensor control experiments did not complete due to timeout. Without knowing whether rank-23 decompositions converge under LM from random starts, we cannot assess the relative difficulty of rank 22 vs rank 23 optimization on T₃₃₃. This comparison must be completed before drawing conclusions.

### M_⟨3,3,2⟩ SAT verification attempt

Built F_2 SAT encoding for rank-13 and rank-14 of M_⟨3,3,2⟩ (9×6×6 tensor):
- Rank 14: 8718 variables, 34344 clauses → CaDiCaL TIMEOUT at 300s, Kissat TIMEOUT at 300s
- The problem is too hard for direct SAT at this size; computational verification of R_F2(M_⟨3,3,2⟩) ≥ 14 not obtained

### Open strata

The characteristic-zero rank-22 question now reduces to:
1. **Transverse full-span/full-UV-rank**: the 531-equation system in 396 variables (gauge to 328). Gauge chart is calibrated with isolated solutions at smooth points. No constructive solution found; no algebraic elimination or impossibility proof.
2. **Lower-UV-rank**: rank(πX) ≤ 12 in the projected-kernel model. These are lower-dimensional strata that could contain rank-22 decompositions with dependent UV columns.

### Research directions

**Most promising for construction**: 
- Continue the numerical optimization with more iterations and better starting points
- Use the projected-kernel structure for algebraic subsystem solving
- p-adic lifting if a modular root is found

**Most promising for lower bound**:
- The transverse chart's gauge-fixed system has 0-dimensional moduli. Higher-order algebraic invariants (beyond first-order Terracini) could detect emptiness.
- The projected-kernel rank condition gives a specific algebraic variety whose emptiness can in principle be tested by elimination.
- F_2 lower bound from related analysis's Wang branch work (mid-range k=1..17 still open).

### Files

- Bläser bound and integrated theorem: [blaser_bound_and_nontransverse_exclusion.md](../../deformation_and_incidence/notes/blaser_bound_and_nontransverse_exclusion.md)
- Optimization scripts: `scripts/real_rank22_optimizer_v*.py`
- Partial optimization data: `tasks/s24_t13_tool1/stdout.log` (v1 ALS results) and `tasks/s24_t24_tool1/stdout.log` (v3 ALS+LM)
- M_⟨3,3,2⟩ SAT: [M332_sat.py](../code/M332_sat.py), `data/blaser_verification/`
