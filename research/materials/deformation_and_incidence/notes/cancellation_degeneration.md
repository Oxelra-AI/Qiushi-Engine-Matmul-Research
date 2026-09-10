# Cancellation Degeneration — Definitive Closure of the Continuation Route

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Main Result

**All tested gauge-fixed continuation paths from rank-23 decompositions of T_{3,3,3}
approach a border-rank-22 configuration at t→∞, not a genuine rank-22 decomposition
at any finite parameter value.** This is a cancellation degeneration: pairs of terms
converge projectively in their two-factor (u⊗v) pairing while their third factors (w)
diverge to compensate. The decreasing column-normalized pairing singular values
reflect this border-rank phenomenon, not approach to a rank-reduction boundary.

## Evidence

### Serendipitous_8d34, ranked:0 direction (analysis continuation path)

The gauge-fixed continuation from analysis produced a path with Brent residuals ~10⁻¹⁴
to ~10⁻¹² through t=60. The column-normalized uv pairing σ_min fell from 0.1033 to
4.745×10⁻⁵. Analysis reveals:

1. **Two-term projective merging**: Terms 10 and 17 become projectively identical
   in the uv pairing: cosine similarity 0.9999999958 at t=60, angular distance 9.2×10⁻⁵.
   This null vector structure stabilizes from t≈5 onward (sparsity = 2).

2. **Factor divergence**: Term norms grow roughly linearly in t:
   - Term 10: ||u||=25.8, ||v||=28.9, ||w||=23.9 at t=60 (growth 17-27×)
   - Term 17: ||u||=32.3, ||v||=22.2, ||w||=24.7 at t=60 (growth 17-29×)

3. **Absorbed w analysis**: After projective uv normalization:
   - |w₁₀+w₁₇| (sum) = 45.7 at t=60 — bounded
   - |w₁₀-w₁₇| (diff) = 22115 at t=60 — divergent
   This is the classical cancellation signature: the two terms contribute
   d ⊗ (w₁₀+w₁₇) + ε ⊗ (w₁₀-w₁₇) where ε→0 and w₁₀-w₁₇→∞.

4. **Power-law decay**: σ_min(t) ~ 2.65 × t⁻²·⁷¹ (R²=0.92). The finite-boundary
   model (σ ~ (t*-t)^β) gives t*=1005 with R²=0.17 — essentially rejected.

5. **Laurent limit is invalid**: The s=1/t quadratic extrapolation gives a limit
   with ||T_lim|| = 1206 (target 15.6), relative residual 77×. The path diverges.

### Generic behavior across directions and families

- **Serendipitous_8d34**: 7/10 tested liftable directions show cancellation (cos>0.99)
  at t=20. Cancelling pairs: (10,17), (10,15), (7,14), (18,20), etc.
- **cn122**: 9/10 tested liftable directions show cancellation at t=20.
  Cancelling pairs: (2,4), (10,12), (7,10), (14,21), (1,19), (0,18), etc.
- The remaining directions did not converge (Brent residual blew up at t=5),
  not evidence against cancellation but solver failure at that ARTIFACT size.

## Mathematical Interpretation

The rank-23 decomposition variety F₂₃(T) near T_{3,3,3} has a boundary that
generically consists of border-rank-22 configurations, not genuine rank-22
decompositions. Specifically:

- Each deformation direction within the unobstructed residual tangent space
  drives a specific pair of terms toward projective coalescence in their
  two-factor pairing
- The corresponding third factors diverge oppositely, maintaining the tensor
  identity through a cancellation that becomes singular in the limit
- Different directions cause different pairs to merge, but the qualitative
  behavior is universal

This is consistent with the expected structure of secant variety boundaries.
The closure of σ₂₃ (rank-≤23 locus) contains σ̄₂₂\σ₂₂ (border-rank-22 points
that are not rank-22), and the paths from the interior of σ₂₃ generically
approach these border points rather than crossing to the interior of σ₂₂.

## Consequence for the Rank-22 Problem

**The continuation-from-rank-23 approach cannot produce a rank-22 decomposition.**
This is not because the continuation fails numerically; it succeeds perfectly in
tracking the Brent-equation variety. Rather, the variety itself leads to the
"wrong" boundary — the border-rank boundary rather than the rank-reduction boundary.

This definitively closes the main characteristic-zero upper-bound route pursued
in earlier analysis.

## What This Does NOT Prove

- It does NOT prove rank(T_{3,3,3}) = 23
- A rank-22 decomposition could still exist in a completely different component
  of the decomposition variety, or found by direct construction
- The cancellation is a property of deformation from existing rank-23 points,
  not an intrinsic obstruction to rank-22 existence

## Implications for Future Directions

1. **Upper bound**: Must use direct construction (SAT, algebraic, heuristic search)
   rather than deformation from rank-23
2. **Lower bound**: The generic cancellation structure might be formalizable as an
   obstruction theory (very hard, but geometrically natural)
3. **Finite-field route**: Not affected by this finding; restricted-core searches
   and SAT/occupation-constraint approaches remain viable

## Key Files

- [puiseux_analysis.json](../../exact_baselines/results/fmm_r23_schemes/puiseux_analysis.json) — power-law and Laurent fits
- [cancellation_analysis.json](../../exact_baselines/results/fmm_r23_schemes/cancellation_analysis.json) — detailed projective analysis
- [cancellation_scan_serendipitous.json](../../exact_baselines/results/fmm_r23_schemes/cancellation_scan_serendipitous.json) — multi-direction scan
- [cancellation_scan_cn122.json](../../exact_baselines/results/cn122_r23_reproduce/cancellation_scan_cn122.json) — cn122 scan
- [puiseux_analysis.py](../../quotient_cores/code/puiseux_analysis.py) — power-law/Laurent analysis
- [projective_cancellation.py](../code/projective_cancellation.py) — projective normalization
- [cancellation_scan.py](../code/cancellation_scan.py) — multi-direction cancellation scan
