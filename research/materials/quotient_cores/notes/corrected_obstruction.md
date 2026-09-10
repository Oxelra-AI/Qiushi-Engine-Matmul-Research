# CORRECTED: Second-Order Deformation Analysis at Rank-23 Decompositions

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Critical correction from initial analysis

The initial report claimed "universal second-order obstruction" at all tested rank-23
decompositions. This was **wrong** due to two issues:
1. Checking individual SVD basis vectors is NOT equivalent to checking all directions
2. A factor-of-2 error in the Veronese mapping for off-diagonal terms

## Corrected results at cn122

| Quantity | Value |
|----------|-------|
| Jacobian rank | 527 / 621 |
| Kernel dimension | 94 |
| Symmetry subspace | 71 (46 rescaling + 26 stabilizer, overlap 1) |
| Residual dimension | **23** |
| Effective quadratic obstruction equations | **15** |
| Unobstructed directions found | **1000** (all 1000 random starts) |
| Local solution variety dimension | **≥ 14** |

### Explanation

The 202-dimensional cokernel of J generates 202 quadratic constraint equations on the
23 residual deformation variables. However, these 202 equations collapse to only **15
algebraically independent** quadratic equations. With 23 variables and 15 equations,
the solution variety (the "Kuranishi zero set") is generically 8-dimensional. The actual
local dimension is at least 14 because the Jacobian of the 15-equation system at a
solution has rank only 9.

Individual SVD basis vectors e_j are all obstructed (each satisfies only some equations),
but generic linear combinations x = Σ x_j e_j satisfy ALL equations simultaneously.

### Verification

All 10 verified solutions have |cokernel projection| / |Q(d,d)| < 10^{-14},
confirming Q(d,d) ∈ Im(J) to machine precision.

## Mathematical interpretation

The decomposition variety F_{23}(T) = Φ_{23}^{-1}(T) is smooth at cn122 with
local dimension at least 71 (symmetry) + 14 (unobstructed residual) = 85.

There exist at least a 14-dimensional family of genuine deformation directions
(modulo symmetry) that preserve T_{3,3,3} at second order. These are NOT obstructed.

## Implications for rank-22 question

This result does NOT prove rank-22 exists, but it removes the "local rigidity" barrier:
- The rank-23 decomposition variety is genuinely large and deformable
- Rank-22 = F_{23}(T) ∩ {pairing rank ≤ 22}, a codimension-1 condition
- A 14-dim deformation family could potentially intersect this locus
- The question reduces to: does F_{23}(T) intersect the pairing rank-defect locus?

## What remains

1. **Exact rational verification**: Key computation (15 independent equations, 14-dim
   solutions) should be verified over Q using modular arithmetic
2. **Same analysis on other schemes**: Check serendipitous_8d34 and naive_c88
3. **Pairing-rank trajectory**: Do any unobstructed directions move toward pairing
   rank defect at finite (not just infinitesimal) parameter?
4. **Third-order analysis**: Can the second-order deformation paths be extended?
5. **Global structure**: Does the full decomposition variety F_{23}(T) contain
   pairing-rank-defect points?

## Stabilizer verification note

The GL_3^3 sandwich action δU=pU-Uq, δV=qV-Vr, δW=pW-Wr generates 27 Lie algebra
vectors. Of these, 9 (the dQ directions) are individually in ker(J), while 18 (dP, dR)
individually produce nonzero J·s. But 26 LINEAR COMBINATIONS of all 27 are in ker(J).
The missing 1 is the scalar (aI,0,-aI) giving J·s = 4a·T ≠ 0, because the full GL_3^3
does NOT preserve T (it scales by λ²/ν² for scalar (λI,μI,νI)).

## Files

- [corrected_obstruction.json](../../exact_baselines/results/cn122_r23_reproduce/corrected_obstruction.json)
- [corrected_kuranishi.py](../code/corrected_kuranishi.py)
- [kuranishi_variety.py](../code/kuranishi_variety.py) (has the factor-of-2 bug)
- [second_order_obstruction.py](../code/second_order_obstruction.py) (initial, per-vector only)
