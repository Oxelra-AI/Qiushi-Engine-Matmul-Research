# KY tangent analysis and Klein conjugacy

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Result 1: BILR is first-order isolated in the KY-low-rank stratum

**Theorem (first-order isolation, verified mod 65521 and mod 32003).**
At the displayed BILR internal frame, the 1134×1134 Koszul–Young flattening of
the residual cubic R has rank 722 (corank 412). Among the 32 internal frame
tangent directions (4 planes × 8 sl_3 basis elements):

- The 8 torus directions (H₁, H₂ per plane) fix R exactly (δR = 0) and are
  trivially tangent.
- All 24 non-torus directions (E₁₂, E₁₃, E₂₁, E₂₃, E₃₁, E₃₂ per plane)
  have strictly positive rank(V^T KY(δR) U):

| Direction | rank mod 65521 | rank mod 32003 |
|-----------|----------------|----------------|
| E₁₂      | 84             | 70             |
| E₁₃      | 50             | 18             |
| E₂₁      | 26             | 16             |
| E₂₃      | 32             | 11             |
| E₃₁      | 26             | 16             |
| E₃₂      | 76             | 69             |

The ranks are orbit-independent (same for all 4 planes), reflecting Z₄ symmetry.

**Consequence.** Since KY rank ≥ 701 certifies Waring rank ≥ 11, the rank-≤10
locus (requiring KY ≤ 700) cannot be reached by first-order internal frame
deformation from BILR. The low-rank stratum at BILR is exactly 8-dimensional
(the torus that fixes R), matching the expected 8 = dim Stab(ω).

## Result 2: Klein V₄ and C₄ regular families are conjugacy-consistent with BILR

Over F₅, all 8 tested Klein V₄ points and all 8 tested C₄ regular points
match the BILR signature exactly:
- det restricted to each plane ≡ 0
- Killing conic determinant = -2 ≡ 3 (mod 5) on all 4 planes

These are PGL₃-invariant properties. Combined with the matching chart dimensions
(dim C_{PGL₃}(H) = 2 for both regular C₄ and diagonal V₄), this is consistent
with a single PGL₃-orbit of rank-4 exterior decompositions.

The basic invariants cannot prove conjugacy (they only fail to disprove it), but
no evidence of an inequivalent exterior component has been found.

## Implications for (10,4) cyclic rank-22

1. The trace-grading reduction (ker Ψ = 0 ⟹ (10,4) is the only rank-22 skeleton)
   is satisfied at BILR and at all extracted F₅ points of both symmetric families.

2. Within the BILR exterior orbit, the residual Waring problem is first-order
   blocked: BILR's displayed frame gives rank 11, and every non-trivial frame
   perturbation moves the KY rank upward (away from the ≤700 threshold).

3. The rank-≤10 locus, if nonempty, must be:
   - Disconnected from BILR within the frame family (a separate algebraic stratum)
   - Or on a different exterior component (no evidence found via symmetric ansätze)
   - Or a higher-order phenomenon invisible to the tangent

4. Direct stratification of the frame family by special loci (e.g., where two
   planes share a form direction, or unipotent one-parameter subgroups) is the
   natural next probe, using KY rank mod p as the detector.

## Scope

These results concern the BILR rank-4 exterior family and its internal-frame
residual problem. They do not exclude:
- Non-cyclic rank-22 decompositions (the independent-UV formulation remains open)
- The m ≥ 5 cyclic skeletons (7,5), (4,6), (1,7)
- Finite-field specific phenomena

## Files

- [ky_tangent_at_bilr.py](../code/ky_tangent_at_bilr.py): tangent computation
- [ky_tangent_at_bilr.json](../results/ky_tangent/ky_tangent_at_bilr.json): full results
- [klein_conjugacy_check.py](../../symmetry_and_residuals/code/klein_conjugacy_check.py): Klein vs BILR
- [klein_conjugacy_discriminants.json](../../symmetry_and_residuals/results/klein_conjugacy/klein_conjugacy_discriminants.json): conjugacy data
