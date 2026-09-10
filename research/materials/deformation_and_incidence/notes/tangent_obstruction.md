# Tangent Space Decomposition and Second-Order Obstruction Analysis

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Summary of key results

All three independently verified rank-23 decompositions of T_{3,3,3} exhibit
**complete second-order obstruction** in every non-symmetry deformation direction.

## Data table

| Scheme | Jacobian rk | Kernel dim | Symmetry dim | Residual dim | Obstructed | Cross-terms |
|--------|-------------|-----------|-------------|-------------|-----------|-------------|
| cn122 (verified, integer) | 527/621 | 94 | 71 | **23** | 23/23 | 45/45 |
| serendipitous_8d34 (verified, ternary) | 531/621 | 90 | 71 | **19** | 19/19 | 45/45 |
| naive_c88 (verified, ternary) | 528/621 | 93 | 71 | **22** | 22/22 | 45/45 |

## What the analysis computes

1. **Jacobian kernel**: For a rank-r decomposition T = Σ u_i⊗v_i⊗w_i, the Jacobian
   J of the map (u_1,...,w_r) → Σ u_i⊗v_i⊗w_i evaluated at the decomposition point.
   Kernel directions preserve T at first order.

2. **Rescaling subspace (dim = 2r = 46)**: Per-term torus (λ,μ) acting as
   (λu_i, μv_i, w_i/(λμ)). All 46 directions are confirmed in the kernel.

3. **Stabilizer subspace (dim = 26/27)**: GL_3 × GL_3 × GL_3 "sandwich" action on
   decomposition terms: (P,Q,R) sends U_i → PU_iQ^{-1}, V_i → QV_iR^{-1}, W_i → PW_iR^{-1}.
   The missing 1 direction (out of 27) is the scalar (dP=tI, dQ=0, dR=-tI) which
   changes the tensor by 4t·T ≠ 0, explained by the formula:
   (aI, bI, cI) gives J·d = (2a-2c)T. Only directions with a=c preserve T.

4. **Combined symmetry dimension = 71**: The 46 rescaling + 26 stabilizer directions
   span 71-dimensional subspace of the kernel (some small overlap). This is constant
   across all three schemes — a structural invariant.

5. **Residual deformation dimensions**: cn122: 23, serendipitous: 19, naive_c88: 22.
   These vary by decomposition family (expected from algebraic geometry).

6. **Pairing rank-defect test**: ALL residual directions can drop all three two-factor
   pairing ranks (uv, uw, vw). This is necessary for rank shortening.

7. **Second-order obstruction (the main result)**: For each residual direction d,
   the quadratic Brent error Q(d,d) is NOT in the image of J. That is:

   Q(d,d)_{abc} = Σ_i [δu_i[a]δv_i[b]w_i[c] + δu_i[a]v_i[b]δw_i[c] + u_i[a]δv_i[b]δw_i[c]]

   has a component in coker(J) (the "obstruction cokernel") that is nonzero.

   All 23+19+22 = 64 residual directions across 3 families are obstructed.
   All sampled cross-terms Q(d_i, d_j) are also obstructed.

## Mathematical interpretation

The variety σ_{23}(Seg(P^8 × P^8 × P^8)) of rank-≤23 tensors in C^{729} has
"infinitesimally rigid" decompositions at T_{3,3,3}: no smooth path of rank-23
decompositions can begin at these points and reduce the number of terms.

**The obstruction cokernel dimension** is:
- coker(J) has dim = 729 - 527 = 202 for cn122 (and 198, 201 for the others)
- The obstruction maps Q(d,d) project nontrivially into this 200-dimensional space
  for every residual direction.

## What this does NOT prove

1. Rank-22 via non-smooth/algebraic paths through singularities
2. Coverage of ALL rank-23 decompositions (only three tested)
3. Exact (rational) arithmetic verification (uses float64)
4. Existence/nonexistence of rank-22 decompositions not connected to rank-23 families

## What this provides toward rank-23 optimality

- Strong numerical evidence that the rank-23 variety near T_{3,3,3} is
  "second-order locked": rank-23 decompositions cannot smoothly deform toward rank-22.
- If the obstruction map Q: ker(J)/symmetry → coker(J) could be shown to be
  surjective or to have full image dimension algebraically, this would contribute
  to a lower-bound proof strategy.
- The constant symmetry dimension 71 across families suggests a universal structure.

## Files produced

- `data/cn122_r23_reproduce/tangent_analysis.json` (partial, JSON bug)
- [second_order_obstruction.json](../../exact_baselines/results/cn122_r23_reproduce/second_order_obstruction.json)
- [serendipitous_8d34_obstruction.json](../../exact_baselines/results/fmm_r23_schemes/serendipitous_8d34_obstruction.json)
- [naive_c88_obstruction.json](../../exact_baselines/results/fmm_r23_schemes/naive_c88_obstruction.json)
- [serendipitous_8d34_invariants.json](../../exact_baselines/results/fmm_r23_schemes/serendipitous_8d34_invariants.json)
- [naive_c88_invariants.json](../../exact_baselines/results/fmm_r23_schemes/naive_c88_invariants.json)

## Invariant comparison across families (over Q)

cn122: sorted_rank_types = {(1,1,1):13, (1,1,2):6, (2,2,2):4}, Jacobian rk=527
serendipitous_8d34: sorted_rank_types = {(1,1,1):13, (1,1,2):6, (2,2,2):4}, Jacobian rk=531
naive_c88: sorted_rank_types = {(1,1,1):12, (1,1,2):3, (1,1,3):3, (1,2,2):1, (2,2,2):4}, Jacobian rk=528

cn122 and serendipitous share rank-type profile; naive_c88 is a different family.
All have full factor spans (rank 9) and full pairing ranks (23) over Q.

## Converter note

FMM JSON w-vectors use column-major C indexing (i.e., C^T convention):
  w_FMM[3k+i] = coefficient for C_{ik}
QMM verifier expects row-major: w_QMM[3i+k] = coefficient for C_{ik}
Fix: transpose w as 3×3 matrix when converting.

## Next research directions

1. **Exact verification**: Redo key computations (Jacobian rank, obstruction) with
   exact rational arithmetic to eliminate floating-point concern.
2. **Algebraic obstruction map**: Compute the image of Q in coker(J) as an algebraic
   variety to understand whether obstruction is "generic" or "special."
3. **More families**: Convert and test additional rank-23 schemes from the corpus.
4. **Symbolic second-order**: Use Wolfram/sympy for exact obstruction computation.
5. **Connection to finite-field lower bounds**: The obstruction cokernel may relate to
   the constrained-tensor lower-bound certificates that research_record is studying.
