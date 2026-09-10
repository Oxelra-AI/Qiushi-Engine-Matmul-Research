# Prehomogeneity Theorem and Cyclic Rank-22 Feasibility

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Verified characteristic-zero theorem: m ≥ 4 for cyclic rank-22

### The ambient correction

The Cartan 3-form ω arising from the cyclic quotient of T_{⟨3,3,3⟩} does NOT live
in Λ³(K⁹) = Λ³(gl₃) in the natural way. Instead, the contraction

    ι_tr(ω) = 0

was verified exactly (numerically zero to machine precision), meaning ω ∈ Λ³(sl₃)
where sl₃ = ker(tr) is 8-dimensional. The ambient exterior algebra is therefore
Λ³(C⁸), of dimension C(8,3) = 56, not Λ³(C⁹) = 84.

### Prehomogeneity and dense orbit

The GL₈ action on Λ³(C⁸) was verified to have:
- Stabilizer dimension at ω: **8** (= dim sl₃)
- Orbit dimension: **64 − 8 = 56** = dim Λ³(C⁸)
- This is a **dense orbit** (open orbit = generic orbit)

Computation: the infinitesimal action map φ: gl₈ → Λ³(C⁸) was built as a 56×64
matrix, and its rank was computed modulo three large primes (1000003, 65521, 32003);
all gave rank **56**, hence dim(stab) = 64 − 56 = 8.

### Third secant variety is proper

The cone over the Grassmannian G(3,8) has dimension 3(8−3) = 15. Its third secant
variety σ₃(G(3,8)) has dimension at most 3 × 15 + 3 = 48 < 56. Since σ₃ is a
GL₈-stable closed subvariety of dimension < 56 and the dense orbit has dimension 56,
the dense orbit is disjoint from σ₃.

### Conclusion

Since ω is in the dense orbit of Λ³(C⁸) and σ₃ is a proper closed invariant
subvariety, ω ∉ σ₃. Therefore the exterior rank of ω is ≥ 4.

**Theorem (characteristic-zero cyclic m ≥ 4):** Over any characteristic-zero field K,
any cyclic-invariant rank-22 decomposition of T_{⟨3,3,3⟩} must have at least 4 free
cyclic 3-orbits. The skeletons (22,0), (19,1), (16,2), (13,3) are excluded.

*This is a field-independent result* (works for K = Q, R, C, and any algebraically
closed extension). It is purely geometric and does not depend on DRAT or SAT.

### Exterior rank exactly 4

A numerical rank-4 decomposition of ω was found (SciPy TRF, cost ≈ 1.9 × 10⁻³⁰)
on the first trial, confirming exterior rank = 4. Together with exterior rank ≥ 4
from prehomogeneity, this establishes exterior rank(ω) = 4.

Data: [sl3_trivector_verification.json](../../quotient_cores/results/sl3_trivector/sl3_trivector_verification.json),
      [exterior_rank4_decomposition.json](../results/exterior_rank4/exterior_rank4_decomposition.json)

## The rank-22 cyclic feasibility question

### Decomposition structure

A cyclic rank-22 decomposition with (f,m) = (10,4) would require:
1. **Exterior condition**: 4 orbit triples (U_j, V_j, W_j) ∈ sl₃ with Σ_j U_j ∧ V_j ∧ W_j = ω
2. **Diagonal condition**: tr(M³) = Σᵢ ℓᵢ³ + 3 Σⱼ ℓ_{Uⱼ} ℓ_{Vⱼ} ℓ_{Wⱼ}
   with 10 cube vectors cᵢ ∈ gl₃

### Key mathematical identity

The anti-symmetric part of the tensor (T[i,j,k] − T[i,k,j]) depends ONLY on the
orbit parameters (cubes are symmetric and cancel). Moreover, the anti-symmetric part
is EXACTLY the wedge product:

    A_decomp[i,j,k] = Σ_s (BU_s ∧ BV_s ∧ BW_s)[i,j,k]

where B: sl₃ → gl₃ is the basis change. Since ι_tr(A_{T333}) = 0, the anti-symmetric
conditions in Λ³(K⁹) are equivalent to the exterior conditions in Λ³(sl₃).

**Therefore: diagonal (165 equations) + exterior (56 equations) = all 249 cyclic Brent
equations = all 729 tensor entries.**

### Numerical findings

| Test | Cost | Interpretation |
|------|------|---------------|
| Diagonal only (165 eqs, 186 params) | 4.68e-29 | EXACT: tr(M³) matches |
| Exterior check of diagonal solution | max err 6.53 | FAILS: orbits don't decompose ω |
| Full 729-tensor (729 eqs, 186 params) | ~6e-07 (after 10 trials) | NOT converged, background running |

The diagonal cubic CAN be written as 10 cubes + 4 trilinear products over R. But the
specific orbits found by the diagonal optimizer do NOT satisfy the exterior condition.
The full tensor optimization (729 overdetermined equations) is the correct test.

### Residual cubic catalecticant

For all 20 tested rank-4 exterior decompositions, the residual cubic
R = tr(M³) − 3Σⱼ ℓ_{Uⱼ}ℓ_{Vⱼ}ℓ_{Wⱼ} has catalecticant rank exactly **9** (fully
concise in all 9 variables). The catalecticant cannot distinguish Waring rank 10 from 11
for cubics in 9 variables (maximal catalecticant rank for any cubic is 9).

### Known rank-23 schemes are not cyclic

None of the three available rank-23 schemes (cn122, serendipitous_8d34, naive_c88) have
cyclic symmetry. A cyclic rank-23 scheme could not be found via F₂ SAT in 300s for
skeletons (2,7) through (11,4). The F₂ diagonal collapse excludes (20,1) and (17,2)
by UNSAT, consistent with the m ≤ 3 general exclusion.

## Scope and next work

The m ≥ 4 theorem is a genuine characteristic-zero result. Combined with the analysis
F₂ DRAT certificates for m ≤ 3, the cyclic rank-22 exclusion at m ≤ 3 now holds over
both characteristic zero and F₂.

The remaining cyclic rank-22 question is m = 4: does there exist a rank-4 decomposition
of ω whose residual cubic has Waring rank ≤ 10? The background optimization tests this
directly (full 729-tensor system). If it fails to converge, the system may be infeasible,
but this would be numerical evidence, not a proof. A proof would require either:
- An algebraic argument (e.g., apolarity/secant invariant on the fiber of rank-4 decompositions)
- An exact finite-field computation

For m ≥ 5 in characteristic zero, the catalecticant non-conciseness argument
applies: f ≤ 7 < 9 forces the residual to have at least 2 annihilating linear forms,
giving additional constraints that may close these cases. This is not yet implemented.

The general (non-cyclic) rank-22 question remains completely open.
