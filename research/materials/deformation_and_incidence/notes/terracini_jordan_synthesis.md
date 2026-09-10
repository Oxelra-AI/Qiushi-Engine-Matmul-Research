# Terracini conormal defect and Jordan-type classification

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Summary of corrected results

### 1. Characteristic-zero anchoring

The GL₃³ sandwich action on the 3×3 matrix multiplication tensor T₃₃₃ has the following
verified structure:

- The infinitesimal stabilizer of T₃₃₃ is the **full** gl₃³ (dimension 27). Every
  basis element of gl₃³ preserves T₃₃₃ as a tensor (orbit tangent = 0).
- The embedding gl₃³ → gl₉³ via the Kronecker-difference formulas has rank **26**
  over all tested primes (5, 7, 11, 13, 65521). By the standard modular argument,
  this rank is 26 over Q. The 1-dimensional kernel is the central direction
  (P₀, Q₀, R₀) = (cI, cI, cI).
- The 26 independent stabilizer directions in gl₉³ are therefore genuine characteristic-zero
  objects.

### 2. Corrected Kronecker convention (row-major QMM)

The correct formulas for the 9×9 factor actions under QMM's row-major vectorization are:

    dg₁ = P₀^T ⊗ I₃ - I₃ ⊗ Q₀
    dg₂ = Q₀^T ⊗ I₃ - I₃ ⊗ R₀
    dg₃ = I₃ ⊗ R₀^T - P₀ ⊗ I₃

The analysis script `stabilizer_embedding_9x9` used column-major convention
(I⊗P^T - Q⊗I instead of P^T⊗I - I⊗Q), which caused J*stab_cols to have rank 16
instead of the correct 0. This is now fixed in `terracini_jordan.py`.

### 3. Verified Terracini defect at cn122

At the rank-23 scheme cn122 over F₆₅₅₂₁:

| Quantity | Value |
|----------|-------|
| Brent Jacobian rank | 527 / 621 |
| Kernel dimension | 94 |
| Scaling subspace rank | 46 |
| Stabilizer parameter rank (from 27 generators) | 26 |
| J × stab_cols rank (must be 0) | **0** ✓ |
| Combined scaling + stabilizer rank in kernel | 70 |
| Extra stab directions beyond scaling | **24** |
| Extra kernel beyond stab + scaling | 24 (decomposition-specific) |

This confirms:
- All 26 stabilizer directions are rigorously in the Brent kernel
- The stabilizer contributes exactly 24 kernel dimensions beyond the 2 central scalings
- cn122 has an additional 24 kernel dimensions from decomposition-specific symmetry
  (total kernel = 94 = 70 + 24)

### 4. Forced Terracini defect for rank-22 decomposition of T₃₃₃

For **any** rank-22 decomposition of T₃₃₃ with full factor spans (all three spans = K⁹):

| Quantity | Generic r=22 | Forced at T₃₃₃ | Defect |
|----------|-------------|-----------------|--------|
| Parameter dimension | 594 | 594 | 0 |
| Term scaling kernel | 44 | 44 | 0 |
| Stabilizer kernel (new) | 0 | 26 | +26 |
| Central overlap | 0 | 2 | +2 |
| Total kernel lower bound | 44 | 68 | +24 |
| Jacobian rank upper bound | 550 | 526 | −24 |
| Conormal dimension lower bound | 179 | 203 | +24 |

The 24 extra conormal directions come from the 24 noncentral stabilizer directions
(26 total minus 2 central) that are in the Brent kernel but not in the scaling subspace.
Each creates a linear relation among the 22 Segre tangent space contributions:

    Σᵢ [(dg₁ uᵢ) ⊗ vᵢ ⊗ wᵢ + uᵢ ⊗ (dg₂ vᵢ) ⊗ wᵢ + uᵢ ⊗ vᵢ ⊗ (dg₃ wᵢ)] = 0

These relations reduce the Terracini tangent dimension by exactly 24 (for full-span decompositions).

### 5. Jordan-type analysis of stabilizer elements

For the stabilizer parametrized by (P₀, Q₀, R₀) ∈ gl₃:

**Generic case (P₀, Q₀, R₀ all diagonalizable with distinct eigenvalues):**
- dg₁ has 9 distinct eigenvalues {pₐ − q_b}, all with geometric multiplicity 1
- dg₂ has 9 distinct eigenvalues {qₐ − r_b}
- dg₃ has 9 distinct eigenvalues {rₐ − p_b}
- All three are diagonalizable (semisimple)
- Each u_i is a rank-1 matrix: u_i = pₐ q_b^T (eigenvectors of P₀^T and Q₀)
- Similarly v_i = q_c' r_d^T, w_i = p_f'' r_e'^T

**Non-diagonalizable case (P₀ with Jordan block of size 2):**
- Three eigenvalues of dg₁ get algebraic multiplicity 2 but geometric multiplicity 1
- Total independent eigenvectors: 6 (not 9)
- dg₁ is NOT diagonalizable → cannot have 9 independent eigenvectors
- A full-span rank-22 decomposition (u-span = K⁹) requires 9 independent u-eigenvectors
- Therefore: non-semisimple stabilizer elements **cannot** act projectively on
  all summands of a full-span decomposition

### 6. Eigenvalue balance constraint

At a stabilizer-compatible rank-22 decomposition (generic semisimple stabilizer):
- Each term has eigenvalue indices (a_i, b_i, c_i, d_i, e_i, f_i)
- Eigenvalue balance: (p_{a_i} - q_{b_i}) + (q_{c_i} - r_{d_i}) + (r_{e_i} - p_{f_i}) = 0
- Full span requires all 9 eigenvalue pairs occupied in each factor
- 22 terms with 9 pairs: multiplicity vector sums to 22 with each ≥ 1

The matrix multiplication structure constrains which index tuples are allowed.
In the diagonal eigenbasis, the natural 27-term decomposition has 27 elementary tensors
with indices (a_i, b_i, c_i, d_i, e_i, f_i) = (p, q, q, s, s, p).

### 7. What this does NOT prove

- The Terracini defect is a necessary condition, not a proof of rank ≥ 23.
- The 24 extra conormal directions constrain the decomposition structure but do not
  by themselves show the constrained variety is empty.
- The Jordan type classification constrains which stabilizer elements can act
  projectively, but the full stabilizer analysis (including non-projective actions)
  is not complete.
- Lower UV-rank strata remain untreated.
- Non-transverse alignment strata (where stabilizer-scaling intersection exceeds 2)
  require separate analysis. The 27-term decomposition shows this intersection can
  reach dimension 8.

## Files

- [terracini_jordan.py](../code/terracini_jordan.py): comprehensive script with corrected Kronecker convention
- [terracini_jordan.json](../results/terracini_jordan/terracini_jordan.json): all numerical results
- This synthesis note

## Next work

The two branches from the review:

**Conormal branch**: Express the 24 extra conormal directions without choosing a chart.
The current formulation already does this (the stabilizer relations are in tensor-factor
language, not chart coordinates). The next ARTIFACT is to show that these directions, combined
with the generic conormal conditions, create an incompatible system — or to identify what
additional algebraic structure is needed.

**Jordan classification branch**: Classify all noncentral stabilizer orbits by Jordan type
and determine which can act on a rank-22 decomposition. The semisimple case forces rank-1
matrix factors in the eigenbasis. The key open question: in the eigenbasis, does the
matrix multiplication tensor require more than 22 rank-1 matrix factor terms? This is
basis-independent (equivalent to the original rank question), so the eigenbasis analysis
alone cannot resolve it — but the structural constraints may combine with other invariants.

**Integration with related analysis finite-field branch**: related analysis has all 69 exact-18 high-pair orbits
CP-SAT INFEASIBLE with verified DRAT leaves through index 7+ (batch 7-68 in progress).
Rep10 k=1..17 is CP-SAT INFEASIBLE but DIMACS/DRAT too large (6.6M vars). Rep2 and
rep16 still produce LUT-violating candidates or UNKNOWN. The finite-field branch needs
continued DRAT leaf production and better compression for the remaining mixed cases.
