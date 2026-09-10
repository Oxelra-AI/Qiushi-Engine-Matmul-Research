# Strassen/Hessian commutator theorem — corrected scope through analysis

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## What IS rigorously proved

### 1. The Strassen/Hessian pointwise commutator bound on gl₃ (algebraic theorem)
For k cubes on gl₃ (dim 9) with quadratic moment Σ wᵢ μᵢ⊗μᵢ = K (trace form,
rank 9), the Hessian endomorphism H(X) = (1/6) Hess_R(X) K⁻¹ satisfies:
  rank([H(X), H(Y)]) ≤ 2·max(0, k − 9)   for all X, Y.

Proof for k=9: In the M-basis (M = matrix of μᵢ rows, 9×9 invertible),
H(X) = S · diag(y) · S⁻¹ where S columns are the μᵢ and y = Mx. Diagonal
matrices commute, so [H(X), H(Y)] = 0. ✓

Proof for k=10: Define u(y) = w₁₀ diag(α)((α·y)1 − y) where μ₁₀ = Sα.
In the S-basis, H(X) = diag(y) + u(y)r^T where r^T = α^T G⁻¹ and G = W + w₁₀ αα^T.
The commutator column space ⊆ span(u(y), u(z)) by the identity:
  y∘u(z) − z∘u(y) = −(α·z)u(y) + (α·y)u(z).
Hence rank ≤ 2. ✓

**review correction:** The u(y)ⱼ formula in the original note had an error:
  WRONG: u(y)ⱼ = w₁₀ αⱼ Σ_{m≠j} αₘ yₘ
  RIGHT: u(y)ⱼ = w₁₀ αⱼ (Σₘ αₘ yₘ − yⱼ) = w₁₀ αⱼ (α·y − yⱼ)
These differ by w₁₀ αⱼ(αⱼ−1)yⱼ. The key identity still holds with the correct
formula because it depends only on u(y) = w₁₀ diag(α)((α·y)1 − y). ✓

### 2. BILR certificate (computational theorem)
The BILR residual cubic on gl₃ has Waring rank ≥ 11, proved by:
- Koszul–Young flattening rank 722 > 700 = 10·70 (analysis)
- Strassen/Hessian commutator: nonzero commutator certificate (analysis), later refined to the exact Pfaffian scalar Φ_true=-80000 and 4×4-Pfaffian/common-pencil certificates (earlier analysis).

Combined with the 11-cube decomposition, BILR Waring rank = 11 exactly. ✓

**review insight:** K = (1/6) Hess_R(I) is an INTRINSIC property of R, not an
additional assumption. For any Waring decomposition R = Σ ρᵢ ℓᵢ³ with
ℓᵢ(I) ≠ 0, setting μᵢ = ℓᵢ/ℓᵢ(I) and wᵢ = ρᵢ ℓᵢ(I)³ gives both
R = Σ wᵢ μᵢ³ AND K = Σ wᵢ μᵢ μᵢ^T. So the Jennrich bound is intrinsic
to R, and applies to ANY Waring decomposition of R with at most 10 cubes. ✓

### 3. Pure cyclic status under ker Ψ = 0
Over characteristic zero, pure cyclic rank-22 with traceless free orbits:
- m ≤ 3: excluded by Cartan 3-form rank ≥ 4 (analysis) ✓
- m ≥ 5 under ker Ψ = 0: trace grading forces f ≥ 8, hence m ≤ 4 (analysis) ✓
- the fixed BILR residual, not the whole `(10,4)` branch, is excluded from 10 cubes by the commutator/Koszul certificates ✓

The `(10,4)` cyclic branch is still open. earlier analysis showed why the old sentence "BILR orbit excluded" was too strong: internal determinant-one frame changes preserve the exterior trivectors but change the residual cubic, and the reduced-pair orthogonal-complement test vanishes at the BILR identity frame.

## What is NOT yet proved

### The universal (10,4) exclusion
The gap identified by review: the exterior decomposition (4 planes Pⱼ in sl₃)
does NOT determine the residual cubic. Internal frame changes (U,V,W) → (AU,AV,AW)
with A ∈ SL₃ preserve the decomposable trivector U∧V∧W but change the symmetric
product UVW. Each plane admits 8-dimensional SL₃ freedom, giving 4×8 = 32
internal parameters. The residual R varies along this 32-dimensional family.

The BILR certificate shows R_BILR has Waring rank 11. But:
- Other frame choices within the same exterior decomposition give different R
- Other rank-4 exterior decompositions of ω might also exist
- The Jennrich commutator rank ≥ 3 is an OPEN condition on R's coefficients
- It could fail on a proper closed subset of the parameter space

### Remaining research to close the gap

**Correct polynomial method after analysis:** one scalar Φ or one minor at one pair X,Y is not enough, and a nonconstant polynomial on the irreducible frame space necessarily has zeros over an algebraic closure. The exact equations for a rank-10 residual are the 4×4 Pfaffians of Ω=K[H_X,H_Y] for all relevant pairs, plus the stronger common-pencil equations Ω(X,Y)∧Ω(X,Z)=0 forced by the k=n+1 normal form. analysis calibrated the reduced split {i,j}|{k,l}: all six BILR identity-frame reduced commutators are zero, so that cheap two-frame route is inactive at BILR.

**Approach B (invariant method):** Show that the Waring rank of the residual is
an invariant of the full decomposition (not just the exterior part), and use the
full 729 Brent equations to constrain the frame choices.

**Approach C (gl₃ moment independence):** The quadratic moment K = (1/6)Hess_R(I)
is determined by R alone. If we can show that K = tr(XY) (the trace form on gl₃)
for ALL valid (10,4) decompositions, then the Jennrich bound applies to all of them.
But whether K = tr(XY) holds generally depends on the trace structure of the cubes.

## Files
- [hessian_gl3_instrument.py](../code/hessian_gl3_instrument.py): gl₃ commutator
- [jennrich_integer_cert.py](../code/jennrich_integer_cert.py): integer certificate
- [jennrich_integer_certificate.json](../results/hessian_commutator/jennrich_integer_certificate.json): certificate
- [jennrich_and_10_4_exclusion.md](jennrich_and_10_4_exclusion.md): original synthesis (superseded)
- This file: corrected scope after review verification
