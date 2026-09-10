# Characteristic-zero Z₄-equivariant exterior fiber analysis

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Key structural results

### Character-block decomposition of Ad(a₀) on gl₃
- a₀ = companion matrix of t³+t²+t+1 = (t+1)(t²+1), eigenvalues -1, ±i over char 0
- Ad(a₀) on gl₃ (9×9): eigenvalues 1(×3), -1(×2), ±i(×4 combined)
- V₁ = centralizer = span{I, a₀, a₀²} (dim 3)
- V₋₁ (dim 2), V₊ = ker(Ad²+I) (dim 4)
- Verified mod 65521 and 32003

### Exterior equation
The correct equation (fixing the normalization from analysis) is:
$$S_4 \cdot (A \wedge B \wedge C) = \omega$$
where S₄ = I + Λ³(Ad) + Λ³(Ad)² + Λ³(Ad)³ is the Z₄ sum operator
and ω is the Cartan 3-form tr(X[Y,Z]) in Λ³(gl₃), with 8 nonzero entries (values ±1).

- ω is Z₄-invariant: verified
- ι_tr(ω) = 0: verified (ω ∈ Λ³(sl₃))
- BILR orbit representatives ARE Z₄ images of rep0 (direct match for all k)
- S₄·w₀ = orbit_sum = ω: exact match (not 3ω as previously noted)

### Z₄-invariant dimension
- dim(Λ³(gl₃)^{Z₄}) = 20, decomposing as 14 (Λ³(sl₃)^{Z₄}) + 6 (I∧Λ²(sl₃)^{Z₄})
- For traceless A,B,C ∈ sl₃: the 6 trace equations are auto-satisfied
- Effective system: 14 equations in 24 traceless unknowns

### Fiber dimension at BILR
- sl₃-restricted Jacobian rank: 14 (mod 65521 and 32003)
- Full gl₃ Jacobian rank: 17 = 14 (sl₃) + 3 (trace)
- **Fiber dimension: 10** (= 24 - 14 in sl₃)
- Stabilizer: 2-dimensional (from a₀ and a₀² centralizer actions, X=I gives zero direction)
- **Effective fiber dimension: 8** (mod stabilizer)

### Kuranishi second-order analysis
All 6 quadratic obstruction forms Q₀,...,Q₅: rank 0.
Total rank of all 6 forms in 55 monomials: 0.
**The fiber is smooth at BILR with dimension 10 (8 effective).**
Verified at both p=65521 and p=32003.

### correction: tangent kernel is symmetry-generated, not an affine fiber
The analysis interpretation that the exterior fiber is an affine linear subspace was too strong and is superseded by [z4_symmetry_kernel_and_residual.md](z4_symmetry_kernel_and_residual.md). Exact rank computations show that the 10-dimensional kernel is precisely the span of 8 internal `SL_3` recombination directions `(A,B,C) -> (A,B,C)M` and 2 nontrivial centralizer-conjugation directions for `a₀`. These directions integrate through group actions: internal recombination scales the wedge by `det M`, so it preserves `S₄(A∧B∧C)=ω` exactly only for `M ∈ SL_3`, while centralizer conjugation preserves the equation by finite conjugation. A one-ARTIFACT linear tangent move preserves the equation only in special cases such as `det(I+N)=1`; the pattern of basis directions that happened to be exact at `t=1` is not intrinsic.

## Implications for rank-22

The live `Z₄` single-free-orbit exterior component is the explicit 8-parameter internal `SL_3` orbit modulo the 2-dimensional centralizer action, not a new generic 10-dimensional affine family. Centralizer conjugation only changes variables in the residual cubic, so Waring rank is invariant along it. The rank-22 question in this component is therefore whether the residual cubic
`tr(X^3) - 3 Σ_{k=0}^3 (Ad(a₀)^k A_M)(Ad(a₀)^k B_M)(Ad(a₀)^k C_M)`
for `M ∈ SL_3` can be written as ten `Z₄`-stable cubes. At `M=I` this residual is exactly the eleven BILR cubes and has Koszul--Young rank 722, ruling out ten cubes only at that point. Global resolution requires exact apolarity/orbit-cube equations, not finite Koszul sampling.

## Scripts and data
- [z4_char0_exterior_model.py](../code/z4_char0_exterior_model.py): basic structure verification
- [kuranishi_obstruction-1fe8d1d04b.py](../../quotient_cores/code/kuranishi_obstruction-1fe8d1d04b.py): Kuranishi analysis
- [fiber_exploration.py](../../quotient_cores/code/fiber_exploration.py): flat fiber verification + residual analysis
- [z4_exterior_model_basic.json](../results/z4_char0_model/z4_exterior_model_basic.json): basic results
- [kuranishi_obstruction.json](../results/z4_char0_model/kuranishi_obstruction.json): Kuranishi results
- [fiber_exploration.json](../results/z4_char0_model/fiber_exploration.json): fiber point residuals

## Next steps
1. Import and run the analysis Koszul-Young 1134×1134 flattening at multiple fiber points
2. Since fiber is linear, can parametrize Koszul matrix as K(t) = K₀ + Σ tᵢ Kᵢ 
3. The drop condition is that certain (701×701) minors vanish — a polynomial in t₁,...,t₁₀
4. Alternatively use apolarity: check if residual - l³ has rank ≤ 9 for some l
5. The catalecticant (9×45, rank ≤ 9) is NOT discriminating for 10 vs 11 cubes;
   the unfolding rank (81×9) or the full 1134×1134 flattening is needed
