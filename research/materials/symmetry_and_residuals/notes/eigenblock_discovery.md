# Eigenblock decomposition — superseded convention finding

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

**analysis correction.** The statement below that the BILR residual is not `Z₄`-invariant is false. The failure came from testing the wrong variable action for the packed Euclidean pairing `tr(L^T M)`. The coefficient cube action `L -> a₀ L a₀^{-1}` is dual to the variable action `M -> a₀^T M a₀^{-T}`. Under this action the residual is coefficientwise invariant, the residual changes by zero under invariant projection, and the corrected eigenblock pencil-conic instrument reproduces the two BILR size-4 cube orbits. See [z4_pairing_pencil.py](../code/z4_pairing_pencil.py) and [pairing_pencil_positive_control.json](../results/z4_pairing_pencil/pairing_pencil_positive_control.json).

The remaining text is preserved as a record of the error source, not as mathematical evidence.

## Block structure verified
The 43-dim Z₄-invariant cubic space splits into five character blocks:
- p³ (10), pq² (9), pzw (12), qz² (6), qw² (6) = 43 total
- H_W = p³+pq² = 19, off_W = pzw+qz²+qw² = 24

The block counts match analysis's off-W projection dimensions exactly.

## Critical discovery: the residual is NOT Z₄-invariant as a polynomial

The residual C = Σ_{i=0}^{10} l_i³ (sum of 11 BILR cube forms cubed) is NOT invariant
under the Z₄ action on the polynomial ring Sym³(gl₃).

**Verification**: evaluating the residual at a random point x and at Ad(a₀⁻¹)x gives
different values (4906 vs 16874 mod 65521).

**Reason**: the Z₄ symmetry acts on the TENSOR T = Σ u⊗v⊗w by Ad(g) on each factor.
The evaluation T(x,x,x) = tr(X³) IS invariant because tr((g⁻¹Xg)³) = tr(X³).
But individual cube contributions l_i(x)³ are NOT invariant polynomials: the form l_i
transforms under the DUAL action (Ad⁻¹)^T, and Ad(g)l_i = l_i (vector-fixed) does NOT
imply l_i(Ad(g⁻¹)x) = l_i(x).

## Consequence for the block extraction approach

The block decomposition of the residual INTO FIVE BLOCKS is meaningful only for the
Z₄-INVARIANT PROJECTION of the residual, not for the raw residual polynomial.

The invariant projection is:
  C_inv(y) = (1/4) Σ_{k=0}^3 C(D^{-k} y)

where D = diag(eigenvalues). This projects out the 43 invariant components.

The qz² and qw² blocks of C_inv have rank 2 (verified), and the pencil-conic
intersection procedure is algebraically sound for recovering the z-components
of the size-4 orbit forms.

However, the blocks of the RAW residual contain non-invariant contamination.
The correct computation requires either:
1. Explicitly computing C_inv = (1/4) Σ_k C(D^{-k} y), or equivalently
2. Computing the orbit-sum contribution of each Z₄ orbit of cubes (not individual cubes)

## Z₄ orbit structure of BILR cubes (verified)
- Orbit 0: {cube 0} — size 1 (fixed under Ad(a₀))
- Orbit 1: {cubes 1,2} — size 2
- Orbit 2: {cubes 3,4,5,6} — size 4
- Orbit 3: {cubes 7,8,9,10} — size 4

## Form transformation clarification
- change^T @ l_old: gives the form's polynomial coefficients in y-coordinates (CORRECT for evaluation)
- change_inv @ l_old: gives the form's eigenvector decomposition (CORRECT for eigenspace membership)
- These are DIFFERENT because the eigenbasis is not orthogonal

## Files
- Scripts: [eigenblock_decomposition.py](../code/eigenblock_decomposition.py), `eigenblock_pencil_conic.py`
- Data: [eigenblock_pencil_conic.json](../results/eigenblock/eigenblock_pencil_conic.json)
