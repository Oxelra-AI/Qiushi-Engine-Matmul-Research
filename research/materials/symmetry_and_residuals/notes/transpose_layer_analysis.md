# Transpose layer τ(X,Y,Z) = (X^T, Z^T, Y^T)

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## 1. The involution τ

Define τ on M_3^⊗3 by τ(u⊗v⊗w) = u^T⊗w^T⊗v^T. This preserves T_{333}:
tr(X^T Z^T Y^T) = tr((YZX)^T) = tr(YZX) = tr(XYZ). ✓

**τ-invariant dimension:** τ has 27 fixed basis elements (i=j, k=n, l=m), giving
dim(inv) = (729+27)/2 = 378.

## 2. τ-symmetry of known rank-23 schemes

| Scheme         | τ-invariant | Fixed (f) | Free orbits (m) | N=f+m | Unmatched |
|----------------|-------------|-----------|------------------|-------|-----------|
| naive_27       | YES         | 9         | 9                | 18    | 0         |
| cn122          | NO          | 1         | 0                | 1     | 22        |
| serendipitous  | NO          | 0         | 0                | 0     | 23        |
| naive_c88      | NO          | 0         | 0                | 0     | 23        |
| BILR_Z4xZ3     | NO          | 1         | 0                | 1     | 22        |

Only the naive 27-term algorithm is τ-invariant (in its standard form).
The rank-23 schemes may be conjugable to a τ-compatible form, but this would
require a suitable (P,Q,R) conjugation — not checked yet.

## 3. H^1 conjugacy lemmas

### Z_3 (cyclic rotation): H^1(Z_3, PGL_3^3) = 1

analysis proved this computationally. The abstract proof: the Z_3 action
on PGL_3^3 by cyclic permutation makes PGL_3^3 a coinduced module
(isomorphic to Ind^{Z_3}_1(PGL_3)), so H^1 vanishes by Shapiro's lemma.
Constructively: if σ is cyclic rotation and g = (P,Q,R) satisfies
(σg)^3 = 1, define h = (Id, P, PσP). Then h^{-1}·g·σ(h) = 1,
exhibiting g as a coboundary.

**Consequence:** Every order-3 cyclic-type symmetry of T_{333} is
sandwich-conjugate to the standard cyclic rotation. The Cartan and
trace-grading theorems cover ALL cyclic classes, not just the standard one.

### Z_2 (transpose): H^1(Z_2, PGL_3^3) classification

τ acts on the sandwich group G = PGL_3^3 by (P,Q,R) ↦ (P^{-T}, R^{-T}, Q^{-T}).
A τ-cocycle satisfies g·τ(g) = 1:
- First factor: P·P^{-T} = I ⟹ P^T P = I (P is orthogonal/symplectic)
- Second + third: Q·R^{-T} = I ⟹ R = Q^T

A coboundary from h = (A,B,C) modifies the cocycle:
(A,B,C)^{-1}·(P,Q,Q^T)·(A^{-T},C^{-T},B^{-T}) = (A^{-1}PA^{-T}, B^{-1}QC^{-T}, C^{-1}Q^TB^{-T})

So two cocycles (P₁,Q₁,Q₁^T) and (P₂,Q₂,Q₂^T) are cohomologous iff
there exist A,B,C with A^{-1}P₁A^{-T} = P₂ (equivalence of bilinear forms)
and B^{-1}Q₁C^{-T} = Q₂ (GL×GL equivalence).

Over C (or any algebraically closed field, char ≠ 2):
- Nondegenerate symmetric bilinear forms on K^3 have one equivalence class
- The Q-part is unconstrained (any invertible Q works, and C = (Q₂^{-1}B^{-1}Q₁)^T)

So H^1(Z_2, PGL_3^3) ≅ H^1(Z_2, PGL_3) = {bilinear forms up to equiv} = 1 class
over algebraically closed fields. Over ℝ, there are two classes (positive definite
and indefinite), giving at most 2 transpose-type symmetries.

**Consequence:** Over C, the transpose involution τ is essentially unique up
to sandwich conjugacy. The τ-invariant decomposition space is canonical.

## 4. Fixed-locus Gram reduction

On the τ-fixed locus X = S (symmetric), Z = Y^T:
- Target: tr(S·Y·Y^T) = Σ_{j,k} S_{jk} G_{jk}(Y), with G_{jk} = Σ_l Y_{jl}Y_{kl}
- Fixed term (u sym, w=v^T): contributes ℓ_u(S) · [ℓ_v(Y)]²
- Free orbit pair: contributes 2·ℓ_u^{sym}(S) · ℓ_v(Y) · ℓ_{w^T}(Y)

The 6-dimensional Gram space {G_{jk}} ⊂ Sym²(K^9) must lie in the span
of the f squares + m products = N reducible quadrics, weighted by the
u-coefficients in Sym₃(K).

Let \(N_G\) denote the minimum number of reducible quadrics in \(\operatorname{Sym}^2(K^9)\) whose span contains the Gram space. analysis produced a polarization construction with \(N_G\le 12\) over fields containing \(\sqrt{-1}\), and the naive axis-products give \(N_G\le18\). analysis corrected the interpretation: failed random trials and essentiality of the twelve products inside that one construction do not prove \(N_G\ge12\). The all-free skeleton \((f,m)=(0,11)\) therefore is not excluded by the current Gram evidence.

For rank-22 with τ-symmetry: \(f+2m=22\), and the Gram sector sees \(N=f+m=11+f/2\) products. Any true lower bound on \(N_G\) would remove skeletons with \(N<N_G\), but no such lower bound above 6 has been established here.

## 5. Complementary conditions

The τ-invariant Brent space has dimension 378. The fixed-locus cubics
(Σ S_{jk} G_{jk}(Y) = parametrized by S ∈ Sym_3) give dim(Sym_3 ⊗ Sym²(K^9))
projected to the relevant space = 6 × 45 = 270 equations. The remaining
~108 equations are the "anti-invariant" or "complementary" conditions.

These arise from the τ-odd part: the equations τ(T) - T = 0 restricted
to the antisymmetric-in-(Y,Z) or asymmetric-in-X parts.

## 6. Rank-22 τ-skeletons

| f  | m  | N=f+m | r=f+2m | Notes                              |
|----|-----|-------|--------|------------------------------------|
| 0  | 11  | 11    | 22     | All-free, most economical          |
| 2  | 10  | 12    | 22     | Polarization-achievable over C     |
| 4  | 9   | 13    | 22     |                                    |
| 6  | 8   | 14    | 22     |                                    |
| 8  | 7   | 15    | 22     |                                    |
| 10 | 6   | 16    | 22     |                                    |
| 12 | 5   | 17    | 22     |                                    |
| 22 | 0   | 22    | 22     | All-fixed (symmetric algorithm)    |

## 7. 12-product Gram construction (exact upper bound)

**Result now supported:** \(N_G\le12\) over fields containing \(\sqrt{-1}\) (e.g. \(\mathbb C\), or \(\mathbb F_p\) with \(p\equiv1\pmod4\)). analysis supersedes the analysis statement that this was a proof of equality.

**Upper bound:** The polarization construction achieves \(N_G\le12\):
- 6 norms: ‖y_j‖², ‖y_j+y_k‖² for 1≤j≤3, 1≤j<k≤3
- Each n-vector norm costs ⌈n/2⌉ = 2 products (for n=3): (x+iy)(x-iy) + z²
- Total: 6 × 2 = 12 products
- Verified: rank(Q)=12, rank([Q|G])=12, span=YES

**Essentiality within this construction:** Removing any single product from the displayed polarization set breaks containment of the Gram space. This only shows that those twelve displayed products are all used in that construction. It is not a lower bound for all possible reducible-quadric spans.

**Search observations, not a theorem:** 
- No \(N\le11\) construction was found in the random/structured trials run in analysis.
- The Gram space contains no rank-1 or rank-2 nonzero quadric in the tested coordinates; this does not by itself bound the number of reducible generators of an ambient span.
- Random products almost never contain the Gram subspace because cancellation in the complement is non-generic; this explains the low hit rate, not nonexistence.

**Literature context:** Dumas–Pernet–Sedoglavic \cite{dumas2020fast}, \cite{dumas2021some}
give the 2×2 scalar identity and block-recursive SYRK algorithm. The n=3 result is
a direct application of their polarization technique. Ye–Lim \cite{ye2016fast} study
structured matrix operations but not Y→YY^T specifically.

**Skeleton implications after analysis:** The current Gram evidence does not remove \((0,11)\). The skeleton \((2,10)\) is still a tight Gram-corner worth formulating, but it should not be treated as the first surviving case by proof. The complementary sector supplies an independent lower bound \(m\ge5\) and a separate structured-rank problem for the number of free orbits.

## 8. Complementary conditions (108 equations)

The τ-invariant Brent space decomposes as:
$$K^{9\otimes3}_+ = (\operatorname{Sym}_3 \otimes (K^9\otimes K^9)_{+1}) \oplus (\Lambda^2(K^3) \otimes (K^9\otimes K^9)_{-1})$$
- Gram sector: $6 \times 45 = 270$ equations (sym X, τ₂₃-sym (Y,Z))
- Complementary sector: $3 \times 36 = 108$ equations (antisym X, τ₂₃-antisym (Y,Z))

Fixed terms (u symmetric) have ℓ_u(A) = 0 for antisymmetric A, so they contribute
ZERO to the complementary sector. Only free orbits contribute.

For each free orbit {(u,v,w), (u^T,w^T,v^T)}: the complementary contribution is
$$\ell_{u^{\text{anti}}}(A) \cdot [\ell_v(Y)\ell_w(Z) - \ell_{w^T}(Y)\ell_{v^T}(Z)]$$
where $u^{\text{anti}} = (u-u^T)/2$.

This is the transpose-layer analogue of the cyclic exterior equations (84 dim).
The cyclic case had $249 = 165 + 84$; here $378 = 270 + 108$.

## 9. τ-symmetry of known schemes

None of the known rank-23 algorithms are τ-invariant in their standard form:
- cn122: 1 fixed term, 22 unmatched
- serendipitous: 0 fixed, 23 unmatched
- naive_c88: 0 fixed, 23 unmatched
- BILR Z₄×Z₃: 1 fixed, 22 unmatched
- naive_27: τ-invariant (f=9, m=9, N=18)

By H^1(Z₂, PGL₃³), the transpose involution is unique up to conjugacy over ℂ.
Whether the rank-23 schemes can be conjugated into τ-invariant form is open.

## 10. Order-3 H^1 conjugacy (from analysis)

H^1(Z₃, PGL₃³) = 1 by Shapiro's lemma (PGL₃³ is coinduced). Every order-3 
cyclic-type symmetry is conjugate to the standard rotation. The Cartan and 
trace-grading theorems cover ALL cyclic classes.

## Research significance

The transpose layer τ is a genuinely new structural direction for T_{333}.
Unlike the cyclic layer, the transpose layer has a concrete exact Gram construction and a small complementary sector. analysis shows that the next useful object is not a blind 378-equation residual, but the pair of subspace problems: Gram reducible-quadric containment and complementary decomposable-bivector containment. The skeletons should be retargeted from actual values of these two quantities and from exact linear feasibility once the \((v,w)\) pairs are fixed.
