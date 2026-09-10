# shortened saturated route for excluding rank 20

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Mathematical change from analysis

The analysis route ended by excluding the final high-rank coset profile through 16 full-Wang A-support systems.  The saturated A-split identities give a shorter endpoint.  Once the structural premises force a length-20 decomposition to have
\[
16\text{ rank-one }A\text{-factors}+1\text{ rank-two }A\text{-factor}+3\text{ rank-three }A\text{-factors},
\]
the A-split rank sum is
\[
16\cdot 1+1\cdot 2+3\cdot 3=27=\operatorname{rank}\Phi_A(T_{\langle3,3,3\rangle}).
\]
Thus the A-split flattening inequality is saturated.  In a saturated decomposition the product identity forces at most one invertible A-factor.  The profile has three invertible A-factors, so it is impossible.  The 16 DRAT-certified full-Wang systems from analysis remain valuable corroborating evidence for the same profile, but they are no longer needed for the shortest proof chain.

A second simplification is at the high-rank-pair end.  Orbit 479 is not needed for the coset containment.  Among high-rank pairs, orbit 479 has rank pattern \((1,2,2)\), so it also has rank-one difference.  Therefore the coset argument only needs the dim-2 exclusions 484--491; after those are excluded, any surviving high-rank pair lies in 479 or 481--483, and every such pair has rank-one sum.

## Current verification files

- New analysis finite support: [short_saturation_checks.py](../code/short_saturation_checks.py) and [short_saturation_checks.json](../results/structural/short_saturation_checks.json).
- The analysis run reports: no high-rank pair outside orbits 484--491 has non-rank-one sum (`bad_weak_pairs=0`); orbit 479 contributes 441 high-rank pairs and all have rank-one sum; the rank-one shared-side lemma has no finite counterexample; all 168 rank-three matrices are invertible; and the indexed product formula agrees on all \(729^2=531441\) elementary simple-tensor pairs.
- Original Wang baseline: `data/wang_f2_lb20/verify_receipt.json` records accepted verification of the rank-20 lower-bound certificate; `wang_subspace_lut.meta.json` records complete LUT coverage over all 8,283,458 A-subspaces; `wang_orbit_closed_cache.pkl` carries orbit representatives and lower bounds.
- Line lower bounds: the Wang cache has exactly three one-dimensional orbits, sizes 49, 294, 168, all lower bound 19 by backtracking proof records, covering all 511 nonzero A-directions.
- Affine-plane lower bounds: [coset_plane_verify.json](../results/coset/coset_plane_verify.json) records 651 relevant high-rank affine-plane spans in the normalized cosets, all with Wang lower bound 17.
- Dim-2 exclusions still needing theorem-quality proof objects at the start of this ARTIFACT: 484--491.  analysis reproduced them as original-LUT CP-SAT infeasible systems; analysis found a better proof encoding route, described below.

## High-rank coset containment under the weaker dim-2 premise

Assume a length-20 decomposition exists:
\[
T=\sum_{t=1}^{20} A_t\otimes B_t\otimes C_t
\]
over \(\mathbb F_2\), with all simple terms nonzero.

First, all nonzero A-directions are distinct.  If two terms had the same nonzero A-direction \(a\), quotienting the A-slot by \(\langle a\rangle\) would kill at least two terms and express the quotient tensor using at most 18 terms.  The verified one-dimensional Wang lower bound is 19 for every nonzero A-direction, contradiction.

The A-split flattening \(\Phi_A(T)\) is a 27 by 27 permutation matrix, hence has rank 27.  For a simple term,
\[
\operatorname{rank}\Phi_A(A_t\otimes B_t\otimes C_t)\le \operatorname{rank}(A_t),
\]
and equality holds when \(B_t,C_t\ne0\).  Thus any length-20 decomposition obeys
\[
\sum_t \operatorname{rank}(A_t)\ge 27,
\qquad
\sum_t(\operatorname{rank}(A_t)-1)\ge 7.
\]
In particular at least four A-factors have rank at least two.

For two distinct high-rank A-factors \(a,b\), quotienting by \(\langle a,b\rangle\) kills the two corresponding terms and leaves at most 18 terms.  If the dim-2 quotient lower bound for \(\langle a,b\rangle\) is 19, this is impossible.  Under the deliberately weaker premise that only high-rank pair orbits 484--491 have been raised to lower bound 19, every surviving high-rank pair must lie in orbit 479 or 481--483.  The finite rank-pattern computation in `short_saturation_checks.json` gives
\[
\begin{array}{c|c}
\text{orbit}&\text{ranks of }a,b,a+b\\\hline
479&(1,2,2)\\
481&(1,2,2)\\
482&(1,3,3)\\
483&(1,2,3).
\end{array}
\]
Thus every pair of distinct high-rank A-factors satisfies \(\operatorname{rank}(a+b)=1\).

Fix one high-rank factor \(p\).  For every other high-rank factor \(a\), put \(r_a=a+p\).  Then every \(r_a\) is rank one, and for any two of them,
\[
r_a+r_b=(a+p)+(b+p)=a+b
\]
is also rank one.  Over \(\mathbb F_2\), every nonzero rank-one \(3\times3\) matrix has a unique expression \(uv^T\) with nonzero \(u,v\in\mathbb F_2^3\).  If \(uv^T+xy^T\) has rank one, then either \(u=x\) or \(v=y\).  Moreover a pairwise-compatible family has one shared side globally: if two members share the left vector \(u\) but have different right vectors, any third member with another left vector would have to share both distinct right vectors, impossible; the row-side case is the transpose.  Therefore all high-rank A-factors lie in one affine rank-one coset
\[
p+u\otimes(\mathbb F_2^3)^*
\]
or in the transposed row-type coset
\[
p+\mathbb F_2^3\otimes v^T.
\]

## From the coset to the saturated profile

The eight points in such a coset are an affine 3-space \(AG(3,2)\).  Every five-point subset of \(AG(3,2)\) contains an affine plane of four points.  analysis independently verified the relevant finite tensor fact: every high-rank affine plane that can arise in the normalized cosets spans a three-dimensional A-subspace whose Wang lower bound is 17.  Four A-factors in such a plane cannot occur in a length-20 decomposition, because quotienting by their span leaves at most 16 terms, contradicting lower bound 17.  Hence there are at most four high-rank A-factors.

The split-flattening excess bound requires excess at least seven.  With at most four high-rank factors, there must be exactly four.  At least three of the four must have rank three.  In the normalized column-type coset, lower-block-rank-one cosets have no rank-three points, while lower-block-rank-two cosets contain four rank-two and four rank-three points.  The four rank-three points themselves form one affine plane, so the all-rank-three selection is impossible by the same affine-plane lower bound.  Therefore the only remaining profile is exactly one rank-two A-factor and three rank-three A-factors, plus sixteen rank-one A-factors.  Its rank sum is exactly 27, so the A-split rank inequality is saturated.

The row-type coset follows by transposition symmetry of the A-slot; the finite normalized computation covers the column model, and the matrix-multiplication tensor is invariant under the corresponding exchange of row/column coordinates with the standard companion transformations on the other slots.

## Indexed derivation of the product formula

Index rows of the A-split flattening by \((i,(p,q))\), where \(i\) is an A-row index and \((p,q)\) is a B-coordinate.  Index columns by \((j,(r,s))\), where \(j\) is an A-column index and \((r,s)\) is a C-coordinate.  For a simple term,
\[
F(A,B,C)_{(i,(p,q)),(j,(r,s))}=A_{ij}B_{pq}C_{rs}.
\]
For the matrix-multiplication tensor, the A-split flattening \(P=\Phi_A(T)\) sends
\[
(j,(i,k))\mapsto (i,(j,k)),
\]
so
\[
P^{-1}_{(j,(i,k)),(i,(j,k))}=1.
\]
Now compute an entry of
\[
F(A,B,C)P^{-1}F(A',B',C').
\]
The right factor contributes
\[
F(A',B',C')_{(u,(x,y)),(v,(z,w))}=A'_{uv}B'_{xy}C'_{zw}.
\]
The middle permutation sends row \((u,(x,y))\) to column \((x,(u,y))\) of the left factor.  Therefore the composed entry from column \((v,(z,w))\) to row \((i,(p,q))\) is
\[
\sum_{x,u,y} A_{ix}B_{pq}C_{uy}\, A'_{uv}B'_{xy}C'_{zw}.
\]
Pulling out \(B_{pq}C'_{zw}\), the inner sum is
\[
\sum_{x,u} A_{ix}\left(\sum_y B'_{xy}C_{uy}\right)A'_{uv}
=\bigl[A(B'C^T)A'\bigr]_{iv}.
\]
Thus
\[
F(A,B,C)P^{-1}F(A',B',C')
=F\bigl(A(B'C^T)A',B,C'\bigr).
\]
The analysis script verifies this indexed formula on every pair of elementary simple tensors; bilinearity then gives the formula for all factors.

## Saturation gives at most one invertible A-factor

Let
\[
P=\sum_{t=1}^{20} F_t,
\qquad
F_t=F(A_t,B_t,C_t).
\]
In the forced profile the rank sum equals \(\operatorname{rank}P=27\).  Choose rank factorizations \(F_t=U_tV_t^T\) with \(\operatorname{rank}F_t=\operatorname{rank}A_t\).  Concatenating all \(U_t\)'s and \(V_t\)'s gives two 27 by 27 matrices \(U,V\) with
\[
P=UV^T.
\]
Since \(P\) is invertible, both \(U\) and \(V\) are invertible.  Consequently the block projections satisfy
\[
F_tP^{-1}F_s=\delta_{ts}F_t.
\]
Using the product formula, this gives the matrix identities
\[
A_t(B_sC_t^T)A_s=0 \quad(t\ne s),
\qquad
A_t(B_tC_t^T)A_t=A_t.
\]
The implication from \(F(M,B,C)=0\) to \(M=0\) uses \(B,C\ne0\), which is part of a nonzero simple-term decomposition: some entry \(B_{pq}C_{rs}=1\), and then the corresponding entries of \(F(M,B,C)\) recover every entry of \(M\).

Suppose two distinct A-factors, say \(A_t\) and \(A_s\), are invertible.  The diagonal identities give
\[
B_tC_t^T=A_t^{-1},
\qquad
B_sC_s^T=A_s^{-1}.
\]
Therefore \(B_t,C_t,B_s,C_s\) are all invertible.  But the off-diagonal identity gives
\[
A_tB_sC_t^TA_s=0.
\]
This left-hand side is a product of invertible \(3\times3\) matrices, hence invertible and nonzero, contradiction.  Thus a saturated decomposition has at most one invertible A-factor.

The forced profile has three rank-three, hence invertible, A-factors.  Therefore no length-20 decomposition can exist once the line lower bounds, the eight dim-2 exclusions 484--491, the affine-plane lower bounds, and the split-flattening rank inequality are all supplied with replayable mathematical support.

## Dim-2 proof-object progress in this ARTIFACT

The original analysis occurrence-slot encoding was too symmetric and did not produce proofs quickly.  analysis found a smaller route:

1. For each of the eight needed orbits 484--491, restrict the original-LUT quotient rows to the smallest cap threshold that already gives CP-SAT infeasibility in a pilot: cap<=3 for 484,485,486,487,488,490,491 and cap<=4 for 489.
2. Use CEGAR to extract a row subsystem.  The completed run [dim2_caplimited_cert_manifest.json](../../finite_certification/results/dim2_caplimited_cores_484_491/dim2_caplimited_cert_manifest.json) produced infeasible row cores for all eight orbits.  Active row counts were 2295, 2224, 2139, 2120, 2146, 2502, 2223, and 2362 respectively.
3. Replace the labeled occurrence-slot CNF by a unary-count CNF: variables \(u_{p,\ell}\) mean \(x_p\ge\ell\) for quotient point \(p\) and level \(1\le\ell\le18\).  Monotonicity plus \(\sum_{p,\ell}u_{p,\ell}=18\) represents exactly the integer occupation counts, and every Wang row becomes one cardinality inequality on these unary variables.
4. A pilot for orbit 486 verified quickly: [orbit486_cap3_unary_meta.json](../../finite_certification/results/dim2_unary_pilot486/orbit486_cap3_unary_meta.json) has CaDiCaL return code 20 and `drat-trim` return code 0 with `drat_verified=true` for a 321,573-variable, 790,213-clause CNF.
5. A managed batch task `s34_t23_tool1` is running the same unary-count DRAT verification for all eight orbits in `data/dim2_unary_certs_484_491/`.  Its result must be collected and inspected before the dim-2 premise is treated as certified.

If the batch verifies all eight, the remaining work is to connect the generated row cores to the original Wang LUT and the verified Wang certificate in a compact independent replay, then send the whole proof chain for critical review.

## Current mathematical status

The lower-bound route is now substantially shorter:

1. Wang line lower bound 19 for all nonzero A-directions forbids repeated A-factors in a length-20 decomposition.
2. Dim-2 lower bound 19 for orbits 484--491 forbids exactly the high-rank pairs whose sums do not have rank one; orbit 479 is allowed but harmless for coset containment.
3. Rank-one pairwise differences force all high-rank A-factors into one row/column affine rank-one coset.
4. Affine-plane lower bound 17 and \(AG(3,2)\) arithmetic give at most four high-rank A-factors; split flattening gives exactly four and then the one-rank-two/three-rank-three saturated profile.
5. Saturated product identities forbid two invertible A-factors, while the forced profile has three.

No unconditional theorem has yet been completed in this investigation, because the eight dim-2 exclusions and the exact provenance from the Wang certificate to the induced quotient rows still require complete replayable support.  But orbit 479 and the 16 large A-support DRAT systems have been removed from the essential proof dependency list for the shortest route.
