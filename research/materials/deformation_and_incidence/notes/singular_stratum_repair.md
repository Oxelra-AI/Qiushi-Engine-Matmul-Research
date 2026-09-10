# Repairing the pairing-defect geometry and reframing rank 22 through a singular preimage stratum

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Why the analysis `36=36` interpretation is not a proof route

The analysis computation projected infinitesimal changes of the UV pairing matrix at `cn122` through a left null space and compared a 36-dimensional image with the codimension 36 of a rank-defect determinantal condition. This count is not a tangent-cone emptiness argument. At the seed, the UV pairing matrix has full column rank 23, an open condition disjoint from the rank-22 pairing-defect variety. The projected derivative `N δP` describes first-order motion in a coordinate quotient around a full-rank point, not the tangent cone of the rank-defect locus at that point. Also, the presence of many low-rank matrices in the projected image means dimension equality alone cannot certify emptiness of an intersection.

The useful consequence of the computation is different: if a 22-term preimage of `T333` exists, it is forced into a highly singular part of the rank-22 parameterization by term scalings and by the positive-dimensional stabilizer of the matrix-multiplication tensor.

## Actual shortened rank-22 chart

For a 22-term configuration with full-rank UV pairing matrix

\[
P(U,V)=\big[u_i\otimes v_i\big]_{i=1}^{22}\in K^{81\times 22},
\]

choose 22 UV rows `R` such that `M=P_R` is invertible. Split the 729 tensor equations as 22 selected UV rows times 9 C-coordinates and the remaining 59 UV rows times 9 C-coordinates. Then the W factors are determined by

\[
W=M^{-1}T_R,
\]

and the remaining equations are

\[
F_R(U,V)=T_{\bar R}-P_{\bar R}M^{-1}T_R=0.
\]

This is the concrete 531-equation system in 396 UV variables. The script

[rank22_singular_stratum_v2.py](../code/rank22_singular_stratum_v2.py)

implements this chart over finite fields and explicitly requires `rank(T_R)=9` when probing `T333`, so the solved W factors span the full C-space when possible. The first analysis version did not enforce this and therefore sometimes chose rows with `rank(T_R)=3`, producing meaningless low shortened ranks. The corrected run is saved at

[singular_stratum_v2.json](../results/singular_stratum/singular_stratum_v2.json).

Calibration results over `F_65521`:

- For 5 random rank-22 tensors, the chart recovers zero residual and the generic ranks `full Jacobian rank = 550`, `shortened Jacobian rank = 352`.
- For 5 random full-span `U,V` charts against fixed `T333`, the solved W factors have span 9, the residual has all 531 complement entries nonzero, and the ranks remain `550/352`.
- For all 23 one-term deletions of `cn122`, full-W charts exist, the shortened residual is not in the shortened Jacobian image, and the shortened ranks are 309--328 except a few lower cases; these remain local first-order non-repair facts only.
- For all 23 one-term deletions of `serendipitous_8d34`, full-W charts exist and the residual is not in the shortened Jacobian image; several non-solution chart ranks exceed 328, which is allowed because the tensor represented by a deleted scheme is not fixed by the `T333` stabilizer.

## Stabilizer fixed line

The corrected infinitesimal stabilizer action on tensor coordinates was reimplemented in

[invariant_line_and_singularity.py](../../quotient_cores/code/invariant_line_and_singularity.py).

For primes `3, 5, 65521`, the 27 infinitesimal action matrices on the 729-dimensional tensor space have stacked rank 728. Their common fixed subspace is one-dimensional and is spanned by `T333`; the three mode flattenings of `T333` all have rank 9. The saved result is

[invariant_line_and_singularity.json](../results/singular_stratum/invariant_line_and_singularity.json).

Thus the rank-22 problem can be seen as asking whether the rank-22 secant parameterization meets the invariant line `K*T333` at a nonzero point.

## Forced singularity at a rank-22 preimage of `T333`

Let `Phi_22` be the 22-term Brent parameterization. If `Phi_22(U,V,W)=T333`, then all three factor spans are 9-dimensional, because each flattening of `T333` has rank 9. Therefore:

- termwise scaling directions contribute `2r=44` tangent directions in the kernel of `d Phi_22`;
- the infinitesimal stabilizer of matrix multiplication contributes a 26-dimensional tangent image in parameter space;
- for the central scalar subspace, two stabilizer directions coincide with uniform term scalings.

For a stabilizer-transverse decomposition, the combined scaling-plus-stabilizer tangent subspace has dimension

\[
44+26-2=68.
\]

The full Brent Jacobian rank is then at most

\[
594-68=526,
\]

whereas a generic rank-22 tensor has Jacobian rank 550. In a full-UV-rank shortened chart, the eliminated W block has rank 198, so the shortened Jacobian rank is at most

\[
526-198=328,
\]

whereas the generic shortened rank is 352. A rank-22 algorithm for `T333`, if stabilizer-transverse, must therefore sit in a 24-rank-drop singular stratum of the rank-22 parameterization.

This statement comes from the actual equation `Phi_22=T333` and the true stabilizer, not from the invalid rank-defect tangent-cone count.

## Exceptional alignment strata

The intersection between stabilizer tangents and termwise scaling tangents can be larger than the two central scalar directions when a decomposition is aligned with invariant line configurations. The natural 27-term decomposition provides a control: it has full factor spans and stabilizer rank 26, but the stabilizer-scaling intersection has dimension 8 because many stabilizer directions preserve the coordinate factor lines termwise. Therefore the `rank <= 526` bound is the stabilizer-transverse branch, while non-transverse rank-22 decompositions would lie in additional algebraic strata where non-scalar stabilizer elements act termwise on many of the 22 factor triples. Those strata are special and should be treated explicitly rather than hidden inside the generic count.

Known rank-23 schemes are stabilizer-transverse with respect to scalings: `stabilizer_check.py` gives corrected combined rank 70 for `cn122` in the 621-dimensional rank-23 parameter space (46 scaling + 26 stabilizer - 2 scalar overlap), while the actual Jacobian kernel is 94. This matches the earlier corrected symmetry dimension and shows that the singular-preimage viewpoint is compatible with the verified rank-23 geometry.

## Exact algebraic route opened by this reformulation

The next exact computation should work with the preimage of the invariant line, not with seed-local pairing continuation. Concretely:

1. Use the 728 independent linear equations cutting out the quotient by the invariant line `K*T333`, applied to `Phi_22(U,V,W)`. A rank-22 algorithm is a point in this preimage with nonzero scale on `T333`.
2. In a full-UV-rank chart, use the shortened system above and impose the 24-rank-drop condition `rank(dF_R) <= 328` for the stabilizer-transverse branch.
3. Separately enumerate or parameterize the non-transverse alignment strata where the stabilizer action preserves term factor lines beyond the central scalar overlap.
4. If the preimage of the invariant line can be shown to have no nonzero point in either the transverse singular stratum or the non-transverse alignment strata, this would exclude full-UV-rank rank-22 decompositions over the tested characteristic. Lower UV-rank strata still require separate charts.

This is a stronger and more global direction than repeating the `36=36` count at other seeds.

## Finite-field side status from this ARTIFACT

The direct pooled `MM-22-63.cnf` challenge was run with both CaDiCaL and Kissat for 600 seconds. Both returned `UNKNOWN`; this is not evidence for satisfiability or unsatisfiability. related analysis's high-pair exact-18 rank-1 support batch now reports all 69 high-pair orbit representatives infeasible by CP-SAT, with no full-LUT zero-violation support available for exact fixed-A B/C solving. These CP-SAT infeasibilities remain proof objects only after CNF/DRAT replay; the visible filtered CNF/DRAT files for high10, high84, high161 and pairs (17,19), (17,20) are verified, while pair (17,26) has a SAT filtered formula and therefore is not an exclusion in that filtered setting.
