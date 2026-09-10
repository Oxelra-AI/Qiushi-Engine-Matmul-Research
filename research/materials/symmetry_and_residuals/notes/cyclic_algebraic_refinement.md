# cyclic algebraic refinement

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Corrected cyclic quotient bookkeeping

analysis correctly identified the characteristic-zero cyclic quotient as controlled by the Cartan trivector, but it compressed the antisymmetric equations too far.  The full antisymmetric space is
\[
\Lambda^3(\mathfrak{gl}_3)=\Lambda^3(\mathfrak{sl}_3)\oplus I\wedge\Lambda^2(\mathfrak{sl}_3),
\]
so the dimensions are
\[
84=56+28,
\qquad 165+56+28=249.
\]
The 28 mixed equations are not optional: for lifted orbit vectors
\(U_j=u_j+a_jI, V_j=v_j+b_jI, W_j=w_j+c_jI\), the trace part is
\[
\sum_j I\wedge\bigl(a_j v_j\wedge w_j-b_j u_j\wedge w_j+c_j u_j\wedge v_j\bigr)=0.
\]
For the exact BILR four-orbit decomposition reconstructed below, this \(28\times12\) map has rank 12 over all tested primes, so trace lifts are forced to zero at that point.

The characteristic-zero m<=3 exclusion remains valid after this correction: apply \(\Lambda^3\) of the trace-free projection \(\mathfrak{gl}_3\to\mathfrak{sl}_3\).  It fixes the Cartan form and maps every decomposable orbit contribution to a decomposable trivector, so any cyclic decomposition with at most three free cyclic orbits would express the Cartan trivector in \(\sigma_3(G(3,\mathfrak{sl}_3))\).  analysis verified that the Cartan form lies in the open GL(8)-orbit of \(\Lambda^3\mathbb C^8\), while \(\sigma_3(G(3,8))\) has affine dimension at most 48 < 56, hence the Cartan form is not in that secant variety.  Thus any characteristic-zero pure cyclic decomposition needs \(m\ge4\), excluding skeletons \((22,0),(19,1),(16,2),(13,3)\).  Literature support: stable Cartan 3-form/stabilizer facts in Le--Panak--Vanzura lines 188--218 and stable 8-dimensional forms lines 223--234 (`\cite{l2018manifolds}`); direct computation at [sl3_trivector_verification.json](../../quotient_cores/results/sl3_trivector/sl3_trivector_verification.json).

## Exact BILR cyclic rank-23 control

I reconstructed the Ballard--Ikenmeyer--Landsberg--Ryder cyclic rank-23 scheme from their displayed Sec. 2.1 formulas (`\cite{ballard2018geometry}`, object lines 56--100).  The script

- [ballard_z4_cyclic_scheme.py](../../exact_baselines/code/ballard_z4_cyclic_scheme.py)

builds the \(\mathbb Z_4\times\mathbb Z_3\) scheme as 11 cubes plus four free cyclic 3-orbits, expands all 23 terms, and verifies the 729 coefficients of \(\operatorname{tr}(XYZ)\).  The first run saved

- [ballard_z4_cyclic_scheme.json](../../exact_baselines/results/ballard_z4_cyclic/ballard_z4_cyclic_scheme.json).

The corrected normalization is in

- [ballard_cyclic_analysis_v2.py](../code/ballard_cyclic_analysis_v2.py)
- [ballard_cyclic_analysis_v2.json](../results/ballard_z4_cyclic/ballard_cyclic_analysis_v2.json).

Results:

- 23 terms = 11 cubes + four free cyclic orbits.
- Brent errors: 0.
- Diagonal polynomial identity: 0 mismatches.
- Exterior normalization: the target \(\omega\) was stored with coefficients \(\pm3\); one free cyclic orbit contributes \(3(U\wedge V\wedge W)\), so the BILR four orbit representatives satisfy
  \[
  \sum_{j=1}^4 U_j\wedge V_j\wedge W_j=\omega/3,
  \]
  equivalently \(3\sum_j U_j\wedge V_j\wedge W_j-\omega=0\) exactly.
- The four orbit representatives are trace-free, and the mixed trace-lift map has rank 12 over primes 1000003, 65521, 32003.
- The exterior Jacobian has rank 56 over the same primes.

A separate tangent-kernel check

- [bilr_exterior_kernel_check.py](../code/bilr_exterior_kernel_check.py)
- [bilr_exterior_kernel_check.json](../results/ballard_z4_cyclic/bilr_exterior_kernel_check.json)

shows the 40-dimensional kernel of the ordered four-wedge map is exactly the span of 32 per-summand internal \(SL_3\) basis-change directions plus 8 global adjoint \(\mathfrak{sl}_3\) directions, over primes 1000003, 1000033, 65521, 32003.  Thus near the BILR point the rank-4 exterior fiber has the expected local rigidity modulo internal bases and the Cartan stabilizer.

## Koszul--Young flattening evidence for the residual cubic

For a cubic in 9 variables I implemented the Koszul--Young flattening
\[
F_P:\Lambda^4 V\otimes V^*\to \Lambda^5 V\otimes V
\]
as an \(1134\times1134\) matrix.  A pure cube has rank 70 under this map, so \(\operatorname{rank}F_P>70f\) excludes Waring rank \(\le f\).  The pure-power contribution bound is consistent with Guan's definition of Koszul--Young flattenings and pure-power rank formula (`\cite{guan2015flattenings}`, lines 61--69 and related rank statements); the script also directly verifies rank 70 for a random cube.

Evidence files:

- [cyclic_koszul_scan.py](../code/cyclic_koszul_scan.py)
- [cyclic_koszul_scan.json](../results/cyclic_koszul/cyclic_koszul_scan.json)
- [ballard_cyclic_analysis_v2.py](../code/ballard_cyclic_analysis_v2.py)
- [ballard_cyclic_analysis_v2.json](../results/ballard_z4_cyclic/ballard_cyclic_analysis_v2.json)

Numerical/random family scan from the analysis rank-4 decomposition:

- corrected dimensions: 84=56+28;
- exterior Jacobian rank 56 and kernel 40 at the numerical point;
- random pure cube rank under the flattening: 70;
- six sampled m=4 residual cubics all have flattening rank 1048--1050, hence every sampled member has Waring rank at least 15 by this flattening.

Exact BILR residual:

- the residual cubic is exactly the sum of the 11 displayed BILR cubes;
- its Koszul ranks over primes 1000003, 1000033, 65521, 32003 are all 722;
- therefore its Waring rank is at least \(\lceil722/70\rceil=11\), and at most 11 from the displayed cubes, hence exactly 11.

This certifies algebraically why this known cyclic rank-23 scheme cannot be shortened by simply deleting one of its 11 cubes while keeping the same four free orbits.

## Local deletion linearization around BILR

The script

- [ballard_delete_linearization.py](../../quotient_cores/code/ballard_delete_linearization.py)
- [ballard_delete_linearization.json](../results/ballard_z4_cyclic/ballard_delete_linearization.json)

deletes each BILR cube in turn and tests whether the missing cube lies in the first-order image of (i) internal \(SL_3\) changes of the four exterior 3-plane bases and (ii) perturbations of the remaining 10 cube vectors.  For every one of the 11 dropped cubes, the augmented rank is one larger than the Jacobian rank over primes 1000003, 1000033, 65521, 32003.  Thus every single-cube deletion is first-order nonrepairable in this local BILR m=4 chart.  Scope: this is local evidence only; it does not exclude another component or a large move inside the rank-4 exterior fiber.

## Caution about numerical search

A local nonlinear search ([cyclic_m4_rank10_search.py](../code/cyclic_m4_rank10_search.py)) tried to repair BILR by deleting one cube and moving internal \(SL_3\) bases plus 10 cubes.  It is slow because matrix exponentials are used; the first two deletion attempts did not reach zero ([rank10_search_partial.json](../results/cyclic_m4_rank10_search/rank10_search_partial.json), best norm 0.0287).  This should not be treated as mathematical evidence.  It is useful only as a construction probe and is dominated by the exact first-order obstruction above.

## Consequence for the cyclic route

Reliable current cyclic state:

1. Characteristic zero: pure cyclic skeletons with \(m\le3\) are excluded by the trace-free projection plus prehomogeneity/secant argument.
2. Characteristic zero: an exact cyclic rank-23 scheme with \((f,m)=(11,4)\) is reconstructed and verified; its residual cubic has exact Waring rank 11 by Koszul rank 722 and the displayed 11 cubes.
3. Around this BILR point, deleting any cube is first-order nonrepairable in the natural m=4 chart.
4. The global \((10,4)\) cyclic rank-22 question remains open: it asks whether some other point in the rank-4 exterior fiber has residual cubic with Waring rank \(\le10\).  The strongest next algebraic task is to derive the Koszul rank as a function on the finite/moduli m=4 fiber and prove it is always \(>700\), or find the rank-drop locus and use it as a construction target.
5. For \(m\ge5\), \(f\le7\), the same flattening only needs rank \(>490\) to exclude Waring rank \(\le7\).  The sampled m=4 ranks are far above this, but no theorem for m>=5 has been proved.

This does not affect the general nonsymmetric independent-UV incidence, which remains the central unresolved part of the original rank-22/rank-23 problem.

## Post-review correction and strengthened v2 deletion check

review verification (`independent-verification-record`) confirmed the main cyclic algebra but forced two evidence refinements that should govern later use of this note.

First, the BILR residual statement should be read as follows: the Koszul--Young matrix has rank **at least** 722 over characteristic zero because the same integer matrix has rank 722 modulo several primes. This lower bound is already enough: if the residual cubic had Waring rank at most 10, the flattening rank would be at most \(10\cdot70=700\). The displayed 11 BILR cubes give the upper bound, so the residual Waring rank and border Waring rank are exactly 11. We have not separately proved that the rational matrix rank is exactly 722; it may be higher without affecting this conclusion.

Second, the initial deletion linearization used only modular rank evidence and omitted the 8 global adjoint directions. I repaired this in

- [ballard_delete_linearization_v2.py](../../quotient_cores/code/ballard_delete_linearization_v2.py)
- [ballard_delete_linearization_v2_subset.py](../../quotient_cores/code/ballard_delete_linearization_v2_subset.py)
- [ballard_delete_linearization_v2_merged.json](../results/ballard_z4_cyclic/ballard_delete_linearization_v2_merged.json).

The v2 calculation includes 130 columns: 32 internal \(SL_3\) directions for the four exterior triples, 8 global adjoint orbit directions, and 90 perturbation directions for the ten kept cube vectors. Exact rational ranks were computed for all 11 drops. In every case the augmented rank is one larger than the Jacobian rank over \(\mathbb Q\) (with matching ranks modulo 1000003, 1000033, 65521, 32003). This gives a strict first-order nonrepairability result for one-cube deletions in the local BILR \((10,4)\) chart. It remains local: it does not exclude another rank-4 exterior point, another component, a finite non-infinitesimal move, or any non-cyclic rank-22 decomposition.

I also explicitly checked the integer identity \(JT=0\) for the 40 tangent-kernel directions of the BILR exterior decomposition (32 internal plus 8 global adjoint): `JT_nonzero_count=0`, `JT_max_abs=0`. Thus the kernel spanning statement is not merely a modular artifact, while rank independence is still certified by the modular full-rank comparisons in `bilr_exterior_kernel_check.json`.
