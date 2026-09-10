# Removing the sampled S from the E11 quotient-lift obstruction and reassessing the route

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Scientific purpose

The active mathematical problem remains the exact tensor rank of the 3x3 matrix-multiplication tensor.  The current E11 work is a finite-field intermediate: an E11 rank-19 decomposition over F2 would lift to a full F2 rank-22 decomposition by the verified three elementary products, while an E11 obstruction would still not by itself settle characteristic-zero rank.

The analysis row/column-space mechanism explained why the sampled orbit-445 quotient-lift instances fail.  The concern is important: exhaustive work for one four-dimensional prefix orbit V would not cover the other 619 V-orbits.  This ARTIFACT therefore tested how much of the mechanism survives after deleting the sampled quotient-generated matrix subspace S and retaining only:

- the four-dimensional A-prefix subspace V,
- the quotient tensor Q_V in (A/V)^* tensor B tensor C,
- its quotient slice space S0 = span of the four B-C slices of Q_V,
- consequences of rank-one generation expressed only through the residual A-cover problem.

This is deliberately a structural probe, not an E11 lower-bound proof.

## Correction to the analysis S_min cover summary

The previous `e11_vs_smin_scan.py` treated the LP relaxation value as if its ceiling were an exact integer cover size.  That is not justified for the 15-vector covering system over F2^4.  I patched the script to compute the exact integer optimum using `scipy.optimize.milp` and reran all 620 V-orbit representatives.

New file:

- [vs_smin_all620_intcover.json](../results/v_sfree_obstruction/vs_smin_all620_intcover.json)

Correct exact residual cover-size distribution for S0 is:

- 251 orbits: exact minimum residual cover size 7;
- 277 orbits: size 8;
- 84 orbits: size 9;
- 8 orbits: size 10.

Every orbit still has a nonempty quotient-rank window when using only the S0 cover lower bound, so the scientific conclusion of analysis remains: the contraction-cover invariant alone does not exclude all V-orbits.  But the stated distribution `best_s = 6,8,9` is superseded by the exact integer distribution above.  In particular, the 251 `sum_m=45` orbits need 7 residual terms, not 6, despite LP value 45/8 = 5.625.

## Bare S0 tight row/column-space scan at the exact minimum cover size

New script:

- [e11_sfree_v_obstruction_scan.py](../code/e11_sfree_v_obstruction_scan.py)

For each V representative, the script computes S0, computes

\[
  m_\phi(S0)=\min_{M\in R_\phi + S0} \operatorname{rank} M,
  \qquad \phi\in V^*\setminus\{0\},
\]

finds the exact minimum size of a residual A-multiset whose incidence counts dominate these 15 ranks, then tests the analysis tight contraction row/column-space necessary condition using only minimum-rank matrices in the affine cosets `R_phi+S0`.

Output:

- `data/v_sfree_obstruction/sfree_all620.json`

Results at the exact minimum cover size:

- 514 / 620 V-orbits: every minimum-size cover is blocked by the bare S0 tight row/column-space test;
- 106 / 620 V-orbits: at least one minimum-size cover survives this bare test;
- 102 distinct S0 m-profiles occur;
- exact minimum residual cover-size distribution matches the patched integer-cover scan: 7:251, 8:277, 9:84, 10:8;
- quotient-rank window gaps `19 - flat_lb - s_min` are 0 for 7 orbits, 1 for 84, 2 for 275, 3 for 252, and 5 for 2.

The 106 surviving orbits already show that the tight-space mechanism is not a universal V-only obstruction even before considering enlargements of S beyond S0.

## Scan over all residual budgets allowed by the quotient flattening lower bound

A rank-19 E11 decomposition with this quotient setup could have quotient length q larger than the flattening lower bound, reducing residual size to s=19-q.  To test whether the S0 mechanism becomes universal when every possible residual budget is considered, I built:

- [e11_tight_obstruction_rank_s_scan.py](../../quotient_cores/code/e11_tight_obstruction_rank_s_scan.py)

For each V, it scans residual sizes from the exact S0 minimum cover size up to `s_max = 19 - flat_lb(Q_V)`, stopping at the first cover not blocked by the S0 row/column-space test.

Output:

- [sfree_budget_scan_all620.json](../results/v_sfree_obstruction/sfree_budget_scan_all620.json)

Result:

- all 620 / 620 V-orbits have a surviving residual A-cover for some allowed budget;
- first survivor sizes: 269 at s=8, 340 at s=9, 10 at s=10, 1 at s=11.

Examples:

- orbit 445, V = [1,2,8,64], flat_lb=6: all S0 minimum covers at s=8 are blocked, but a cover survives at s=9: `[2,2,3,4,5,8,9,12,13]`;
- orbit 439, V = [1,2,4,32], flat_lb=6: minimum covers at s=10 are blocked, but a cover survives at s=11;
- orbit 455, V = [1,2,80,152], flat_lb=9: minimum covers at s=7 are blocked, but a cover survives at s=8;
- orbit 438, V = [1,2,4,8], flat_lb=9: a cover survives already at its only allowed residual size s=10.

Thus, after eliminating S down to V and S0, the row/column-space mechanism cannot close the quotient-lift route across the 620 V-orbits.  Its success for the sampled orbit-445 dim-11 S spaces is a real local explanation of those failures, but it does not scale to a global E11 result without a new theorem controlling all rank-one-generated enlargements S containing S0.

## Interpretation of the obstruction mechanism

The S0 scan is useful because it separates three layers:

1. **Cover layer.**  The contraction ranks m_phi(S) force lower bounds on how many residual A-vectors are visible to each phi.  This layer is too weak for all V and now has exact integer cover sizes.
2. **Tight-space layer.**  When a contraction is tight, each participating rank-one B-C term must lie in row/column spaces of minimum-rank matrices in the affine coset.  This explains many failures and all sampled orbit-445 dim-11 S failures, but the bare V/S0 version has survivors in every orbit once larger residual budgets are allowed.
3. **Actual S layer.**  Enlarging from S0 to a quotient-generated S can change m_phi and the minimum-rank row/column-space allowances.  The analysis orbit-445 rank-11 pool remains exactly excluded at this layer, but sampled exclusion is not a theorem over all possible S.

Consequently, enumerating all dimension-11 S for orbit 445 is no longer the best main direction.  It would still leave 619 V-orbits, and this ARTIFACT shows the current V-only abstraction is not strong enough to generalize.

## Route reassessment

The finite-field E11 quotient-lift line has produced valuable infrastructure and insight: exact fixed-A solvers, quotient/coset formulations, S-level compression, and the tight row/column-space explanation.  But it has not produced a rank-19 E11 witness or a global E11 obstruction.  The main concentration should now shift away from orbit-445 S enumeration.

Two higher-value threads should receive the next main effort:

1. **Integrate and independently validate related analysis's full-tensor finite-field Wang branch.**  related analysis has DRAT proof objects excluding all-rank-3 and rank-2/no-rank1 T-level Wang branches, and rank-1 projection proof objects showing any length-20 Wang-admissible full-T support has at most 18 rank-1 A-directions with no repeated direction.  The remaining finite-field support problem is mixed and not yet closed.  related analysis should help by independently checking the proof semantics, Wang LUT reconstruction/conventions, and testing any full-LUT E11 support with the calibrated fixed-A B/C solver.

2. **Rebuild the characteristic-zero pairing-defect incidence as an exact algebraic problem.**  Earlier numerical continuation only showed noncompact rank-23 cancellation ends; it did not find a finite rank-22 point.  Any revival should impose the projective two-factor dependence/incidence directly in Brent equations, including gauge choices and coefficient-domain awareness, instead of following raw numerical singular-value descent.

The E11 S-level row/column-space obstruction should be preserved as a reusable lemma template and fast filter, not treated as the main global route until a genuinely orbit-level or all-S theorem appears.
