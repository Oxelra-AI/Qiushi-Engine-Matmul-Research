# shared-pair RLT, triangles, invariant counts, and orbit-face search

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

The finite-field line is still the E11 quotient distinct-support problem: determine whether there exists a 19-point subset of the 255 nonzero projected A-directions satisfying all 417,199 complete Wang occupation rows, and if so pass it into fixed-A/B/C reconstruction; if not, a replayable exclusion would combine with the repeated-direction proof and analysis bridge to improve the \(\mathbb F_2\) lower bound.  analysis introduced a 103-variable orbit-averaged shared-pair RLT relaxation.  The zero-objective LP returned one feasible vertex supported only on point orbits 4 and 5, but that fact alone did not justify restricting the integer support search to those 132 directions.

This ARTIFACT tests that interpretation more directly.

## Files

- Main strengthened relaxation script: [rlt_triangle_integrality.py](../code/rlt_triangle_integrality.py).
- Main output: [rlt_triangle_integrality_result.json](../results/rlt_triangle_integrality/rlt_triangle_integrality_result.json).
- Triangle row validation: [validate_triangle_rows.py](../../quotient_cores/code/validate_triangle_rows.py), output [triangle_row_validation.json](../../quotient_cores/results/triangle_validation/triangle_row_validation.json).
- Exact point-count arithmetic: [orbit_count_arithmetic.py](../../quotient_cores/code/orbit_count_arithmetic.py), output [orbit_count_arithmetic.json](../../quotient_cores/results/orbit_count_arithmetic/orbit_count_arithmetic.json).
- Heuristic support search in point orbits 4+5: [orbit_face_support_search.py](../../occupation_and_completion/code/orbit_face_support_search.py), output [orbits_4_5_support_search.json](../../occupation_and_completion/results/orbit_face_support_search/orbits_4_5_support_search.json).
- Stronger invariant block-count CP-SAT script: [invariant_pair_block_cpsat.py](../../quotient_cores/code/invariant_pair_block_cpsat.py); the triangle run was submitted as background task `s66_t35_tool1` and should be read after completion.

## Corrected triangle/Fortet rows

For binary variables the triangle/Fortet inequality
\[
  y_{pq}+y_{pr}-y_{qr}\le x_p
\]
and its two permutations are valid for every labelled triple.  In orbit-averaged variables, two labelled pair variables can land in the same pair orbit, so their coefficients must be **added**.  The first in-flight background run was cancelled because the draft builder used dict literals that could overwrite a repeated pair-orbit coefficient.  The repaired builder accumulates coefficients and then deduplicates sparse rows.

Validation independent of the Wang table: `triangle_row_validation.json` tested 52 exact stabilizer-averaged 19-point supports (two structured supports plus 50 random supports).  It generated 8,193,405 labelled inequalities and 5,913 unique invariant inequalities; all tested supports had zero triangle-row violation.

## What the stronger LP tests show

The base RLT system has 7 equalities and 183,302 inequalities on 6 point-orbit variables plus 97 pair-orbit variables.  With the repaired triangle rows it has the same equalities and 189,215 inequalities.

The important result is that the analysis omitted-orbit avoidance is **not forced**.  Optimizing mass in point orbits 0--3 gives:

### Base RLT LP

- zero-objective witness: masses `[0,0,0,0,2.290411,16.709589]`;
- maximize total mass on orbits 0--3: objective 19.0 with masses `[3.0,0.444444,15.555556,0,0,0]`;
- minimize total mass on orbits 0--3: objective 0.0 with masses `[0,0,0,0,3.979992,15.020008]`;
- max orbit 0 mass: 6.0;
- max orbit 1 mass: 3.0;
- max orbit 2 mass: 19.0;
- max orbit 3 mass: about 12.83180484.

### Triangle-strengthened RLT LP

- zero-objective witness: masses `[0,0,0,0,1.794145,17.205855]`;
- maximize total mass on orbits 0--3: objective 19.0 with masses `[3.140499,0,8.528939,7.330562,0,0]`;
- minimize total mass on orbits 0--3: objective 0.0 with masses `[0,0,0,0,3.5625,15.4375]`;
- max orbit 0 mass: 6.0;
- max orbit 1 mass: 3.0;
- max orbit 2 mass: 19.0;
- max orbit 3 mass: about 12.83180484.

Thus triangles do not make the first pair relaxation infeasible, and neither base nor triangle LP gives any reason to privilege the orbits-4+5 face as a necessary support region.  They do show that the invariant relaxation is weak enough to realize mutually very different orbit-mass profiles, including all 19 points fractionally in orbit 2.

## Invariant-count integrality

For an actual support \(S\), the averaged point masses are \(x_a=n_a/|O_a|\) where \(n_a=|S\cap O_a|\in\mathbb Z\), and the averaged pair masses are \(y_j=m_j/|P_j|\) where \(m_j\in\mathbb Z\) counts selected unordered pairs in the pair orbit.

Exact arithmetic over point-count cardinality alone gives 34,335 possible six-tuples \(n_a\) with sum 19.  Only 20 have no points in orbits 0--3.  The rounded analysis vertex has masses near \(n_4\approx2.2904,n_5\approx16.7096\); its nearest integer point-count branches are `[0,0,0,0,2,17]` and `[0,0,0,0,3,16]`.

MILP tests keeping all continuous pair variables feasible found point-count integer witnesses and pair-count integer witnesses:

- Base point-count feasibility: `n=[0,1,2,1,7,8]`.
- Base point-count max omitted: `n=[0,3,16,0,0,0]` (all 19 in orbits 0--3).
- Triangle point-count feasibility: `n=[0,0,2,2,6,9]`.
- Triangle point-count max omitted: `n=[1,2,11,5,0,0]` (all 19 in orbits 0--3).
- Base point+pair count integrality witness: `n=[1,0,3,5,2,8]`, `m_total=171`, 40 nonzero pair-orbit counts; exact rational substitution into the linear relaxation has zero equality residual and zero inequality violation.
- Triangle point+pair count integrality witness: `n=[0,0,0,5,4,10]`, `m_total=171`, 23 nonzero pair-orbit counts; exact rational substitution into the triangle-strengthened linear relaxation has zero equality residual and zero inequality violation.

This is a real negative result for this level of invariant strengthening: point-count and pair-count integrality alone still do not exclude the distinct branch.  But these pair counts are not yet a true averaged support graph unless they satisfy the block totals \(\sum_{P_j\subset O_aO_b}m_j=n_an_b\) and \(\sum_{P_j\subset O_a}m_j=\binom{n_a}{2}\).  The new `invariant_pair_block_cpsat.py` script adds exactly those equations and should be treated as the next sharper test.

## Orbits 4+5 support search

The heuristic complete-Wang integer search restricted to point orbits 4 and 5 uses 132 directions and 346,262 nontrivial complete-Wang row constraints.  It returned `UNKNOWN` after about 601 s, with no support and no proof:

- [orbits_4_5_support_search.json](../../occupation_and_completion/results/orbit_face_support_search/orbits_4_5_support_search.json);
- allowed size 132;
- rows by dimension: dim2 1,664; dim3 55,377; dim4 181,984; dim5 96,192; dim6 10,789; dim7 255; dim8 1.

This run must not be interpreted as evidence that the face is empty.  It only says the face is computationally nontrivial under a direct CP-SAT encoding; because the LP objectives show omitted-orbit avoidance is optional, this face is not an exhaustive reduction.

## Current interpretation

The shared-pair relaxation is mathematically useful because it ties all conditioned Wang rows to one global pair distribution.  The analysis computations show that the first two obvious strengthenings do not yet produce a contradiction:

1. triangle/Fortet inequalities preserve feasibility;
2. invariant point-count and pair-count integrality preserve feasibility;
3. the zero-objective orbit-4+5 concentration is not forced and should not drive an exclusive search route;
4. a restricted orbits-4+5 support search did not resolve the actual integer support question.

The immediate higher-value continuation is to test **support-graph block consistency** of invariant counts (already scripted/running).  If that survives, the next useful discrete layer is likely either exact graph realizability inside pair orbits, or returning to the original 255-variable support search with cuts learned from which invariant count branches remain possible.  Any infeasibility at the invariant-count level would still need exact proof/certificate before being used in the mathematical lower-bound chain.

## Block pair totals also survive

The pending block-count CP-SAT run completed: [pair_block_triangles.json](../../quotient_cores/results/invariant_pair_block/pair_block_triangles.json).

This model substituted exact integer orbit counts into all base RLT rows plus the 5,913 triangle/Fortet rows, scaled by 1152, and added actual support-graph block equations:

\[
  \sum_{P_j\subset O_aO_b}m_j=n_an_b\quad(a<b),\qquad
  \sum_{P_j\subset O_a}m_j=\binom{n_a}{2}.
\]

It was still feasible.  Four CP-SAT objectives all returned `OPTIMAL`, and every displayed witness passed exact rational substitution into the linear constraints with zero equality residual and zero inequality violation; every block equation checked exactly.

- Lexicographic feasibility: `n=[3,0,0,3,0,13]`, omitted count 6, 17 nonzero pair-orbit counts.
- Max omitted mass: `n=[6,0,11,2,0,0]`, omitted count 19, 18 nonzero pair-orbit counts.
- Min omitted mass: `n=[0,0,0,0,2,17]`, omitted count 0, 15 nonzero pair-orbit counts.
- Forced zero omitted: `n=[0,0,0,0,2,17]`, omitted count 0, 15 nonzero pair-orbit counts.

This is stronger than the point/pair integrality result but still only an invariant averaged graph-count witness, not an actual selected 19-subset.  It shows that the Wang+RLT+triangle constraints remain too weak even after enforcing integer point counts, integer pair-orbit counts, total 171 pairs, and orbit-block pair totals.  It also shows directly that both extremes are allowed by this invariant abstraction: all 19 points can lie in orbits 0--3 in the relaxation, or none can lie there.

The next meaningful strengthening cannot simply add these invariant constraints again.  It should either:

1. test realizability of the displayed invariant pair counts by an actual 19-vertex simple graph inside the point orbits with edge colors equal to the pair orbits, and then by actual Wang row incidences; or
2. use the surviving integer count branches as guidance for 255-variable support search and cut generation; or
3. introduce a third-order shared statistic that couples triples of selected points to Wang rows, if a compact orbit formulation can be made exact and checkable.

Any infeasible result at these higher abstractions would still need a replayable exact proof before entering the finite-field lower-bound chain.

## Fixed invariant pair-count witnesses are not point-level graph realizations

I then tested whether the displayed block-count witnesses actually come from any 19-point subset with the stated point-orbit counts and pair-orbit counts, before adding any Wang row constraints.  Script: [realize_pair_count_witness.py](../../quotient_cores/code/realize_pair_count_witness.py).

The model uses point variables for the allowed orbits, Boolean pair variables \(z_{pq}=x_px_q\), fixed \(\sum_{p\in O_a}x_p=n_a\), and exact pair-orbit count equations \(\sum_{\{p,q\}\in P_j}z_{pq}=m_j\).  It is therefore a point-level colored graph realization problem for the invariant witness.

Results:

- `min_omitted` witness (`n=[0,0,0,0,2,17]`) counts-only: `INFEASIBLE` after 143.273 s; output [realize_min_omitted_counts_only.json](../../quotient_cores/results/realized_pair_counts/realize_min_omitted_counts_only.json).
- `force_zero_omitted` witness (`n=[0,0,0,0,2,17]`, different pair counts) counts-only: `INFEASIBLE` after 10.445 s; output [realize_force_zero_omitted_counts_only.json](../../quotient_cores/results/realized_pair_counts_force_zero/realize_force_zero_omitted_counts_only.json).
- `feasibility_lex` witness (`n=[3,0,0,3,0,13]`) counts-only: `INFEASIBLE` after 5.657 s; output [realize_feasibility_lex_counts_only.json](../../quotient_cores/results/realized_pair_counts_feasibility_lex/realize_feasibility_lex_counts_only.json).
- `max_omitted` witness (`n=[6,0,11,2,0,0]`) counts-only: `INFEASIBLE` after 2.625 s; output [realize_max_omitted_counts_only.json](../../quotient_cores/results/realized_pair_counts_max_omitted/realize_max_omitted_counts_only.json).

These solver `INFEASIBLE` statuses are not replayable proof artifacts, but they reveal the main loss in the invariant abstraction: it can satisfy Wang+RLT+triangle+block equations with pair-orbit counts that are not the edge-color distribution of any actual 19-point subset.  The next sharper computation should either integrate point-level graph realization into the RLT search, or use a separation loop: find an invariant witness, test point-level graph realization, add a sound no-good/count cut or stronger graph-realizability condition, and repeat.  Only after such a point-level witness exists does it make sense to ask whether that witness also satisfies the complete Wang rows or fixed-A/B/C filters.
