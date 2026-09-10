# reassessment: square-cut status and next finite-field investment

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Correction to analysis interpretation

analysis produced useful exact square inequalities, but its route-status sentence was too strong. The computation established only the following:

- 149 exact global square inequalities were extracted from 12 non-PSD integer pair-count assignments.
- When these cuts were added to a CP-SAT integer pair-count model, the solver still found integer pair-count assignments for the six selected count vectors.
- Those returned assignments were non-PSD.

This does **not** imply that polyhedral PSD separation cannot decide the integer pair-count problem. The pair-count lattice is finite, and every non-PSD rational moment assignment has a rational square separator. A finite square family exists in principle for any finite infeasible lattice search, although it may be computationally large. Also, the minimum eigenvalues of arbitrary CP-SAT vertices are not a meaningful convergence measurement unless the solver is asked to optimize a PSD-related quantity.

There is a second important scope issue: [pooled_global_square_cuts.py](../../relaxations_and_cuts/code/pooled_global_square_cuts.py) explicitly skipped the 5,913 triangle/Fortet rows. Therefore the new integer witnesses found in analysis may not satisfy the analysis formulation. The cuts remain valid globally, but the Phase 4/5 feasibility statements are statements about Wang RLT + block totals + pair-cardinality + square cuts without the triangle rows. The result should be used as evidence that a small unguided cut pool did not settle the sampled branches, not as evidence that the moment route is exhausted.

The durable analysis note should no longer be read as closing the orbit-averaged pair-count approach. Its reusable output is the cut coefficient file:

- [pooled_cuts_coefficients.json](../../relaxations_and_cuts/results/pooled_square_cuts/pooled_cuts_coefficients.json)

## Current research state after correction

The finite-field frontier and the E11 bridge remain unchanged. The unresolved object is a distinct 19-subset of the 255 nonzero E11 quotient directions satisfying all 417,199 complete Wang occupation rows. A solution support would enter fixed-A/B/C completion and could produce a rank-19 E11 core; a complete exclusion would combine with the repeated-direction proof and bridge to raise the full tensor lower bound over `F2`.

The useful layers now separated by evidence are:

1. continuous fixed-count moment feasibility with full Wang RLT + triangle + block totals + PSD: six selected count vectors have numerical survivors from analysis;
2. integer pair-count feasibility with full linear rows: analysis found exact integer assignments for two counts, but they were non-PSD;
3. square-cut outer approximations: analysis generated 149 exact global cuts but did not include triangle rows in the later CP-SAT phases;
4. point-level realization and complete Wang support: still open; targeted searches returned `UNKNOWN`.

## Reassessment of the next investment

The newly available structure is the fast block SDP. A direct 255-variable support search is still the ground-truth problem, but recent direct runs returned `UNKNOWN` and did not use the conic geometry. The most informative next bounded investment is therefore a conic-guided integer pair-count pilot for one already studied count vector, while continuing to keep direct support search as the final target.

A bounded pilot should fix one count vector, preferably `[0,0,3,5,4,7]` because it has saved continuous witnesses and several non-PSD integer assignments. At each search node it should keep the complete analysis linear formulation:

- Wang RLT rows;
- triangle/Fortet rows;
- pair-cardinality equations;
- deterministic block-pair totals;
- bounds or fixed values on selected integer pair counts;
- block-decomposed PSD constraints.

Then solve the continuous block SDP under the current pair-count bounds. If the conic subproblem returns a fractional feasible point, branch on pair-count variables whose implied `m_j=|P_j|y_j` are far from integer, preferably weighted by sensitivity in the smallest PSD blocks or by participation in tight rows. If it returns an integer pair-count vector, test the full labelled moment matrix and save it if PSD; otherwise derive exact rational square cuts from negative eigendirections and add them to the global cut pool. Numerical conic infeasibility is useful for steering the pilot, but only exact square inequalities, exact integer row checks, and replayable discrete encodings should be promoted into formal support.

This route is not a commitment to preserve moment methods indefinitely. It is a bounded comparison enabled by the analysis block decomposition. Its possible outcomes are all useful:

- an integer PSD pair-count witness gives a concrete target for point-level graph/color realization;
- a small exact square-cut contradiction for a fixed branch gives new branch information for support search;
- many conic-feasible fractional nodes with no integer PSD witness would show where the integer/conic gap remains and help decide whether to return effort to point-level search.

A direct support search remains essential and should use the complete table, verified face cuts, overlap cuts, count restrictions that are actually established, and the fixed-A/B/C completion pipeline for any found support. But the next ARTIFACT should first test whether conic guidance changes the integer pair-count search, because that is the important untried connection exposed by the correction of analysis.
