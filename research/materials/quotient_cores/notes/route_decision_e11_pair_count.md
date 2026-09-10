# route decision for the E11 distinct branch

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Corrected state of the pair-moment line

The analysis square inequalities are valid reusable mathematics, but the analysis route-status sentence is not. The computation did not show that square separation or integer pair-count PSD methods are exhausted. It showed only that one small pooled family of 149 exact square inequalities did not decide six sampled count vectors in a later CP-SAT model that omitted the 5,913 triangle/Fortet rows.

A direct scope check of the four stored analysis Phase-3 integer pair-count vectors found:

- all four satisfy the base Wang RLT rows exactly and have exact block totals;
- two violate triangle/Fortet rows and therefore do not satisfy the full analysis linear formulation;
- two satisfy the full analysis linear formulation but remain non-PSD.

Thus analysis remains useful for its exact cut file, not for the broad route conclusion.

Relevant files:

- [pooled_cuts_coefficients.json](../../relaxations_and_cuts/results/pooled_square_cuts/pooled_cuts_coefficients.json)
- [CORRECTION_SCOPE.md](../../relaxations_and_cuts/notes/pooled_square_cuts/CORRECTION_SCOPE.md)
- [summary.json](../results/scope_check/summary.json)
- [pooled_square_cuts_analysis.md](../../relaxations_and_cuts/notes/pooled_square_cuts_analysis.md)

## Field-scope caveat

A complete exclusion of the E11 distinct rank-19 projected-A branch would combine with the repeated-direction proof and the established full-to-core bridge to exclude full rank 20 over `F2`, giving the next finite-field lower-bound ARTIFACT `R_F2(T) >= 21`. It would not by itself prove rank 23 optimality or settle characteristic zero.

## Why the conic-guided pilot is the best next bounded investment

The open finite-field object remains a distinct 19-point E11 projected-A support satisfying all complete Wang rows. The recent point-level searches are semantically closest to this object but returned `UNKNOWN`; repeating the same run would not exploit the main new structure from earlier analysis.

The main new structure is the fast block representation of the invariant moment PSD constraint. analysis preflight confirmed that all 103 orbit moment coefficient matrices are block-separated by the analysis eigenspaces to about `1.19e-11`, supporting use of the 93-block model as the conic representation. For the count

`[0,0,3,5,4,7]`,

zero counts in the first two point orbits force 27 of the 97 pair-orbit variables to zero, leaving 70 active pair-orbit variables. The saved continuous witness has pair-count integrality sum distance about `17.2843`, and analysis already found four exact full-linear integer pair assignments for this count with labelled moment minimum eigenvalues from about `-0.3646` to `-0.0704`.

This is precisely the gap not yet tested: use the conic model to guide the integer pair-count decisions, rather than asking CP-SAT for arbitrary linear-feasible vertices and checking PSD only afterward.

## Next executable work

Build a bounded single-count pilot for `n=[0,0,3,5,4,7]`:

1. Use the full analysis linear rows: Wang RLT, all triangle/Fortet rows, pair-cardinality, and deterministic block totals.
2. Work in `m_j` coordinates for integer search, with explicit conversion to `y_j=m_j/|P_j|` for PSD blocks.
3. Enforce the 27 forced-zero pair-orbit variables from the zero-count point orbits.
4. Solve reduced block SDP subproblems under current pair-count bounds, preferably with an objective maximizing the reduced PSD margin rather than a zero objective.
5. Choose integer branches from fractional `m_j` values, weighted by their effect on active small PSD blocks.
6. When an integer `m` is returned, check all rows exactly, build the full labelled moment matrix, and test PSD.
7. If non-PSD, derive a small exact square inequality and save the generating vector `v` together with normalized coefficients `(A,B,C)` and the identity tying it to `1152 v^T M v`.
8. If PSD, save the profile as the next target for point-level graph/color realization and then complete Wang support search.

The pilot should not use numerical conic infeasibility as a mathematical deletion. A mathematical branch deletion needs exact square inequalities or a replayable discrete certificate. A numerical conic result can still be used for variable choice and for discovering candidate inequalities.

## How to interpret outcomes

- An integer PSD pair profile would be a new concrete object, not a tensor algorithm. It should immediately move to point-level realization with fixed pair-orbit counts and all 417,199 Wang rows.
- A compact exact contradiction for the chosen count would be a real count-branch deletion and should be transported or pooled only where the exact statement applies.
- If the pilot keeps finding fractional conic survivors and non-PSD integer leaves without compact exact closure, the route has supplied useful structure but not a decisive branch result; effort should then shift toward either point-level realization/search or completion-aware constraints that connect occupation directly to fixed-A/B/C rank-one reconstruction.
