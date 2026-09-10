# pooled exact global square cuts: corrected scope

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## What the computation established

analysis extracted 149 exact global square inequalities from 12 PSD-failing integer pair-count assignments and saved them in

- [pooled_cuts_coefficients.json](../results/pooled_square_cuts/pooled_cuts_coefficients.json).

For any integer vector `v` on the labelled moment coordinates, the PSD condition gives the valid inequality

\[
1152 v_0^2 + \sum_a {1152\over |O_a|}(2v_0S_a+Q_a)n_a
 + \sum_j {1152\over |P_j|}R_j m_j \ge 0,
\]

where `S_a=sum_{p in O_a} v_p`, `Q_a=sum_{p in O_a} v_p^2`, and `R_j=sum_{{p,q} in P_j} 2 v_p v_q`. The saved cuts were verified by exact rational arithmetic at their source points.

When those 149 cuts were added to a CP-SAT integer pair-count model, the solver still found integer pair-count assignments for the six selected count vectors. The returned assignments were non-PSD.

## Important correction

The analysis result does **not** show that polyhedral PSD separation cannot decide the integer moment problem. The count variables range over a finite lattice, and every non-PSD rational assignment has a rational separating square. In principle a finite square family can separate all non-PSD lattice points, though it may be too large or too hard to find efficiently. The minimum eigenvalues of arbitrary CP-SAT vertices are not a convergence measure unless the search is directed to optimize a PSD-related quantity.

There is also a concrete implementation-scope issue. In [pooled_global_square_cuts.py](../code/pooled_global_square_cuts.py), lines 260--263 explicitly skip the 5,913 triangle/Fortet rows. Therefore the new Phase 3--5 witnesses need not satisfy the full analysis linear formulation, which included Wang RLT + triangle rows + deterministic block totals. The JSON `meaning` field in [pooled_square_cuts_results.json](../results/pooled_square_cuts/pooled_square_cuts_results.json) mentions triangle rows, but the script did not add them in the later CP-SAT phases. Future use should follow the script behavior, not that field.

## Correct interpretation

The safe conclusion is:

- The 149 inequalities are reusable exact valid inequalities on `(n_a,m_j)`.
- A small unguided pooled square-cut collection, tested without triangle rows in the later CP-SAT phases, did not decide the six sampled count vectors.
- The integer pair-count + PSD problem remains open.
- The fast analysis block SDP remains valuable because it can be used inside a conic-guided integer search rather than only as an after-the-fact separator for arbitrary CP-SAT vertices.

## Next useful connection

The most consequential untested connection is between the block SDP and the integer pair-count search. A bounded pilot should keep the complete analysis linear conditions and solve continuous block-SDP subproblems under partial integer-pair decisions. It should branch on fractional `m_j=|P_j|y_j`, derive exact rational square inequalities from non-PSD integer assignments, and treat numerical conic infeasibility as search evidence until it is backed by exact inequalities or a replayable discrete certificate.

A found integer PSD pair-count witness would be a concrete target for point-level graph/color realization. A compact exact contradiction for one fixed count branch would provide new branch information for the direct 255-variable support search. Neither outcome is a final tensor-rank result by itself; both would advance the E11 distinct projected-A branch.
