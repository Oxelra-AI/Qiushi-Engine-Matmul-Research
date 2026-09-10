# correction to analysis pooled square-cut result

> Historical research record. Read with the [correction guide](../../../../corrections.md); recorded conclusions are not new verification receipts.

The cut coefficient file in this directory remains a useful artifact:

- `pooled_cuts_coefficients.json` contains 149 exact integer-coefficient square inequalities on `(n_a,m_j)` that are valid for every actual support average, provided the coefficient identity is reconstructed with the same orbit tables.

However the `meaning` field in `pooled_square_cuts_results.json` overstates the constraints used in the later CP-SAT phases. The script [pooled_global_square_cuts.py](../../code/pooled_global_square_cuts.py) explicitly sets `tri_ub_A=[]` and `tri_ub_b=[]` at lines 260--263, so Phase 3--5 did **not** add the 5,913 triangle/Fortet rows. The returned integer witnesses therefore need not satisfy the full analysis linear formulation.

The valid conclusion is only that these 149 cuts, in that incomplete later CP-SAT model, did not decide the six sampled count vectors. This does not prove that polyhedral PSD separation, conic-guided search, or the integer pair-count PSD route is exhausted. Every non-PSD rational moment assignment has a rational square separator; effectiveness is a computational/search question, not ruled out by analysis.

Use this sidecar correction together with [pooled_square_cuts_analysis.md](../pooled_square_cuts_analysis.md) and [reassessment_and_correction.md](../../../quotient_cores/notes/reassessment_and_correction.md) before citing analysis.
