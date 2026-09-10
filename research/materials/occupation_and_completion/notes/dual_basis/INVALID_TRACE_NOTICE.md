# Invalidated analysis trace artifacts

> Historical research record. Read with the [correction guide](../../../../corrections.md); recorded conclusions are not new verification receipts.

analysis corrected the trace-functional coefficient convention. analysis used `M_inv[b,c]` as the coefficient on `X[b,c]`. For `X=b c^T`, the correct trace row is

`tr(M_inv X) = sum_{b,c} M_inv[c,b] X[b,c]`.

Therefore the analysis files `trace_linear_strengthening.json`, `trace_contradiction_certificate.json`, and `per_contraction_trace_test.json` do not have the tensor-decomposition meaning previously claimed. In particular, the 36-row single-`q=49` certificate and the six single-contraction contradictions are invalid as evidence. Use the corrected artifacts in `data/corrected_trace/` and the note [corrected_trace_reassessment.md](../../../quotient_cores/notes/corrected_trace_reassessment.md).

The analysis repeated projected-A certificate and the analysis annihilator-weight Wang reformulation are unaffected.
