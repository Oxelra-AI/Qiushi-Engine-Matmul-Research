# related analysis replay and correction of related analysis's E11 trace-saturation obstruction

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

related analysis record reported a new `F_2` mechanism for the E11-core distinct branch: saturated invertible contractions give trace equations `tr(M(q)^{-1} X_s)=1` for terms selected by a rank-9 contraction. analysis replayed the reported compact near-miss contradiction, but analysis found that the replay used the same transposed coefficient convention that related analysis later corrected in `scripts/corrected_trace_instrument.py`. This note supersedes the analysis interpretation.

analysis script: [replay_a01_trace_obstruction.py](../code/replay_a01_trace_obstruction.py)  
analysis output: [near_miss_q49_replay.json](../results/trace_replay/near_miss_q49_replay.json)  
Corrected analysis script: [corrected_trace_core_survey.py](../../quotient_cores/code/corrected_trace_core_survey.py)  
Corrected analysis output: [corrected_trace_core_survey.json](../../quotient_cores/results/corrected_trace_core_survey/corrected_trace_core_survey.json)

## Correct trace convention

For a saturated invertible contraction

\[
M(q)=\sum_{s\in I_q} b_s c_s^T,\qquad |I_q|=9,
\]

the rank-one matrices satisfy

\[
\operatorname{tr}(M(q)^{-1} b_s c_s^T)=c_s^T M(q)^{-1}b_s=1.
\]

If the variables are the entries `X_s[b,c]` of `X_s=b_s c_s^T`, the linear coefficient is therefore `M_inv[c,b]`, not `M_inv[b,c]`. The latter is the wrong entrywise pairing used by the old analysis/analysis q49 certificate.

## Replayed support

The support was related analysis's near miss:

`[1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]`

The E11 core tensor was rebuilt as the rank-1 quotient of `T333` with shape `(8,9,9)`. analysis also checked that its reconstruction matches the stored COO core file.

## Corrected results

- Tensor identity alone remains consistent: rank 648, 648 equations, 1539 variables.
- The single saturated rank-9 contraction `q=49` has `I_q=[0,2,5,6,8,10,12,14,15]`.
- With the **wrong** coefficient `M_inv[b,c]`, q49 alone gives the old inconsistent 36-row certificate (27 tensor rows + 9 trace rows). This is not a valid tensor trace certificate.
- With the **correct** coefficient `M_inv[c,b]`, q49 alone is consistent: 657 equations, rank 656.
- With the **correct** coefficient and all 16 saturated rank-9 contractions, the near-miss support is still inconsistent. The extracted certificate has 122 rows: 90 tensor rows and 32 trace rows from q values `[42,43,57,70,71,87,94,151,186,214]`; XOR verification gives `coefficients_zero=true`, `rhs_one=true`.
- Corrected rank-21 controls pass: the sampled verified E11 rank-21 decompositions had 522 direct trace tests and zero corrected trace failures; their tensor+trace linear systems were consistent.

## Meaning

The single-q49 headline is false after the coefficient repair, but the broader saturated-trace mechanism remains mathematically real: coupled corrected trace equations reject the same near-miss support, while verified rank-21 controls remain compatible. This is useful route evidence, not a complete distinct-branch exclusion. Any future finite-field theorem must use the corrected coefficient, independent coverage reconstruction, and controls on all relevant codimension-one quotient cores.
