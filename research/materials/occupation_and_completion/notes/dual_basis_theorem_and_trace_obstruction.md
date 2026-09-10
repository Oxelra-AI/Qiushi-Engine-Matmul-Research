# Correction notice (analysis)

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

The trace-obstruction and overlap-strengthening claims in this analysis note are superseded by [corrected_trace_reassessment.md](../../quotient_cores/notes/corrected_trace_reassessment.md). analysis used the wrong coefficient convention for trace rows: for `X=b c^T`, `tr(M^{-1}X)` uses `M_inv[c,b]` on `X[b,c]`, not `M_inv[b,c]`. The old single-`q=49` 36-row certificate and the six single-contraction trace contradictions are invalid as tensor evidence. The binary overlap bound is equivalent to the existing contraction lower bound `w(q1+q2) >= rank L(q1+q2)` when both rank-9 contractions are saturated. The certified repeated-direction reduction and other non-trace evidence are unaffected.

# Dual-Basis Theorem and Trace Obstruction for E11 Core

## Mathematical Result

### Dual-Basis Overlap Bound (General Theorem)

**Theorem.** Let T be a 3-tensor over a field K, and q₁, q₂ be linear
functionals on the first factor space such that L(q₁), L(q₂) are both
invertible (rank = n). In any decomposition T = Σₛ aₛ ⊗ bₛ ⊗ cₛ
where both contractions are saturated (|I_qᵢ| = n), the overlap satisfies

    |I_{q₁} ∩ I_{q₂}| ≤ ⌊(2n − rank(M₁⁻¹ − M₂⁻¹)) / 2⌋,

where Mᵢ = L(qᵢ) and subtraction is field addition in char 2.

**Proof sketch.** For saturated rank-n contractions, the participating B/C
factors form dual bases: C^T M⁻¹ B = I_n. For common terms in I₁ ∩ I₂,
both dual-basis conditions apply. Setting N = M₁⁻¹ − M₂⁻¹, the common
factors satisfy C_common^T N B_common = 0. Since B_common has k independent
columns, dim(im(N B_common)) = k − dim(ker(N) ∩ col(B_common)) ≤ 9 − k
(the dimension of null(C_common^T)). The minimum intersection of
ker(N) (dim 9−r) with col(B_common) (dim k) is max(0, k+9−r−9) = max(0,k−r).
The constraint k − max(0,k−r) ≤ 9−k gives k ≤ ⌊(18−r)/2⌋. □

### Application to E11 Core

For the E11 quotient core (8×9×9 over F₂), with 72 rank-9 contractions:
- 468 pairs have N-rank 3 → overlap ≤ 7
- 1512 pairs have N-rank 6 → overlap ≤ 6
- 576 pairs have N-rank 9 → overlap ≤ 4

**1676 out of 2556 rank-9 pairs give strictly stronger bounds than Wang.**
Verified on cn122 positive control (all pass).

### Trace Linear Obstruction

For a saturated rank-9 contraction q with invertible M = L(q), each
participating term s satisfies tr(M⁻¹ Xₛ) = 1 (where Xₛ = bₛcₛᵀ).
These are linear equations on the relaxed matrix variables.

**Key finding:** For the best near-miss support
`[1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]`,
the tensor identity (648 eqs) combined with trace equations from
saturated rank-9 contractions (144 eqs) is **INCONSISTENT** over GF(2).

The smallest contradiction uses only **36 equations**: 27 tensor identity
entries + 9 trace equations from a single contraction q=49. This is a
compact, verifiable GF(2) linear proof that the support has no valid B/C
completion — even without imposing rank-one!

**Per-contraction analysis:** 6 of 16 saturated rank-9 contractions
individually produce trace contradictions (q = 49, 70, 94, 179, 214, 241).
The cn122 positive control passes ALL 5 of its saturated rank-9 contractions.

### Significance

1. **Domain tests miss rank-9 contractions entirely** (full col/row spaces).
   The trace equations are the first mechanism to extract compatibility
   information from invertible contractions.

2. The trace obstruction is **algebraic** (GF(2) linear algebra), not
   combinatorial (Wang occupation). It uses the tensor structure directly.

3. The contradiction certificate is **compact and verifiable** by
   Gaussian elimination.

4. The trace test is **cheap** (O(n³) linear algebra) compared to the
   B/C rank-one completion CP-SAT (146 seconds for one support).

## Files

- [dual_basis_instrument.py](../code/dual_basis_instrument.py): core instrument
- [overlap_bound_analysis.py](../../quotient_cores/code/overlap_bound_analysis.py): Wang comparison
- [augmented_cpsat.py](../../quotient_cores/code/augmented_cpsat.py): augmented solver
- [trace_linear_system.py](../../quotient_cores/code/trace_linear_system.py): trace system builder
- [trace_contradiction.py](../../quotient_cores/code/trace_contradiction.py): certificate extractor
- [per_contraction_trace.py](../code/per_contraction_trace.py): per-q analysis

- [analysis.json](../results/dual_basis/analysis.json): cn122 validation
- [overlap_bounds.json](../results/dual_basis/overlap_bounds.json): Wang comparison
- [trace_linear_strengthening.json](../results/dual_basis/trace_linear_strengthening.json): rank gains
- [trace_contradiction_certificate.json](../../finite_certification/results/dual_basis/trace_contradiction_certificate.json): certificate
- [per_contraction_trace_test.json](../results/dual_basis/per_contraction_trace_test.json): per-q results

## Open Questions

1. Does every Wang-admissible 19-point distinct support fail the trace test?
   If yes, this proves R_F2(core_E11) ≥ 20 by a route independent of
   exhaustive Wang search.

2. Can the trace equations be encoded into the CP-SAT or CNF model to
   produce a proof-producing exclusion of the distinct branch?

3. Do the 6 inconsistent contractions have a structural relationship
   under the E11 stabilizer?

4. Can the dual-basis overlap bound (a general tensor theorem) contribute
   to lower bounds over larger fields?
