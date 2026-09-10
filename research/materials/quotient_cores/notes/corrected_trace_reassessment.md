# corrected trace-functional convention and rebuilt trace evidence

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Why analysis's trace certificate had to be corrected

For a saturated rank-9 contraction of the E11 core over `F2`, let

\[
M_q=L(q)=\sum_{s\in I_q} b_s c_s^T,
\qquad X_s=b_sc_s^T .
\]

If `|I_q|=9` and `M_q` is invertible, the participating `B` and `C` factors satisfy

\[
C_q^T M_q^{-1} B_q=I_9,
\]

so each participating term obeys

\[
c_s^T M_q^{-1} b_s=\operatorname{tr}(M_q^{-1}X_s)=1.
\]

With entries `X_s[b,c]`, this trace is

\[
\operatorname{tr}(M_q^{-1}X_s)=\sum_{b,c}(M_q^{-1})_{c,b} X_s[b,c].
\]

analysis used `(M_q^{-1})[b,c]` instead of `(M_q^{-1})[c,b]`.  The transpose is not cosmetic: the old equations compute the wrong Frobenius pairing unless the inverse is symmetric in the relevant coordinates. Therefore the analysis single-`q=49` 36-row certificate and the statement that six single contractions individually reject the near-miss are not valid tensor-decomposition evidence.

## Controls validating the corrected convention

Main files:

- corrected instrument: [corrected_trace_instrument.py](../code/corrected_trace_instrument.py)
- corrected output: [correction_manifest.json](../results/corrected_trace/correction_manifest.json)
- corrected certificate extractor: [corrected_trace_certificate.py](../../finite_certification/code/corrected_trace_certificate.py)
- compressed support-level trace system: [trace_compressed_support.py](../../occupation_and_completion/code/trace_compressed_support.py)
- random exact controls: [random_trace_control.py](../code/random_trace_control.py)

Checks performed:

1. **Actual cn122 E11 core terms.**  For the five saturated rank-9 contractions of the exact cn122 E11 core, all 45 actual participating terms satisfy the corrected trace equation. The old analysis pairing disagrees with the direct value in 16 of those 45 term tests.

2. **Nonsymmetric synthetic saturated decompositions.**  Thirty random exact decompositions of invertible 9-by-9 matrices as `B C^T` were generated. The corrected trace pairing had zero failures; the old analysis pairing disagreed with the direct `c^T M^{-1} b` value 136 times.

3. **Random exact tensor controls with the same A-support.**  Forty random exact tensors were generated from the analysis near-miss A-support by choosing random nonzero `B,C` factors. Among 155 saturated rank-9 contractions found in 37 trials, the corrected trace rows had zero failures on the known term matrices; the old analysis pairing disagreed 688 times.

4. **`q=49` explanation.**  In row-major full matrix coordinates, core functional `q=49=0x31` corresponds to `E12+E23+E31`, the 3-cycle matrix

\[
Q=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix},
\]

and `L(q)=Q^T \otimes I_3`. The corrected pairing gives `tr(M^{-1}M)=tr(I_9)=1` over `F2`; the old entrywise pairing gives 0. Thus summing the nine malformed analysis rows necessarily created a false contradiction when `w(q)=9`.

## What remains true after correction

For the analysis near-miss support

`[1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]`,

using corrected trace rows:

- the tensor-only relaxed `X_s` system has 648 equations, rank 648, and is consistent;
- each one of the 16 saturated rank-9 contractions is individually consistent when added alone;
- the full set of corrected trace rows from all 16 saturated rank-9 contractions is inconsistent: 792 rows, rank 732;
- one verified XOR certificate for the corrected full trace system uses 122 rows: 90 tensor-coordinate rows and 32 trace rows involving 10 contractions;
- exhaustive subset search over these 16 saturated contractions found no inconsistent subset of size at most 7; the first inconsistent subsets appear at size 8.

Thus the near-miss still fails a genuine corrected trace linear relaxation, but only through **multi-contraction coupling** of the same `X_s` variables. It is not a one-contraction obstruction.

The compact support-level system in `compressed_trace_support_system.json` reproduces the same consistency outcomes for checked subsets while using variables `y_{q,s}=tr(M_q^{-1}X_s)` and trace-functional dependencies instead of 19×81 matrix variables. For the near-miss it uses 304 variables and 424 rows, has trace-functional rank 8 among 16 saturated contractions, and is inconsistent. This gives a useful small representation for investigating corrected trace compatibility without launching a global CNF expansion.

## One-contraction trace condition

For a single saturated invertible contraction `q`, define

\[
\phi_q(X)=\operatorname{tr}(M_q^{-1}X),\qquad g_q(i)=\phi_q(T_i).
\]

After setting `z_s=1` for the nine participating terms, the remaining variables can solve the projected tensor equations only if

\[
g_q+\sum_{s\in I_q} a_s \in \operatorname{span}\{a_s:s\notin I_q\}.
\]

For the near-miss, all 16 saturated rank-9 contractions satisfy this automatically because the ten outside A-points span the 7-dimensional hyperplane `ker(q)`. A complete scan of subspaces inside rank-9 kernels shows this automatic behavior is not forced by a single Wang row alone: proper subspaces of dimensions 5 and 6 inside rank-9 kernels can have stored lower bound `L=9`, so 10 outside points in such a proper subspace are not immediately excluded by the corresponding row. Genuine single-`q` trace cuts could occur only when the outside points fail to span `ker(q)` and the displayed vector lies outside their span. Existing stored near-misses show zero such one-`q` failures.

## Overlap-bound reinterpretation

The analysis overlap bound is not an independent new restriction in the binary E11-core model once contraction lower bounds are already included. Over `F2`, for invertible contractions,

\[
M_1^{-1}+M_2^{-1}=M_1^{-1}(M_1+M_2)M_2^{-1},
\]

so

\[
\operatorname{rank}(M_1^{-1}+M_2^{-1})=\operatorname{rank}L(q_1+q_2).
\]

If both `q1,q2` are saturated with weight 9 and their overlap is `k`, then

\[
w(q_1+q_2)=18-2k.
\]

The overlap inequality is therefore exactly equivalent to the existing contraction lower bound

\[
w(q_1+q_2)\ge \operatorname{rank}L(q_1+q_2).
\]

The script verified zero failures of this rank identity over all 2556 rank-9 pairs and zero failures of the overlap/contraction equivalence over the 120 saturated rank-9 pairs of the near-miss.

## Existing candidate batch after correction

The corrected trace filter was run on 31 already stored distinct near-misses from the analysis completion batch. All of these candidates are still Wang-inadmissible, so this is local evidence only. Results:

- 15/31 are inconsistent under corrected trace rows;
- 16/31 remain corrected-trace consistent;
- all one-contraction support-level trace tests pass in this batch;
- among the first six candidates, the compressed support-level system and full matrix-variable trace system agree on consistency in every checked case.

This means corrected trace compatibility is useful but not a substitute for Wang admissibility, saturated-domain tests, transversality, quotient-rank tests, or exact rank-one completion. In particular, the analysis round-12 candidate has repaired rank-one completion infeasible from analysis but is corrected-trace consistent, so trace is only one layer of B/C compatibility.

## Replaced / invalidated analysis claims

The following analysis statements are replaced by this correction:

- the single-`q=49` 36-row trace contradiction is invalid as tensor evidence;
- the six single-contraction trace contradictions are invalid;
- the overlap bound should not be treated as new separating power in the `F2` Wang-plus-contraction model;
- related analysis's replay of the old generated equations verified the same malformed rows, not their tensor meaning.

The certified repeated projected-A reduction from analysis, the analysis bridge to a future `R_F2(T)>=21` proof, the analysis annihilator-weight Wang reformulation, and the repaired analysis fixed-A rank-one completion remain unaffected.

## Scientific state after correction

The distinct E11-core branch remains open. The analysis near-miss is still locally rejected by corrected multi-contraction trace linear compatibility, but it already violates 12 complete Wang rows. No complete-Wang-admissible distinct support, no rank-19 E11 core decomposition, and no proof-producing distinct-branch exclusion has been obtained. The worthwhile trace direction is now narrower and more precise: study support-level coupled trace-functional dependencies and their interaction with domains for candidate supports, while continuing the exact occupation/hybrid Wang work needed to settle the distinct branch.

## Additional exact block-structure check

After the review review suggested making the coordinate convention even more explicit, I verified the full E11-core contraction structure in [core_kron_trace_structure.py](../code/core_kron_trace_structure.py), with output [correction_manifest.json](../results/corrected_trace/correction_manifest.json):

- for all 255 nonzero core functionals `q`, if `Q` is the corresponding `3×3` matrix with `Q_11=0`, then `L(q)=Q^T \otimes I_3` in the current row-major conventions;
- `rank L(q)=3 rank Q` for all 255 functionals, reproducing the `{3:33, 6:150, 9:72}` distribution;
- for all 72 invertible `Q`, the corrected trace coefficient matrix is the transpose of `L(q)^{-1}`, equivalently `Q^{-1}\otimes I_3` on `X[b,c]` under the current flattening;
- `g_q(i)=tr(L(q)^{-1}T_i)` equals the core mask of `Q^{-T}` for every invertible `q`;
- the 72 corrected trace functionals have rank 9 as 81-entry masks, while the corresponding `g_q` masks span the full 8-dimensional core A-space.

This removes the remaining indexing ambiguity around `contraction_matrix`, `var_idx(s,b,c)`, and qmm `v/w` direction for the corrected trace rows. It also shows that future coupled-trace work can be represented by small `3×3` inverse-matrix data rather than generic 81-entry matrices.
