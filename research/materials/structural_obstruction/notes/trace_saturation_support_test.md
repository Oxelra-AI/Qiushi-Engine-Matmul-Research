# support-level tight-contraction test for the corrected trace mechanism

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

This note records the finite-field computation following the corrected trace convention.  For a quotient core over `F2`, a contraction by `q` gives a `9 x 9` matrix `M(q)`.  If `rank M(q)=9` and a putative rank-19 core decomposition is tight at `q`, then the nine active terms are not only constrained by the diagonal trace equations

\[
\operatorname{tr}(M(q)^{-1}X_s)=1,
\]

but by the full spectral-resolution equations

\[
 c_s^T M(q)^{-1} b_{s'}=\delta_{ss'}.
\]

The diagonal trace row uses coefficient `M^{-1}[c,b]` on the variable `X[b,c]`; the earlier `M^{-1}[b,c]` convention is not tensor-correct.  related analysis record and related analysis analysis agree on this correction.  related analysis record further reports that the trace-parity shadow is 9-dimensional and useful only under certificate-specific guards, not as a full-72 family theorem.

The first question is whether tight invertible contractions are forced already at the support level.  For each nonzero quotient A-vector `a`, define

\[
\nu(a)=\#\{q: \operatorname{rank}M(q)=9,\ \langle q,a\rangle=1\}.
\]

For a support multiset `A={a_s}`,

\[
\sum_s\nu(a_s)=\sum_{q\,\mathrm{inv}} |I_q|,
\qquad |I_q|\ge 9.
\]

With 72 invertible contractions in each quotient core, the number of saturated invertible contractions is at least

\[
72-\left(\sum_s\nu(a_s)-648\right).
\]

Thus a universal support-level saturation theorem by this count would require all admissible rank-19 supports to have `sum_nu <= 720`.

The script [trace_saturation_test.py](../code/trace_saturation_test.py) computed the raw contraction data and `nu` distributions.  The script [trace_support_lp.py](../../occupation_and_completion/code/trace_support_lp.py) solved the complete Wang occupation linear relaxation with all 417,199 core inequalities.  Output is in [trace_test_lp.json](../results/trace_saturation_test/trace_test_lp.json).  The key results are:

| core | `nu` distribution | LP max `sum_nu` with Wang + contraction-rank rows | LP no-saturation feasibility |
|---|---:|---:|---:|
| E11 | `{32:81,36:96,40:72,48:6}` | `820.0` | feasible, `sum_nu≈731.686`, min rank-9 hit `10` |
| E12+E21 | `{40:85,44:96,48:55,52:16,56:3}` | `963.145652908` | feasible, `sum_nu≈890.409`, min rank-9 hit `10` |
| H3 | `{36:84,40:98,44:52,48:21}` | `871.829083672` | feasible, `sum_nu≈810.299`, min rank-9 hit `10` |

For E11 the verified eight quotient orbits have constant `nu` values

\[
(48,48,32,40,32,32,40,36)
\]

on the orbits of sizes `(3,3,9,36,36,36,36,96)`.  This confirms invariance under the corrected 576-element quotient action and shows directly why the average-value heuristic is not enough to force saturation.

I also ran [no_saturation_lazy_runner.py](../code/no_saturation_lazy_runner.py) for E11 with longer CP-SAT iterations, with copied output [no_saturation_long_lazy_E11.json](../results/trace_saturation_test/no_saturation_long_lazy_E11.json).  The lazy integer search repeatedly found rank-19 integer supports satisfying point/line Wang cuts, all contraction-rank rows, and zero saturated invertible rank-9 contractions; representative iterations had rank-9 hit histograms such as `{10:42,12:24,14:6}` and `{10:19,11:27,12:12,13:12,14:1,15:1}`.  Each such support still violated some higher Wang inequalities, and the run ended `UNKNOWN` after six iterations.  Therefore no complete integer no-saturation support has been established.

Scientific interpretation: the corrected independent-verification-record mechanism is algebraically stronger than the diagonal trace rows, but tight invertible contractions are not forced by the current cheap support relaxations.  The LP no-saturation solutions for all three quotient cores show that the counting argument alone cannot justify building a standalone trace-only lower-bound route.  The right computational role is to add trace, orthogonality, or parity consequences as conditional cuts inside the distinct-branch support/CPD search, while keeping exact coverage and certificate provenance separate.  The one-line quotient route can at best improve the full-tensor finite-field interval to `R_F2(T333)>=22`, and even `>=21` would require all three quotient cores to exclude rank <=19.

## Algebra controls for the stronger spectral layer

The script [spectral_resolution_controls.py](../../quotient_cores/code/spectral_resolution_controls.py) checks the full tight-contraction and defect-one identities on sampled verified rank-21 decompositions for all three quotient cores.  Output is copied to [spectral_resolution_controls.json](../results/trace_saturation_test/spectral_resolution_controls.json).

Aggregated over 12 verified rank-21 schemes per core, the controls found no failures:

- E11: rank-3 tight tests `29`, rank-6 tight tests `46`, rank-9 tight tests `58`, rank-9 defect-one tests `137`, all with zero failures.
- E12+E21: rank-3 tight tests `26`, rank-6 tight tests `38`, rank-9 tight tests `96`, rank-9 defect-one tests `147`, all with zero failures.
- H3: rank-3 tight tests `12`, rank-6 tight tests `11`, rank-9 tight tests `56`, rank-9 defect-one tests `164`, all with zero failures.

For a tight rank-`rho` contraction the checked matrix was

\[
\Gamma_{st}=c_s^T N b_t,
\]

with `N` any generalized inverse satisfying `M N M=M`; the tests confirmed `Gamma=I_rho`.  For a rank-9 contraction with ten hitters, the checked matrix was `Q=C^T M^{-1}B`; in all sampled cases `Q^2=Q`, `rank(Q+I)=1`, and all `2 x 2` minors of `Q+I` vanished.  These are positive controls for future guarded graph/SAT cuts.  They do not imply the layer fires globally, because the support-level test above shows tight invertible contractions are not forced by the current relaxations.
