# bounded real optimization, degeneration evidence, and projected-kernel full-rank correction

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Research purpose

analysis found a real Levenberg--Marquardt path from a `cn122` one-term deletion with residual down to about \(2.23\times 10^{-4}\), but it did not track whether the factors remain bounded modulo the known term scalings and matrix-multiplication stabilizer.  The review note required that the numerical campaign remain bounded and that we stop chasing residual if the path shows noncompact cancellation.  This ARTIFACT added those diagnostics and used the sparse projected-kernel model to identify a second kind of false numerical solution.

No object produced here is a rank-22 algorithm or a rank-23 lower bound.  The value of the ARTIFACT is that two tempting numerical directions are now better understood and should not be overinterpreted.

## 1. Real LM path: residual falls while cancellation grows

Script:

- [lm_diagnostics.py](../../quotient_cores/code/lm_diagnostics.py)

Main partial output:

- [trajectory_partial.json](../../quotient_cores/results/lm_diagnostics_main/trajectory_partial.json)
- saved states: `state_after_ALS.npz`, `state_segment_01.npz`, `state_segment_02.npz`

I launched a segmented rerun from `cn122` with term 1 deleted, recording after each short LM segment:

- relative Brent residual;
- \(\|J^Tf\|_\infty\) and Jacobian singular values;
- term-balanced amplitude \(\sum_i\|u_i\|\|v_i\|\|w_i\|\);
- a diagonal-stabilizer normalized amplitude proxy;
- span and \(UV\)-pairing singular values.

The run was deliberately cancelled after two 500-evaluation LM segments because the trend was already clear:

| state | relative residual | term-balanced amplitude | diagonal-gauge amplitude | \(UV\) smallest singular value | median \(J\) band \(s_{526}\ldots s_{549}\) |
|---|---:|---:|---:|---:|---:|
| after ALS | \(1.6346\times10^{-2}\) | \(1.829\times10^4\) | \(1.082\times10^4\) | \(5.691\times10^{-2}\) | \(9.50\times10^{-4}\) |
| LM segment 1 | \(3.7547\times10^{-3}\) | \(2.620\times10^4\) | \(1.620\times10^4\) | \(5.602\times10^{-2}\) | \(2.69\times10^{-4}\) |
| LM segment 2 | \(2.1794\times10^{-3}\) | \(3.662\times10^4\) | \(2.452\times10^4\) | \(5.381\times10^{-2}\) | \(1.22\times10^{-4}\) |

The exact rank-23 `cn122` reference has term-balanced amplitude only about \(82.15\) and diagonal-gauge amplitude about \(77.95\).  The rank-22 LM path therefore uses enormous mutually cancelling rank-one terms: by segment 2, about \(3.66\times10^4\) total column norm cancels to a tensor of norm \(5.196\), a cancellation ratio about \(1.42\times10^{-4}\).  The residual decreased by a factor \(0.133\) from after ALS to segment 2, but the total term amplitude doubled and the diagonal-gauge amplitude also grew strongly.  The top terms by product norm at segment 2 are already roughly \(8017,7505,5249,3933,2034,1692,1505,1429\), each with projection onto the target direction only \(10^{-5}\) to \(10^{-4}\) after normalization.

This is not a bounded finite rank-22 candidate.  It is better interpreted as a numerical trace of a cancellation/degeneration phenomenon, similar in review to the earlier rank-23 fiber cancellation observations, although the present data do not prove a full Laurent/Puiseux family.  Therefore I did **not** continue to high precision or try algebraic reconstruction from this endpoint.

Important caveats:

- The diagonal stabilizer normalization is only a proxy; it does not minimize over the full non-diagonal \(GL_3^3\) stabilizer.
- Two LM segments are not a proof that every nearby optimization path is noncompact.
- The LM gradient/`optimality` remains nonzero and even increases over the recorded segments, so the current state is not a stationary local minimum.
- These numbers are not evidence that rank 22 is impossible.

The scientific use is to redirect effort: if we later extract a structured limit from this data, it should be treated as a candidate border/cancellation pattern, not as a finite rank-22 decomposition.

## 2. Structural extraction from the LM states

Script:

- [lm_path_structure.py](../../quotient_cores/code/lm_path_structure.py)

Output:

- [lm_path_structure.json](../../quotient_cores/results/lm_structure/lm_path_structure.json)

This script computed the projected-kernel rank condition on the same LM path.  For a full-rank rank-22 solution one needs
\[
\operatorname{rank}X=22,
\qquad
\operatorname{rank}(QX)=13,
\qquad
L=\operatorname{im}(T_{UV|W})\subseteq\operatorname{span}X,
\]
where \(Q\) is the sparse quotient annihilating \(L\).  Along the LM path:

| state | rank\((QX)\) by numerical tolerance | \(s_{14}(QX)\) | best-\(W\) inclusion residual |
|---|---:|---:|---:|
| after ALS | 22 | \(3.61\times10^{-1}\) | \(1.6346\times10^{-2}\) |
| LM segment 1 | 21 | \(1.49\times10^{-1}\) | \(3.7526\times10^{-3}\) |
| LM segment 2 | 21 | \(1.13\times10^{-1}\) | \(2.1778\times10^{-3}\) |

The path is moving some projected-kernel singular values downward while simultaneously increasing cancellation.  At segment 2 it is still far from the full-rank projected condition \(\operatorname{rank}(QX)=13\).  The near equality between Brent residual and fixed-\(U,V\) best-\(W\) residual shows that the obstruction is already in the \(UV\)-span inclusion, not just in poorly chosen \(W\).

review also pointed out that the smallest singular vector of the 22 term-column matrix, with coefficients near \(1/\sqrt{22}\), should not be mistaken for a new syzygy: it largely reflects the fact that the sum of the 22 huge columns is the small current approximation to \(T_{333}\).

## 3. Projected-kernel real search reaches a wrong low-\(X\)-rank branch

Scripts:

- [projected_kernel_real_search.py](../../quotient_cores/code/projected_kernel_real_search.py)

Outputs:

- [projected_kernel_cn122_drop_1_raw_pivqr_nfev1.json](../../exact_baselines/results/projected_kernel_pilot/projected_kernel_cn122_drop_1_raw_pivqr_nfev1.json)
- [projected_kernel_cn122_drop_1_raw_pivqr_nfev1000.json](../../exact_baselines/results/projected_kernel_real_search/projected_kernel_cn122_drop_1_raw_pivqr_nfev1000.json)

The projected-kernel equations were solved on a 13-column chart with all \(U,V\) factors and all pivot terms live:
\[
QX_{\mathrm{rem}}=QX_{\mathrm{piv}}C.
\]
A finite-difference check of the implemented Jacobian on sampled columns gave max error \(1.64\times10^{-9}\).

From raw `cn122` term-1 deletion, the projected residual went from \(9.32\times10^{-2}\) to machine precision \(1.40\times10^{-16}\) in 75 LM evaluations.  But the endpoint is not a rank-22 candidate:

- final \(\operatorname{rank}X=19\), not 22;
- final \(\operatorname{rank}(QX)=13\);
- fixed-\(U,V\) best-\(W\) residual is \(0.5773502691896258=1/\sqrt3\), worse than the start.

The dimension identity is
\[
\operatorname{rank}(QX)=\dim\operatorname{span}X-\dim(\operatorname{span}X\cap L).
\]
At the endpoint this gives \(19-13=6\), so only a six-dimensional subspace of the nine-dimensional target \(L\) is captured.  Thus the system solved a loose determinantal chart by collapsing \(X\), not by producing \(L\subseteq\operatorname{span}X\).  This exactly illustrates why the projected-kernel algebra must include the full-column-rank open condition for \(X\), not merely \(\operatorname{rank}(QX)\le13\).

The corrected exact algebraic object for this chart is the saturation
\[
\langle QX_R-QX_PC\rangle : (\Delta_X\Delta_P)^\infty,
\]
where \(\Delta_X\) is a nonzero \(22\times22\) minor of \(X\) and \(\Delta_P\) is the selected \(13\times13\) pivot minor of \(QX_P\).  Equivalently, introduce a left inverse \(Y\in K^{22\times81}\) and impose \(YX=I_{22}\) while keeping \(QX=AB\).  Only after this full-rank condition is enforced does \(\operatorname{rank}(QX)\le13\) force \(L\subseteq\operatorname{span}X\) for \(r=22\).

## 4. Exact cn122 relation-space data in the projected quotient

Script:

- [cn122_projected_relations.py](../../exact_baselines/code/cn122_projected_relations.py)

Output:

- [cn122_projected_relation_space.json](../../exact_baselines/results/projected_relations/cn122_projected_relation_space.json)

Exact rational/symbolic checks:

- \(Q T_{UV|W}=0\);
- \(XW^T=T_{UV|W}\) for `cn122`;
- \(QXW^T=0\);
- \(\operatorname{rank}_{\mathbb Q}X=23\), \(\operatorname{rank}_{\mathbb Q}(QX)=14\), \(\dim\ker(QX)=9\);
- \(\operatorname{rank}_{\mathbb Q} W^T=9\), with the same \(QX\) rank 14 over primes 3, 5, 7, 11, and 65521.

For every one-term deletion of `cn122`:

- \(\operatorname{rank}X_{\mathrm{keep}}=22\);
- \(\operatorname{rank}(QX_{\mathrm{keep}})=14\);
- \(\dim(\operatorname{span}X_{\mathrm{keep}}\cap L)=8\).

The dropped \(w_d\) vectors have matrix ranks 1 for 18 terms and 2 for 5 terms.  This exact relation-space picture explains why direct deletion is close but not a rank-22 solution: keeping 22 old \(UV\) columns leaves an 8-dimensional intersection with the target \(L\), while a true full-rank rank-22 solution requires all 9 target directions.

## 5. Updated research judgment

The real numerical campaign has now served its bounded purpose.  It should not continue as a residual-minimization chase unless a future method keeps factor amplitude controlled and directly enforces the full-rank projected-kernel condition.  The most defensible continuations are algebraic:

1. build a saturated projected-kernel chart with live factors and explicit \(X\)-rank open condition, using either a nonzero \(22\times22\) minor or left-inverse variables;
2. analyze lower-\(UV\)-rank strata as shorter minimal models rather than as singular 22-term projected-kernel charts;
3. if using the LM states, extract only a possible cancellation/degeneration leading structure from the largest term clusters, without calling it a finite algorithm;
4. preserve the exact cn122 relation-space data as a calibrated reference for any future 22-term candidate: a candidate must improve the intersection \(\operatorname{span}X\cap L\) from 8/9 to 9/9 while keeping \(\operatorname{rank}X=22\).
