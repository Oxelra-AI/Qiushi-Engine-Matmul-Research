# RLT+PSD correction, repaired square cuts, and global status

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Research target connection

The unresolved finite-field branch is still the distinct 19-direction projected-A support for the E11 quotient core.  Any actual support gives an orbit-averaged pair-moment vector with variables
\[
  x_a \quad (a=0,\ldots,5),\qquad y_j\quad (j=0,\ldots,96),
\]
where the six point orbits have sizes
\[
  (6,9,36,72,36,96)
\]
and the 97 pair orbits are under the 1152-element E11 stabilizer.  The complete-Wang RLT model has 7 equalities and 183,302 upper-bound rows; adding repaired triangle/Fortet rows gives 189,215 upper-bound rows.

The moment matrix condition is: for
\[
\chi=(1,x_1,\ldots,x_{255}),
\]
an actual support, averaged over the stabilizer, yields a labelled matrix
\[
M_{00}=1,\quad M_{0p}=M_{pp}=x_p,\quad M_{pq}=y_{pq}\quad(p\ne q),
\]
which must be positive semidefinite.  Exact cardinality imposes the known kernel
\[
  M(-19,1,\ldots,1)^T=0.
\]

## Correction of analysis uniform inference

analysis correctly observed that the uniform extension
\[
  x_p=19/255,\qquad y_{pq}=\frac{19\cdot18}{255\cdot254}
\]
is PSD.  However, it does **not** satisfy the Wang RLT constraints.  The reason is that a capacity-one Wang subspace containing both points in a pair forces the corresponding conditioned pair moment to vanish; uniform positive \(y_{pq}\) violates these rows.

Regression artifact:

- Script: [uniform_rlt_regression.py](../code/uniform_rlt_regression.py)
- Output: [uniform_rlt_regression.json](../results/uniform_regression/uniform_rlt_regression.json)

Key numbers:

- complete RLT model: 183,302 upper-bound rows;
- uniform extension equality residual: `9.44e-16`;
- uniform extension RLT max violation: `0.029334568473058598`;
- number of RLT rows violated above `1e-10`: `21`;
- triangle rows alone are satisfied by the uniform extension: max violation `0.0`;
- cap-one diagnostic still shows forced-zero pair structure for point orbits 1, 3, and 5 (100, 8, and 12 forbidden partners respectively for the representatives in the saved diagnostic).

Therefore the statement “continuous RLT+PSD is feasible because the uniform point is PSD” is withdrawn.  Continuous RLT+PSD feasibility remains an open question.

## Repair of analysis PSD-cut coefficient extraction

analysis's `extract_orbit_cut` divided coefficients by orbit sizes but then evaluated them against normalized moment variables \(x_a=n_a/|O_a|\) and \(y_j=m_j/|P_j|\).  This made the exported reconstruction values positive even when the eigenvalues were negative.

For normalized variables, the correct expression is the **undivided orbit-sum** formula
\[
 v^TMv = v_0^2
 +\sum_a\left(2v_0\sum_{p\in O_a}v_p+\sum_{p\in O_a}v_p^2\right)x_a
 +\sum_j\left(2\sum_{\{p,q\}\in P_j}v_pv_q\right)y_j.
\]
The divided coefficients would instead be coefficients for the integer counts \(n_a,m_j\), not for normalized moments.

Repair artifacts:

- Script: [repair_moment_cut_extraction.py](../code/repair_moment_cut_extraction.py)
- Summary: [moment_cut_repair_summary.json](../results/moment_cut_repair/moment_cut_repair_summary.json)
- Full integer square cuts: `workspace/data/moment_cut_repair/integer_square_cuts.jsonl`

For the four analysis block-count witnesses, the corrected undivided reconstruction matches direct \(v^TMv\) to floating precision, while the old divided reconstruction is positive.  Integerized square cuts evaluate to exactly negative rationals on the corresponding rational count/pair witnesses:

| witness | min eigenvalue | old divided reconstruction | corrected reconstruction | exact integer square value |
|---|---:|---:|---:|---:|
| `feasibility_lex` | -0.1697461473 | +0.0005189210 | -0.1697461473 | `-340469/18` |
| `max_omitted` | -0.1483980339 | +0.0185596505 | -0.1483980339 | `-77987/9` |
| `min_omitted` | -0.0761660188 | +0.0019027149 | -0.0761660188 | `-2231921/288` |
| `force_zero_omitted` | -0.1409071034 | +0.0013263010 | -0.1409071034 | `-451651/18` |

Quantifier: each exact negative square value excludes that specific pair-moment witness \((n,m)\).  It does **not** exclude all pair distributions with the same point counts, and it does not by itself exclude the distinct E11 support branch.

## Global free-first-moment spectral separation

I built a global cutting-plane loop with the six first moments free:

- Script: [global_psd_cut_loop.py](../code/global_psd_cut_loop.py)
- Summary: [global_psd_cut_loop_summary.json](../results/global_psd/global_psd_cut_loop_summary.json)
- Full generated square cuts: `workspace/data/global_psd/psd_square_cuts.jsonl`

The linear model uses raw analysis RLT coefficients, not normalized/double-divided coefficients:

- 7 equalities;
- 183,302 RLT upper-bound constraints;
- 5,913 triangle/Fortet constraints;
- total initial upper-bound rows: 189,215;
- variables: 103.

The loop repeatedly solved the LP, found a negative labelled moment eigenvalue, integerized the eigenvector to a square inequality \(w^TMw\ge0\), and added it as a valid global linear cut.  After 20 square cuts:

- LP remained feasible;
- final LP residuals were at numerical tolerance (`max_ub_violation` about `3.6e-15`);
- the final moment matrix was still not PSD: min eigenvalue `-0.15466795742141565`, with 69 eigenvalues below `-1e-8`;
- final first-moment masses were approximately `[0.01956, 0.01877, 5.83533, 6.16701, 0.16471, 6.79461]` over point orbits.

This establishes only that twenty separated square cuts do not close the continuous relaxation.  It does not prove the continuous RLT+triangle+PSD system feasible or infeasible.  The generated cuts are reusable valid inequalities because they are square inequalities of the labelled moment matrix.

## Direct conic attempt

I wrote a direct SDP test with the known cardinality kernel removed:

- Script: [global_sdp_feasibility.py](../code/global_sdp_feasibility.py)
- Task: `s68_t17_tool1`
- Artifact directory: `workspace/tasks/s68_t17_tool1/`

It formulated a quotient PSD cone of dimension 255 for the global RLT+triangle model and used CLARABEL to maximize a lower bound on the minimum quotient eigenvalue.  CVXPY compiled quickly, but CLARABEL did not complete a numerical iteration before the 1800 s managed runtime limit.  There is no solver status and no feasibility/infeasibility evidence from this run beyond the observation that the naive direct conic formulation is computationally inefficient.

## Current scientific status after analysis

Valid changes from this ARTIFACT:

1. The analysis uniform-based continuous feasibility inference is false and withdrawn.
2. The analysis exported PSD-cut coefficient normalization was wrong; the corrected undivided formula has been validated, and four exact integer square inequalities exclude the four displayed analysis pair-count witnesses.
3. The labelled moment PSD condition is still a strong global realizability condition, but a 20-cut floating separation loop did not close the free-first-moment continuous RLT+triangle model.
4. A direct SDP with kernel removal timed out, so the continuous RLT+PSD feasibility question remains open.

No rank-22 exact algorithm, no E11 rank-19 core identity, and no completed exclusion of the distinct E11 branch was obtained.  The rigorous finite-field bound remains
\[
20\le R_{\mathbb F_2}(T_{\langle3,3,3\rangle})\le23.
\]

## Useful next work

The next valuable work should not resume the analysis count-vector sweep as if the continuous problem had been decided.  Better routes:

1. **Exploit symmetry of the PSD cone.**  Block-diagonalize the labelled moment matrix under the E11 stabilizer / association scheme, or otherwise reduce the PSD cone before another conic solve.  The quotient-basis CLARABEL formulation is too slow, but the matrix is invariant under the group and should decompose into smaller representation blocks.
2. **Continue separation only with purpose.**  More square cuts may be useful if they converge toward a small repeated family or an exact linear contradiction, but the 20-cut loop shows naive separation keeps finding different violated directions.
3. **If a numerical PSD-feasible moment is found, save the full 103-vector and inspect what first moments and pair masses it uses.**  Such a vector would not be a support; it would guide count integrality and point-level realization tests.
4. **If numerical infeasibility appears, do not use it as a theorem.**  It would need an exact certificate or a rational Farkas/SDP dual object that can be independently checked.
5. **Only after the continuous RLT+PSD situation is understood should the 34,335 count branches be treated as the main route.**  Any count-branch conclusion must preserve unresolved statuses and full pair witnesses.
