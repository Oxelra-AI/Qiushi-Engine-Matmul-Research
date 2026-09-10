# corrected tau-orbit walk and anti-sector exact branch

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Active purpose

this investigation goal remains the exact tensor rank of \(T_{\langle3,3,3\rangle}\): find an exact rank-22 algorithm or prove rank 23 optimal over a stated field.  This ARTIFACT stayed within the transpose-invariant structured layer
\[
\tau(A,B,C)=(A^T,C^T,B^T),
\]
which is only a subproblem of the unrestricted rank-one-span incidence.  It produced implementation corrections, finite-field search data, and a clearer mathematical target for the anti-sector; it did not solve the global rank problem.

## 1. Moosbauer--Poole prior-art lookup

The loaded Moosbauer--Poole paper `Knowledge/objects/papers/Flip-Graphs-with-Symmetry-and-New-Matrix-Multiplication-Schemes--d17460b7cf64--5fc3f1d97bb1/object.md` was checked around lines 104, 198, 263, and 294.  Their implemented symmetry groups are:

- \(C_3\), cyclic factor permutation;
- \(C_3\times\mathbb Z_2\), where the \(\mathbb Z_2\) reverses rows and columns inside every factor by conjugation with a backwards identity matrix.

That \(\mathbb Z_2\) is an inner row/column reversal, not the transpose-type factor swap \(\tau(A,B,C)=(A^T,C^T,B^T)\).  For \(n=3\), the paper reports reaching rank 23 with \(G=C_3\) and diagonal partitions, not a single transpose-type \(Z_2\) table.  Therefore their computation does not settle the present \(\tau\)-layer; it only supplies the orbit-flip/orbit-plus transition framework.

## 2. Corrected clean tau-orbit flip

The first analysis script [tau_naive_flip_walk.py](../code/tau_naive_flip_walk.py) implemented the wrong image update: it applied the ordinary flip-cpd `NEXT/PREV` update to the tau-image pair.  review verified the correction: for two terms \(x,y\) in distinct free \(\tau\)-orbits, first apply the ordinary flip to \((x,y)\), obtaining \((u,v)\), then replace the image pair by \((\tau u,\tau v)\).  Because \(x+y=u+v\) and \(\tau x+\tau y=\tau u+\tau v\), the four-term orbit replacement preserves the tensor exactly and preserves \(\tau\)-invariance by construction.

The corrected script is

- [tau_orbit_sample_walk.py](../code/tau_orbit_sample_walk.py).

A pilot run saved

- [tau_orbit_sample_walk_summary.json](../results/tau_orbit_walk/tau_orbit_sample_walk_summary.json).

It verifies the standard seed over \(\mathbb F_3\):

- rank/raw nonzero count 27;
- exact equality to \(T_{333}\) over \(\mathbb F_3\);
- \(\tau\)-skeleton \((f,m)=(9,9)\);
- 162 ordered duplicate-factor pairs in the standard seed;
- exactly 72 clean free-free one-ARTIFACT orbit flips, all rank-preserving at raw count 27.

The earlier [tau_naive_walk_summary.json](../results/tau_naive_walk/tau_naive_walk_summary.json) should be read only as evidence for the old formula's failure, not as graph evidence.

## 3. Weighted/projective normalization layer

review pointed out that raw nonzero slot count can overcount a decomposition over \(\mathbb F_3\): duplicate projective pure tensors may merge with coefficients, a two-orbit may collapse to a fixed term, and coefficients may cancel.  I therefore added

- [tau_normalized_onestep.py](../code/tau_normalized_onestep.py);
- [tau_normalized_onestep.json](../results/tau_orbit_walk/tau_normalized_onestep.json).

This enumerates all 72 corrected clean one-ARTIFACT moves from the standard seed and canonicalizes each pure tensor projectively with its \(\mathbb F_3\) coefficient before merging.  Results:

- standard seed: raw rank 27, merged length 27, skeleton \((9,9)\), dense replay true;
- all 72 clean one-ARTIFACT moves: raw rank 27, merged length 27, weighted skeleton \((9,9)\), weighted tau-invariance true, dense replay true;
- projective duplicate ordered-pair count drops from 162 at the seed to 146 after any one clean one-ARTIFACT move, but no hidden one-ARTIFACT reduction appears.

Thus the corrected walk has nontrivial edges but no rank reduction at distance one.  This is a local calibration only.  The long background run `s64_t12_tool1` timed out after 1800 s with no stdout, so it contributes no search result.

Open implementation work before any large walk has scientific meaning:

1. use projective shared-factor buckets in the walk, not only exact vector equality;
2. maintain a weighted projective multiset and merged length after every ARTIFACT;
3. handle orbit collapse and output-orbit coincidence explicitly;
4. add orbit plus-transitions or legal splitting, because clean free-free flips keep the standard seed's fixed terms frozen and are unlikely to reproduce the full symmetric-flip search dynamics.

## 4. Anti-sector exact problem

For the \(\tau\)-fixed variable split, the complementary/anti target is the 3-plane
\[
L_{\rm anti}=\left\langle-\sum_k e_{0k}\wedge e_{1k},
-\sum_k e_{0k}\wedge e_{2k},
-\sum_k e_{1k}\wedge e_{2k}\right\rangle
\subset\Lambda^2(K^3\otimes K^3).
\]
Equivalently,
\[
L_{\rm anti}=\Lambda^2U\otimes\langle q\rangle,
\qquad q=c_0^2+c_1^2+c_2^2.
\]
Let \(m_0\) be the smallest number of decomposable bivectors \(p_j\wedge q_j\) whose span contains \(L_{\rm anti}\).  The rigorous state remains
\[
7\le m_0\le 9\qquad(\operatorname{char}K\ne2).
\]
The lower bound is analysis's A-wedge flattening: [anti_Awedge_integer_det.json](../results/transpose_component/anti_Awedge_integer_det.json) gives determinant \(8=2^3\), and each structured term has flattening rank at most 4.  The upper bound is the canonical nine columnwise wedges.

## 5. analysis finite-field anti data

New scripts/results:

- [anti_rank_drop_probe.py](../../quotient_cores/code/anti_rank_drop_probe.py) -> [anti_rank_drop_probe_F3.json](../../quotient_cores/results/anti_exact/anti_rank_drop_probe_F3.json);
- [anti_subspace_local_search.py](../../quotient_cores/code/anti_subspace_local_search.py) -> [anti_subspace_local_m8_F3.json](../../quotient_cores/results/anti_exact/anti_subspace_local_m8_F3.json) and corrected `anti_subspace_local_m7_F3.json`;
- [anti_projective_enum.py](../../quotient_cores/code/anti_projective_enum.py) -> [anti_projective_enum_F3.json](../../quotient_cores/results/anti_exact/anti_projective_enum_F3.json);
- [anti_beam_search.py](../../quotient_cores/code/anti_beam_search.py) -> [anti_beam_m7_F3.json](../../quotient_cores/results/anti_exact/anti_beam_m7_F3.json).

Important interpretation corrections:

- The initial `m=7` local-search script had a canonical seeding bug: it dropped only one of nine canonical pairs for every \(m<9\), so old `m=7` best states could contain eight pairs.  review caught this.  The script was patched to seed true \(m\)-subsets and assert `len(pairs)==m`; the saved `anti_subspace_local_m7_F3.json` now records the corrected run.
- The projective enumeration with `sample_mod=9` is a systematic sample of 896,626 RREF 2-planes, not the full \(|G(2,9)(\mathbb F_3)|=8,069,620\) enumeration.
- Random/local misses over \(\mathbb F_3\) do not exclude \(\overline{\mathbb F}_3\), characteristic zero, or even all \(\mathbb F_3\)-points unless the search is exhaustive with a replayable certificate.

Concrete finite-field observations:

- canonical nine-term anti expression contains \(L_{\rm anti}\);
- deleting any one of the nine canonical wedges leaves defect 1;
- corrected direct local search for \(m=8\): no hit, best defect/ranks `[1,8,9]`;
- corrected direct local search for \(m=7\): no hit, best defect/ranks `[1,7,8]`;
- 1/9 projective RREF sample: no sampled decomposable bivector lies in \(L_{\rm anti}\) (`zero_quotient_projective_count=0`), canonical quotient rank is 6, all canonical eight-of-nine subsets have defect 1;
- rank-drop probe: among 50,000 random structured terms, 852 have `rank(F_T-F_term)=24`, so this necessary condition for a seven-term decomposition is not selective enough by itself.

## 6. The anti theorem route is still open

review judged that current evidence does not justify asserting \(m_0=9\).  The expected secant dimension for the Segre--Grassmann model \(\mathbb P^2\times G(2,9)\) does not make seven terms implausible, and local finite-field misses are weak.  If \(m_0=9\) is true, the likely proof must use the target's special kernel/radical structure rather than the current flattening alone.

Most promising exact directions:

1. kernel syzygy approach for the constant-rank plane \([x]_\times\otimes I_3\), whose kernel bundle is \(\mathcal O(-1)^3\);
2. column-block cancellation invariants using \(W=U\otimes C=U_0\oplus U_1\oplus U_2\), where any compression below nine must share decomposable bivectors across columns while canceling cross-column blocks;
3. complete \(\mathbb F_3\) quotient-flat search over all 8,069,620 projective decomposable bivectors, then search 4- or 5-dimensional quotient flats for possible \(m=7,8\) configurations, with original-lift replay;
4. stronger mixed Segre--Grassmann/Young flattenings whose target-rank to single-term-rank ratio exceeds 8.

## 7. research-group exchange

The related calculation concerns the \(\mathbb F_2\) E11 quotient RLT/triangle aggregation.  The comparison keeps the characteristic-not-2 \(\tau\) work separate and noting the shared methodological issue: invariant variables or terms must merge orbit/projective duplicates with coefficients, rather than treating labelled objects independently.

## 8. Consequence for the global goal

This ARTIFACT did not find a rank-22 algorithm and did not prove a rank-23 lower bound.  It improved the transpose-layer research state by:

- identifying that Moosbauer--Poole did not already run the relevant transpose-type \(Z_2\) table;
- correcting the tau-orbit flip implementation and showing standard naive_27 has 72 exact clean one-ARTIFACT edges over \(\mathbb F_3\);
- adding projective weighted normalization and verifying no hidden one-ARTIFACT reduction;
- tightening the finite-field anti-sector evidence while correcting the \(m=7\) provenance bug;
- clarifying that the anti branch needs theory or exhaustive quotient-flat computation, not more unstructured local search.

## supersession notice

analysis supersedes the anti-sector interpretation in this note. The analysis finite-field local searches missed the correct noise-canceling eight-bivector configuration. After transporting Laderman's `Phi_3 Phi_4` symmetry to standard `tau`, exact computations over `Q(i)`, `F_65521`, and via scaled congruence over `F_3,F_5,F_7,F_11,F_13` show that the eight free-orbit representative bivectors span `L_anti`. Thus over those fields the current range is `7 <= m_0 <= 8`, not `7 <= m_0 <= 9` with no known eight-witness. See [transported_laderman_tau_correction.md](../../exact_baselines/notes/transported_laderman_tau_correction.md) and [laderman_8bivector_certificate_Qi.json](../../exact_baselines/results/transport_laderman_tau/laderman_8bivector_certificate_Qi.json).
