# corrected E11 bridge and tight rank-weight geometry

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

research: research_record.  Field: \(\mathbb F_2\).  Object: exact rank of \(T_{\langle3,3,3\rangle}\) and the E11 quotient core.

## 1. Bridge correction

The analysis bridge note had a serious quantifier reversal.  The inherited earlier research analysis bridge says the proof-producing Wang branches exclude length-20 full decompositions whose A-support has **no** rank-one factor.  Hence any full length-20 decomposition must contain at least one rank-one A-factor.  It does **not** say no factor is rank-one.

Correct normalized bridge:

1. Wang's verified lower bound gives \(R_{\mathbb F_2}(T)\ge20\).  Thus a rank-\(\le20\) counterexample to the desired lower bound would have length exactly 20.
2. The no-rank-one-support Wang/DRAT branches imply such a length-20 decomposition has a rank-one A-factor.
3. By the matrix-multiplication tensor symmetry, normalize that factor to \(E_{11}\).
4. The one-dimensional Wang row for \(\langle E_{11}\rangle\) has length-20 capacity one, so after quotienting by \(\langle E_{11}\rangle\) exactly nineteen nonzero terms remain.
5. These nineteen terms decompose the E11 quotient core.  The repeated-projected-A certificate applies to these nineteen projected factors.  Therefore the still-open lower-bound branch is the distinct length-19 E11 core, or more sharply the distinct length-19 E11 core together with a lift residual of rank at most one.

I corrected [e11_bridge_reconstruction.md](e11_bridge_reconstruction.md) to reflect this.  The outdated twenty-projected-term formulation should not be used as the inherited bridge.

## 2. Local check of inherited proof assets

I ran a live replay of the compact repeated-projected-A proof:

```text
drat-trim data/repeat_branch_certificate/iis_shrink_p1/fixed_repeat_p1_iis.cnf data/repeat_branch_certificate/iis_shrink_p1/drat/fixed_repeat_p1_iis.drat
```

It returned `s VERIFIED`, parsing 24,895 variables and 53,255 clauses, with verification time 23.535 s.  This is a earlier research-local replay for the repeated E11 core branch.  I also wrote and ran [check_corrected_bridge_assets.py](../code/check_corrected_bridge_assets.py); it inspected hashes, metadata, old `drat-trim` logs, and branch semantics for the two large no-rank-one full-support branches and the repeated projected-A branch.  Output:

[corrected_bridge_assets.json](../results/bridge_asset_checks/corrected_bridge_assets.json)

The manifest reports:

- rank-3-only branch metadata has `rank_s=20`, allowed rank histogram `{3:168}`, and old `drat-trim` log verified;
- rank-2/rank-3 no-rank-one branch metadata has `rank_s=20`, allowed rank histogram `{2:294,3:168}`, and old `drat-trim` log verified;
- repeated-projected-A E11 core review passed, and the compact proof was replayed in analysis.

This does not resolve the distinct length-19 E11 core.  It only restores the bridge dependencies to the correct meaning.

## 3. Koszul task was deliberately not run

The proposed Koszul flattenings \(\wedge^p\mathbb F_2^8\otimes\mathbb F_2^9\to\wedge^{p+1}\mathbb F_2^8\otimes\mathbb F_2^9\) have the a priori ceiling
\[
\left\lceil\frac{9\min\{\binom8p,\binom8{p+1}\}}{\binom7p}\right\rceil\le 15.
\]
They cannot reach the proposed 18–19 threshold or improve the already inherited lower bound \(R(T_{\rm core})\ge17\).  A small value would not change the route.  Compute time was therefore spent on the bridge and tight factor geometry instead.

## 4. Tight rank-weight geometry experiment

The scalar contraction inequality for a 19-term E11 core is
\[
|I_q|=|\{t:\langle q,a_t\rangle=1\}|\ge \operatorname{rank}(T_{\rm core}(q)) = 3\operatorname{rank}(\Lambda_q),\qquad 0\ne q\in\mathbb F_2^8,
\]
where \(\Lambda_q\in\{\Lambda:\Lambda_{11}=0\}\).  If equality holds, the active B-factors lie in the column space of \(T_{\rm core}(q)\), and the active C-factors lie in its row space.  Intersecting these spaces across tight contractions gives term domains.

I implemented this in:

- [tight_rank_geometry_pilot.py](../code/tight_rank_geometry_pilot.py)
- output [tight_rank_geometry_pilot.json](../results/tight_rank_geometry/tight_rank_geometry_pilot.json)

Calibration results:

- The verified cn122-derived 21-term core positive control has 9 tight contractions, no undersaturated contractions, domains `{B3_C3:3, B6_C6:12, B9_C9:6}`, passes the linear fixed-domain test, and the actual B/C factors lie in the computed domains.
- The old earlier research L15 near-complete support `[1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]` satisfies all 255 scalar rank-weight inequalities.  It has 16 tight contractions, all of matrix rank 3, and all term domains remain `B9_C9`.  Hence tight rank-weight geometry adds no B/C restriction to this particular near support, even though the old complete Wang scan says it still has 12 complete-Wang violations of type `L=12`.

Because direct CP-SAT sampling returned no generic supports, I implemented a local-swap sampler around the L15 support:

- [rankweight_mutation_geometry.py](../code/rankweight_mutation_geometry.py)
- output [rankweight_mutation_geometry.json](../results/tight_rank_geometry/rankweight_mutation_geometry.json)

It accepted 40 rank-weight-preserving swaps in 10,254 attempts and analyzed the seed plus 16 nearby supports.  Aggregate:

- 17 supports analyzed;
- only the seed and one mutated support passed the fixed-domain linear membership test;
- 16/17 had nontrivial domain restrictions and 16/17 had zero-domain terms;
- 16/17 had reported independent-transversal failures;
- the seed is exceptional because its tight constraints are all rank-3 contractions with full 9-dimensional B and C spaces.

Scientific reading: scalar rank-weight inequalities alone are weak and can be satisfied by many false supports.  Tight contractions become useful only when rank-1 or rank-2 matrix contractions are tight, because their column/row spaces restrict factors.  The old L15 support avoids that restriction surface; its obstruction remains in lower-L complete Wang rows, not in the 255 scalar inequalities.

## 5. Lift residual cross-check and correction of an over-strong peer statement

Peer research_record reported the rank distribution of \(\Delta=M_0+qr^T\).  I independently verified it in:

- [lift_residual_and_rank1_sum_test.py](../../occupation_and_completion/code/lift_residual_and_rank1_sum_test.py)
- output [lift_residual_rank1_sum_test.json](../../occupation_and_completion/results/lift_residual/lift_residual_rank1_sum_test.json)

For all ordered pairs \((q,r)\in(\mathbb F_2^9)^2\),

```json
{"rank 2": 28, "rank 3": 8100, "rank 4": 254016}
```

Thus \(M_0+qr^T\) never has rank 0 or 1 as a required lifted-subset sum \(\Delta\); at least two rank-one contributions are needed.

However, I also found a simple counterexample to the unconditional claim that a rank-one block sum forces every contributing nonzero left factor to share the final direction:
\[
(e_1+e_2)\otimes r + e_2\otimes r = e_1\otimes r.
\]
The two summands do not both have left factor \(e_1\).  Alignment of individual B or C factors is valid under tight/minimality conditions such as active count equals matrix rank, but not from `rank(sum) <= 1` alone.  The lift route remains promising, but its factor restrictions should be encoded through tight domain/rank-count consequences rather than imposed as unconditional per-term equalities.

## 6. Consequences for next research

The highest-value computational direction is not a low-ceiling flattening and not a search over scalar rank-weight supports alone.  The next useful construction/lower-bound interface should combine:

1. correct normalized nineteen-term E11 core equations;
2. complete Wang occupation rows or a carefully chosen proof-producing subset;
3. tight-contraction factor domains, especially supports with rank-1/rank-2 tight contractions;
4. residual rank-\(\le1\) lift equations only with valid algebraic consequences;
5. exact B/C rank-one completion or formal UNSAT certificates for fixed-A surfaces.

For the upper-bound side, a viable route is to search for A-supports that are not just Wang/rank-weight admissible but also have tight-domain linear membership and no immediate transversal obstruction, then run exact fixed-A rank-one completion.  The current old L15 near support is poor for this because tight domains are full and complete Wang still fails; mutated supports usually die by domains before complete Wang is considered.  This suggests support search should actively optimize for complete Wang admissibility and controlled non-full tight domains simultaneously, rather than one scalar condition at a time.

## 7. Complete Wang scan of tight-geometry samples

After writing the first synthesis I ran [complete_wang_scan_tight_samples.py](../code/complete_wang_scan_tight_samples.py), which scans the seed and 16 rank-weight-preserving mutated supports against all 417,199 E11 quotient Wang occupation rows using the old verified LUT. Output:

[complete_wang_scan_tight_samples.json](../results/tight_rank_geometry/complete_wang_scan_tight_samples.json)

The scalar rank distribution in the E11 coefficient space \(L=\{\Lambda_{11}=0\}\) is:

```json
{"rank 1": 33, "rank 2": 150, "rank 3": 72}
```

This corrects any earlier informal count of rank types in the 255 nonzero contractions.

Complete-Wang scan results for the 17 tested supports:

- none had zero complete-Wang violations;
- the old L15 seed remains by far closest, with exactly 12 violations, all `L=12`, maximum excess 1;
- the 16 one-walk mutated supports had 161 to 315 complete-Wang violations, often including higher `L` violations and maximum excess 2 or 3;
- the mutated support with nontrivial tight domains and linear pass (`swap_rankweight_sample_14`, affine domain dimension 72) still has 178 complete-Wang violations and four zero-domain terms, so it is not a good fixed-A completion target.

This reinforces the route judgement: rank-weight preserving motion usually moves away from complete Wang admissibility even while producing stronger local domain obstructions. A productive search should not first enumerate rank-weight supports and then hope for completion. It should integrate complete Wang rows (or a strong low-L subset) with tight-domain objectives from the start, aiming for supports that have zero complete-Wang violations and nontrivial but nonfatal factor domains.
