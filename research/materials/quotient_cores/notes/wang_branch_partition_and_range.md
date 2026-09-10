# fixed-E11 Wang branch assembly and rank-1-count range probes

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

The active route is the finite-field Wang occupation necessary-condition problem for a hypothetical length-20 A-support of the 3x3 matrix multiplication tensor over \(\mathbb F_2\).  The ARTIFACT did two things that are needed before this computation can become a reliable theorem component:

1. turn the fixed-E11 branch structure into a checkable finite partition, not a loose collection of proof files;
2. test the proposed range-CNF idea for the remaining mixed cases \(k=1,\ldots,17\), rather than assuming that exact-18 pair enumeration scales downward.

No result here is a rank-22 algorithm or a characteristic-zero lower bound.  The work is still inside the \(\mathbb F_2\) Wang necessary-condition framework.

## Branch partition certificate

New script:

- [certify_wang_branch_partition.py](../code/certify_wang_branch_partition.py)

Output:

- [fixed_e11_partition_certificate.json](../../finite_certification/results/wang_branch_partition/fixed_e11_partition_certificate.json)

The script recomputes the group action facts used by the fixed-E11 proof tree:

- full A-side action count: 56,448;
- Stab(E11) action count: 1,152;
- Stab(E11) partitions the 510 non-E11 projective A-points into eight single-point orbits with representatives
  \[
  2,10,16,17,20,84,160,161;
  \]
- all higher-rank unordered pairs form 185 Stab(E11) pair orbits and the recomputed orbit sizes sum to \(\binom{462}{2}=106,491\);
- after analysis single-high exclusions in the exact-18 case, the remaining high points are precisely the 276 rank-2 points in single orbits 17,20,160; their unordered pairs form 69 pair orbits and the recomputed sizes sum to \(\binom{276}{2}=37,950\).

The output booleans are all true:

```json
{
  "single_orbits_partition_non_E11_points": true,
  "all_high_pair_orbits_partition_pairs": true,
  "remaining_exact18_pair_orbits_partition_pairs": true
}
```

This certificate only checks finite partition completeness.  It does not prove any occupation branch unsatisfiable.

## Exact-18 pair status after collecting the background batch

The analysis managed task `s12_t48_tool1` finished.  It processed pair-orbit indices 5 through 68 in the exact-18 high-pair list.  Together with the analysis pilot on indices 0 through 4, all 69 exact-18 remaining high-pair CP-SAT representatives are `INFEASIBLE` in the full residual rank-1 skeleton model.  The summary files are:

- [pilot5_summary.json](../../occupation_and_completion/results/rank1_highpair_batch/pilot5_summary.json)
- [all69_remaining_from5_summary.json](../../occupation_and_completion/results/rank1_highpair_batch/all69_remaining_from5_summary.json)

This is strong execution evidence that the exact-18 branch should close, but it is not yet a mathematical proof component because most leaves still lack verified DRAT replay.

Verified pair leaves now include indices 0--6:

- 0 `(17,19)`: `workspace/data/rank1_fixed_high_filtered_cnf/pair_000_17_19_exact18_max7/`
- 1 `(17,20)`: `workspace/data/rank1_fixed_high_filtered_cnf/pair_001_17_20_exact18_max7/`
- 2 `(17,26)`: the max-7 filtered row family was SAT and must not be counted; max-9 closes it, at `workspace/data/rank1_fixed_high_filtered_cnf/pair_002_17_26_exact18_max9/`, with CNF SHA256 `75661e1acba594e9e9578f5b95fdabee9cccc7473a9c6231d42586381c604070`, DRAT SHA256 `55bf0545fb2988d663db9501c5ce42e2c466883182c7858ad5a5909c9009b425`, trim-log SHA256 `a9c465f98eaaa19897a08f39630bbfd73ea71cb5b77844b4c1ad21732667afc7`;
- 3 `(17,28)`: `workspace/data/rank1_fixed_high_filtered_cnf/pair_003_17_28_exact18_max7/`, CNF `009ed876edce0fab6e730123d73166af7b10f5da3aa8da5fdb0745c4e895640d`, DRAT `d29832e741e3dc72a070e5eed5fd93301b25cde2770e63e365d18294b08e4b3c`, trim `d2c16eaa3b54988a3b0520d4edd80244ff2f9e235008f35ba8c3af2dd2d56f3b`;
- 4 `(17,33)`: `workspace/data/rank1_fixed_high_filtered_cnf/pair_004_17_33_exact18_max7/`, CNF `33fa12ff3df216f3f8bb12f41c3fb90deb04a081bac783e8f50c638ff277ba93`, DRAT `e0f370e3a570312b9975165cdbc3abff1d956087dd1c8132df93c7a28f94f0a8`, trim `2b84a30d28f55f5fe290d3ef3716c568d919d679e0d05453ea3f6c3a372081a0`;
- 5 `(17,34)`: `workspace/data/rank1_pair_filtered_proof_batch/pilot_005_006/pair_005_17_34_exact18_max7/`, CNF `6356f3a015f3e18d9d09e08ccd1445b8d1a24af8c8e5b80bf8f09013eb445027`, DRAT `c8a6b89a60a77474a9f78968b63ca2d78a5b5a46286a21e708f4697fcffb28c0`, trim `0a778e6bf519eff466f3e6ec940ac2735c40080d842c339f10ccb73c21570d44`;
- 6 `(17,35)`: `workspace/data/rank1_pair_filtered_proof_batch/pilot_005_006/pair_006_17_35_exact18_max7/`, CNF `4ee237c30c543f14bd84ab4ed4a397a3472a94debd3c0f572ee025d90bc0047e`, DRAT `4e97c615cd935f004ccc2dd20083c7e8d0fd63a8c4becaaa498c53144d111be2`, trim `3964498b2c3678adfa2c245286c596401d5c09a3f9ea407b47f2a1f5729dbd48`.

I also launched managed task `s13_t36_tool1` to continue verified DRAT replay for pair-orbit indices 7--68, trying max-intersection filters 7 and 9.  This task is still running and must be collected later before claiming any additional verified leaves.

A status snapshot after launching the batch is saved at:

- [wang_branch_status_summary_v3.json](../results/wang_branch_partition/wang_branch_status_summary_v3.json)

At the moment that snapshot was made it saw 12 verified pair indices because the new background task had already written some early leaves.  Since the managed task is not terminal yet, only the files already visible and verified should be used; do not infer the rest.

## Range CP-SAT for k=1..17

New scripts:

- [wang_fixed_e11_range_cpsat.py](../code/wang_fixed_e11_range_cpsat.py): CP-SAT range model combining fixed E11, optional fixed second representative, total support size 20, rank-1 count interval/exact count, selected full Wang rows, high-dimensional rows through the fixed prefix, and the full compressed rank-1 projection.
- [wang_fixed_e11_range_ablation.py](../code/wang_fixed_e11_range_ablation.py): runs several such CP-SAT row-family variants after loading the LUT once.
- [wang_fixed_e11_range_cnf.py](../code/wang_fixed_e11_range_cnf.py): DIMACS/DRAT counterpart for a chosen row family; it was tested on rep10 but the produced CNF was large.

### All fixed E11 without second representative

Command result:

- [e11_k01_17_dim123_throughE11_rank1proj.json](../results/wang_fixed_e11_range_cpsat/e11_k01_17_dim123_throughE11_rank1proj.json)

Model: fixed E11, \(1\le k\le17\), full dimensions 1--3, rows in dimensions 4--8 through E11, full rank-1 projection.  Result after 600 s:

- `UNKNOWN`; no support was produced.

### Remaining second-point representatives

The three open analysis fixed-E11 second-orbit branches were probed with the same range model but with the representative fixed and earlier second-orbit points omitted.

Rep 2:

- initial file: [e11_rep002_k01_17_dim123_throughfixed_rank1proj.json](../results/wang_fixed_e11_range_cpsat/rep002_k01_17/e11_rep002_k01_17_dim123_throughfixed_rank1proj.json)
- CP-SAT `OPTIMAL`, support rank histogram `{1:17,2:3}`.
- Full LUT scan: [e11_rep002_k01_17_full_capacity_check.json](../../occupation_and_completion/results/wang_fixed_e11_range_cpsat/rep002_k01_17/e11_rep002_k01_17_full_capacity_check.json), 246 violations, max excess 2, violations by dimension `{4:12,5:111,6:99,7:18,8:6}`.
- With the first 200 violation keys seeded back: [e11_rep002_k01_17_seed1.json](../results/wang_fixed_e11_range_cpsat/rep002_k01_17/e11_rep002_k01_17_seed1.json), result `UNKNOWN` after 600 s.  This is not closure.

Rep 10:

- file: [e11_rep010_k01_17_dim123_throughfixed_rank1proj.json](../results/wang_fixed_e11_range_cpsat/rep010_k01_17/e11_rep010_k01_17_dim123_throughfixed_rank1proj.json)
- CP-SAT `INFEASIBLE` in about 320 s for the row family dim 1--3 + dim 4--8 through fixed prefix + rank-1 projection.
- Exact count probes: exact k=17 and exact k=16 are `INFEASIBLE`; exact k=15 is `UNKNOWN` after 180 s (`workspace/data/wang_fixed_e11_range_cpsat/rep010_exact_k/`).
- Row-family ablation ([rep010_k01_17_summary.json](../results/wang_fixed_e11_range_ablation/rep010_k01_17_summary.json)) showed weaker families can be SAT and the full family needs longer than 120 s in that run; through dims 4--8 was the successful 600 s CP-SAT run.
- DIMACS replay `workspace/data/wang_fixed_e11_range_cnf/rep010_k01_17/e11_rep010_k01_17_dim123_throughfixed_rank1proj.cnf` has 6,641,874 variables and 40,610,205 clauses.  CaDiCaL did not finish within 900 s and no DRAT proof exists.  Thus rep10 k=1..17 is promising for closure but not theorem-ready.

Rep 16:

- initial file: [e11_rep016_k01_17_dim123_throughfixed_rank1proj.json](../results/wang_fixed_e11_range_cpsat/rep016_k01_17/e11_rep016_k01_17_dim123_throughfixed_rank1proj.json)
- CP-SAT `OPTIMAL`, support rank histogram `{1:14,2:6}`.
- Full LUT scan: [e11_rep016_k01_17_full_capacity_check.json](../../occupation_and_completion/results/wang_fixed_e11_range_cpsat/rep016_k01_17/e11_rep016_k01_17_full_capacity_check.json), 555 violations, max excess 2, violations by dimension `{4:37,5:116,6:258,7:134,8:10}`.
- With the first 200 violation keys seeded back: [e11_rep016_k01_17_seed1.json](../results/wang_fixed_e11_range_cpsat/rep016_k01_17/e11_rep016_k01_17_seed1.json), result `UNKNOWN` after 600 s.  This is not closure.

## Interpretation

The exact-18 high-pair surface is likely finite and closable: all 69 representatives are CP-SAT infeasible, and the first seven pair-orbit leaves now have verified filtered DRAT replays (with pair `(17,26)` needing max-size 9 rather than max-size 7).  The immediate execution value is to finish the DRAT leaf conversion, not to enumerate triples for k=17.

For \(k=1,\ldots,17\), the one-shot range formula is scientifically useful but did not close the whole fixed-E11 branch.  It did close the rep10 range in CP-SAT, suggesting that a better proof encoding or a stronger small row-family search could make rep10 theorem-ready.  Rep2 and rep16 still produce full-LUT-violating candidates or timeouts after seeding, so the mid-range problem remains real.  The range formulation is the correct replacement for naive high-point triple/quadruple orbit enumeration, but it needs a better compression/proof strategy for rep2 and rep16.

## related analysis analysis correction

related analysis first reported a rank-22 Jacobian and pairing-defect tangent picture, then corrected the interpretation in analysis.  The durable piece from the corrected analysis is not a proof of rank-23 optimality but a sharper necessary singular-stratum statement: any full-span rank-22 preimage of \(T_{333}\) in a full-UV-rank shortened chart must lie in a forced singular stratum with full Jacobian rank at most 526 and shortened rank at most 328 on the stabilizer-transverse branch; non-transverse alignment strata remain separate.  This supports the judgment that a characteristic-zero rank-22 algorithm, if it exists, is structurally isolated from known rank-23 schemes, but it does not replace the finite-field Wang branch.

## Next work

1. Collect `s13_t36_tool1` when delivered and update [wang_branch_status_summary_v3.json](../results/wang_branch_partition/wang_branch_status_summary_v3.json) or a successor summary from actual terminal results.
2. Finish verified DRAT leaves for exact-18 pair-orbit indices 7--68; use max-size 7 first, max-size 9 when needed, and never count a SAT filtered leaf as exclusion.
3. For rep10 \(k=1..17\), search for a smaller row family or use exact-k/range splitting before attempting another enormous DRAT replay.  The 6.6M-variable CNF did not solve in 900 s.
4. For rep2 and rep16 \(k=1..17\), the current row family only produces candidates violating full LUT or UNKNOWN after seeding.  Develop a better range-level lazy/row-selection mechanism rather than descending to high-point tuple enumeration.
5. Ask review to inspect and improve the range CNF/DRAT representation and branch assembly, because this ARTIFACT exposed that the proof object size, not just CP-SAT feasibility, is now the bottleneck.
