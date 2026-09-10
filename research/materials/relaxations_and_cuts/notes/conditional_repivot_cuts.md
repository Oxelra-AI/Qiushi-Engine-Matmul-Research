# conditional re-pivoted lift-obstruction cuts

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Mathematical object

The two certified pivot-17 lift obstructions from earlier analysis give 96 valid quotient support cuts of the form
\[
|S\cap C|\le 11
\]
for a length-19 quotient support relative to a selected rank-2 pivot normalized to \(q=17\).  Each cut is backed by an all-4096-assignment lift certificate transported under the actual pivot-17 tensor stabilizer with the affine lift-bit offset.

The review pointed out a stronger way to use these certificates in a full length-20 A-support \(X\), not only relative to the distinguished fixed pivot.  If a selected full A-direction \(a\in X\) has rank 2, choose an actual tensor automorphism \(g\in GL_3(\mathbb F_2)\times GL_3(\mathbb F_2)\) with \(g(a)=17\).  For a certified quotient cut \(C\), define
\[
B(a,C)=\{b\ne0,a: \pi_{17}(g(b))\in C\}.
\]
For a rank-20 support, the one-term-per-quotient-fiber property relative to the selected high-rank pivot \(a\) follows from the two-dimensional full Wang rows: with \(a\) selected, the two lifts in a nonzero quotient fiber cannot both be selected.  Thus the certified pivot-17 obstruction implies
\[
|X\cap B(a,C)|\le 11 \quad\text{whenever } a\in X.
\]
With Boolean full-direction variables \(z_b\) and total size 20, this is encoded as
\[
\sum_{b\in B(a,C)} z_b + 9z_a \le 20.
\]
If \(a\) is absent the inequality is tautological; if \(a\) is present it is exactly \(|X\cap B(a,C)|\le11\).  This is not a new single Wang row.  It is a compiled multi-row deduction from the replayed lift certificates plus the one-fiber property.

The normalizer choice is harmless provided the full stabilizer orbits of the base cuts are used: two choices of \(g\) differ by a pivot-17 stabilizer element, and the 96 cuts already include the stabilizer images.

## Artifacts

- Generator/evaluator: [conditional_repivot_cuts.py](../code/conditional_repivot_cuts.py).
- Compact export: `workspace/data/quotient_lift/conditional_cuts/conditional_rank2_cut_masks_from_two_orbits.json`, SHA256 `10283bb66cf37e79f0d7625ac90313599d684635b05869a568aaf9549ea78ccf`.
- Candidate evaluation: [conditional_repivot_cut_candidate_eval.json](../results/quotient_lift/conditional_cuts/conditional_repivot_cut_candidate_eval.json).
- Global full-A Boolean CEGAR with conditional cuts: [fullA_global_cegar.py](../../occupation_and_completion/code/fullA_global_cegar.py).
- Conditional non-redundancy witness finder: [find_conditional_violation_witness.py](../../quotient_cores/code/find_conditional_violation_witness.py).

The compact export contains 28,224 conditional cuts: 294 rank-2 full directions times 96 certified quotient cuts.  For each cut, \(|B(a,C)|=24\), as expected because each of the 12 quotient points has two full lifts.

## Tests on saved full-A candidates

I evaluated all analysis repaired pivot-fixed CEGAR candidates for the remaining hard cases.

- `rank2_branch0_n20_d2cap2.json`: four saved candidates; no conditional violations.  Max active left side values were 13, 14, 16, 15.  The full Wang violation counts were 12917, 8295, 3005, 4021.
- `rank2_branch2_n20_d2cap2.json`: three saved candidates; no conditional violations.  Max active left side values were 13, 13, 15.  Full Wang violation counts were 14401, 10768, 5397.
- `rank3_branch0_n20_d2cap2.json`: four saved candidates; no conditional violations.  Max active left side values were 11, 14, 17, 17.  Full Wang violation counts were 17391, 10921, 2520, 2950.

Thus the conditional cuts are not immediately rejecting the saved low-dimensional CEGAR candidates; those candidates are still excluded by ordinary full-Wang rows, often in dimensions 3--8.  This argues against treating the re-pivoted cuts as an instant branch closure.

## Full-A Boolean CEGAR pilots

I built a full-direction Boolean model with 511 variables, total size 20, split-flattening rank-sum constraint \(\sum\operatorname{rank}(a_i)\ge27\), optional fixed-pivot quotient branch constraints, initial full Wang rows of dimension <=2 and cap<=2, complete-LUT replay of every returned support, and the 28,224 conditional cuts when enabled.

Pilot outputs:

- `rank2_branch0_global_bool_cond_d2.json`: after three rounds, still OPTIMAL candidates; full-LUT violations 12573, 11191, 3299; conditional max lhs 13, 16, 16.
- `rank2_branch0_global_bool_nocond_d2.json`: after three rounds without conditionals, still OPTIMAL candidates; full-LUT violations 6181, 8563, 6219.  Re-evaluating those candidates against the conditional family found zero violations, with max lhs 13, 14, 16.
- `rank2_branch2_global_bool_cond_d2.json`: after three rounds, still OPTIMAL candidates; full-LUT violations 14538, 11179, 7209; conditional max lhs 12, 13, 14.
- `rank3_branch0_global_bool_cond_d2.json`: after three rounds, still OPTIMAL candidates; full-LUT violations 15851, 10280, 4476; conditional max lhs 12, 15, 16.

These runs show that the conditional cuts are mathematically valid and cheap to encode, but at this row level they do not dominate the ordinary full-Wang row CEGAR.

## Non-redundancy relative to the starting row system

To test whether the conditional cuts add any information at all beyond the dimension<=2 full-Wang start, I asked CP-SAT to find supports satisfying the low-dimensional rows, branch constraints, rank-sum, and deliberately violating at least one conditional cut.

It found such witnesses quickly:

- Rank-2 branch 0: `rank2_branch0_cond_violation_witness_d2.json`, support `[1,2,10,17,73,119,139,152,164,261,266,270,298,324,330,335,354,394,396,442]`, one conditional violation with lhs 21, and 8180 complete full-Wang violations.
- Rank-2 branch 2: `rank2_branch2_cond_violation_witness_d2.json`, support `[5,12,17,21,30,51,72,87,94,140,142,158,221,284,286,314,318,332,347,510]`, one conditional violation with lhs 21, and 9228 complete full-Wang violations.
- Rank-3 branch 0 with an additional selected rank-2 factor: `rank3_branch0_cond_violation_witness_d2.json`, support `[157,272,273,365,405,409,410,412,413,421,423,431,432,437,438,445,448,466,477,503]`, one conditional violation with lhs 21, and 6335 complete full-Wang violations.

So the conditional family is a genuine extra propagation family relative to the minimal low-dimensional Boolean start, but it is not yet a decisive replacement for full-Wang row generation.

## Pending and related outcomes

The analysis mined-pair DFS pilots for rank-2 branch 2 and rank-3 branch 0 both timed out after about 900 seconds with no stored supports, so they are process evidence only.  The branch-1 mined-row exact DFS replay also timed out after 900 seconds, despite no stored supports; branch 1 therefore still lacks an independent exact proof object beyond CP-SAT infeasibility.

The branch-5 exact DFS closure remains the best independent branch replay: [rank2_branch5_cap3_pair32_dfs_900s.json](../../occupation_and_completion/results/quotient_lift/rank2/rank2_branch5_cap3_pair32_dfs_900s.json) closed completely with zero supports.  Attempts to start a CaDiCaL/DRAT proof calibration initially failed because the proof output path was not writable under the narrow file mount.  A directory-write retry was launched as background task `s25_t20_tool1`; use its terminal result before relying on the SAT route.

## Interpretation

The re-pivoted conditionals strengthen the representation by connecting different rank-2 views of the same hypothetical full decomposition, and they are justified by certified lift obstructions rather than by unsupported new Wang rows.  Empirically, however, current hard-branch candidates generated after several ordinary full-Wang CEGAR rounds avoid these two obstruction orbits with a margin of at least 3 in lhs.  This suggests that the known two obstruction orbits do not yet describe the dominant obstruction geometry of the remaining branches.  The most valuable next use is therefore selective: keep the conditional cuts in full-A models because they are cheap and valid, but continue mining and minimizing new lift obstructions from live or near-live supports, especially supports not already shaped by the two O-containing pivot-17 obstructions.
