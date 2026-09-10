# residual-capacity Wang cover tests for distinct E11 branches

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Mathematical point

For the unresolved distinct projected-A E11 support search, the repaired semantics remain:

- every Wang row is an upper bound \(|S\cap R|\le c_R\);
- a saturated row can remove future points inside \(R\);
- unused capacity in one row is never a filling requirement.

There is nevertheless a sound global-size implication.  At a partial node with selected support \(P\), future domain \(F\), and remaining target size \(t=19-|P|\), a valid Wang upper row \(|S\cap R|\le c_R\) has residual capacity
\[
  u_R=c_R-|P\cap R|.
\]
Any extension \(Q\subseteq F\) must satisfy
\[
  |Q| \le u_R + |F\setminus R|.
\]
Therefore \(u_R+|F\setminus R|<t\) closes the branch.  The obligation comes from the global target size; this is not the invalid `small_remain < cap-count` rule from the retracted peer DFS.  Larger-capacity Wang rows can become useful when saturation and branch order have concentrated the future domain.

A two-row integer cover variant was also tested on saved frontiers: for two upper rows one can exactly maximize the number of future points subject to their two residual capacities by partitioning \(F\) into \(R\cap S\), \(R\setminus S\), \(S\setminus R\), and the outside.  This is a short rational/integer cover certificate in the same review as the weighted cover idea, but was only measured on partial frontier samples in this ARTIFACT.

## Implementation and soundness tests

New/reused scripts and binaries:

- [cover_bitset_dfs.cpp](../../quotient_cores/code/cover_bitset_dfs.cpp) -> `workspace/scripts/cover_bitset_dfs`: repaired cap<=5 Wang saturation runner with optional separate cover rows.  Cover rows are valid Wang upper rows used for over-cap rejection and residual-capacity one-row pruning; they are not saturated into the domain, so this isolates the new pruning mechanism.
- [cover_soundness_test.py](../../quotient_cores/code/cover_soundness_test.py): tiny brute-force review for ordinary upper rows, separate cover upper rows, and mixed lower cuts.  Output [cover_soundness_test.json](../../quotient_cores/results/domain_dfs_soundness/cover_soundness_test.json) records 103 small cases, 154 brute-force solutions and 154 C++ solutions, zero mismatches, and 45 cover prunes.
- [cover_bitset_dfs_stats.cpp](../../quotient_cores/code/cover_bitset_dfs_stats.cpp): diagnostic frontier sampler that records best one-row margins at a fixed split depth without claiming coverage when it times out.
- [cover_exhaust_prefix.cpp](../../quotient_cores/code/cover_exhaust_prefix.cpp): attempted coverage-preserving prefix splitter; current branch-1 depth-10 run timed out and emitted only a partial frontier.
- [pair_cover_frontier_analysis.py](../../exact_baselines/code/pair_cover_frontier_analysis.py): Python replay of saved prefixes to compare one-row and two-row cover strength.

The soundness review includes a fixed example where after forcing point 1, cover row \(R=\{1,2,3,4\}\), cap 2, target 4, and future universe \(\{2,3,4,5\}\) give residual \(u=1\), outside=1, need=3, hence the branch is correctly closed; the satisfiable counterpart with one more outside point is accepted.

## Row families prepared

All rows come from the canonical earlier research Wang LUT under the same E11 quotient encoding used in earlier analysis.

- `e11_wang_cap5_rebuilt.bin`: 338,840 rows, SHA256 `dd1aaf3795db56f4a33fce5ecd139052ec70527d709b77c16f76187879f9a59b`.
- `e11_wang_cap10_rebuilt.bin`: 416,587 rows, SHA256 `fa717a5365f2a4655fe343d96eba673fa8c3b8e66d26e339e9e244c056da771d`.
- `e11_wang_cap16_rebuilt.bin`: 417,198 non-ambient rows, SHA256 `7ddf644c557c647c42942510de082b0c52a6fd2eebc403d000809853bf3788b3`.
- `e11_wang_cap6_7_cover.bin`: 69,362 omitted cover rows (8,130 cap-6 and 61,232 cap-7), SHA256 `daef250c1b942c6a93a86350327c06b494855d3da4b88f4379938bce7d08e77e`.
- `e11_wang_cap6_8_cover.bin`: 70,227 rows, SHA256 `ca362fdb5a11be38905fa3f968309f3c4a62d5fa000705bad68fd642498c21ed`.
- `e11_wang_cap6_10_cover.bin`: 77,747 rows, SHA256 `159f82bae778181bb45a7e6c85ea72360ba44667a8472ffae36badfaadb3f080`.
- `e11_wang_cap67_first512_cover.bin`: the first 512 cap-7 cover rows, SHA256 `094dccc2dc0c0d17dbb9ffb2d2bd2ff7567bdcc8342256fb1fa512f6da6be9ec`.
- `e11_wang_cap5_plus_cover512.bin`: cap<=5 rows plus those 512 cap-7 rows treated as ordinary upper constraints, SHA256 `f4583c828a3c0c4638f0e7e15b21a1c94fb85f34cc090061357182f87e03bc46`.

`row_family_stats.json` records row-size and dimension distributions.  Notably cap-7 rows are numerous (61,232) but moderate sized on average (31.55 points), so they often become relevant once the future domain has shrunk to roughly 7--10 points.

## E11 branch runs and what they mean

All branch runs below are still support-level tests only.  Timeout and absence of a stored solution are not exclusions.  Closure means zero supports for the specific row family in that orbit branch, not an E11 tensor-rank theorem by itself.

### Ordinary larger-cap rows as full constraints

Using all cap<=10 rows directly as ordinary upper constraints was not uniformly helpful: branch 7 still closed in 3.11 s, but branch 4 timed out at 92.18 s even though cap<=5 alone had closed it in about 70 s.  This suggests that naively adding hundreds of thousands of rows can hurt more than help unless the rows are selected or implemented with stronger propagation.

Treating only the first 512 cap-7 rows as ordinary extra upper constraints is more promising.  Short 60 s runs on branches 0 and 1 still timed out but reached depth 15 and 13 respectively, with no support recorded.  A long branch-0 run is now in background task `s15_t50_tool1`, output path [merged_cover512_as_upper_branch0_1800s.json](../../quotient_cores/results/domain_dfs_soundness/merged_cover512_as_upper_branch0_1800s.json).

### One-row cover pruning with cap-6/7 rows

With cap<=5 as propagation rows and all cap-6/7 rows as separate cover rows checked at every depth:

- branch 7 closed with zero supports in 1.76 s (`cover_cap67_branch7_always_patch_60s.json`), 7,159 recursive calls and 1,089 cover prunes;
- branch 4 closed with zero supports in 74.07 s (`cover_cap67_branch4_always_patch_90s.json`), 302,915 recursive calls and 36,430 cover prunes.

These reproduce the already closed later-orbit branches under a sound stronger row family.  They are not new global coverage.

On branch 0, using cap-6/7 cover rows only from depth 12 timed out after 63.48 s (`cover_cap67_branch0_d12_patch_60s.json`), with max depth 13, 7,795 one-row cover prunes, 634 cover over-cap rejections, and no solution.  The stored certificate heads are typical depth-12 states with need 7 and cap-7 residual/outside combinations such as residual 3 plus outside 3, giving at most 6 future points.

### Combining one-row covers with the 1,440 K=15 mixed cuts

Using cap<=5, cap-6/7 cover rows from depth 12, and the 1,440 analysis gap-6 mixed cuts:

- `cover67_mixed1440_branch0_d12_180s.json`: timeout, 753,665 recursive calls, max depth 13, 104,259 mixed prunes, 22,970 cover prunes, no solution.
- `cover67_mixed1440_branch1_d12_180s.json`: timeout, 770,049 calls, max depth 14, 147,440 mixed prunes, 1,718 cover prunes, no solution.
- `cover67_mixed1440_branch2_d12_180s.json`: timeout, 786,433 calls, max depth 12, 175,233 mixed prunes, 220 cover prunes, no solution.
- `cover67_mixed1440_branch3_d12_180s.json`: timeout, 753,665 calls, max depth 13, 127,589 mixed prunes, 1,506 cover prunes, no solution.

The cover rows mainly act late in these settings, while mixed cuts often act earlier.  The combined row family has real pruning but does not close branches 0--3 in these short runs.  Long branch-0 and branch-1 versions are running as background tasks `s15_t29_tool1` and `s15_t30_tool1` with output paths `cover67_mixed1440_branch0_d12_1800s.json` and `cover67_mixed1440_branch1_d12_1800s.json`.

Using only the first 512 cap-7 cover rows makes checking much cheaper and often faster per call.  In 180 s with mixed cuts and depth-12 cover checks, branches 0--3 still timed out, but branch 0 reached 1,179,649 recursive calls with 171,363 mixed prunes and 24,686 cover prunes; branch 1 reached 1,228,801 calls with 244,011 mixed prunes and 2,328 cover prunes; branch 2 reached 1,196,033 calls with 272,401 mixed prunes and 352 cover prunes; branch 3 reached 1,163,265 calls with 190,088 mixed prunes and 1,718 cover prunes.  With cover checks starting at depth 10, branch 0 in 60 s had 96,762 one-row cover prunes and branch 1 had 8,111; adding mixed cuts to the same first-512 cover rows changed the pruning mix but still timed out.

### Frontier and two-row cover measurements

The frontier diagnostic without early cover pruning is incomplete but informative.  At split depth 12, while traversing the first explored part before timeout, cap-6/10 cover rows had negative best one-row margin in most recorded depth-12 nodes:

- branch 0: 117,111 of 117,407 recorded frontier nodes had negative best one-row margin; best cap was usually 7, sometimes 10.
- branch 1: all 1,682 recorded frontier nodes had negative best one-row margin.
- branch 2: all 788 recorded frontier nodes had negative best one-row margin.
- branch 3: 28,624 of 28,631 recorded frontier nodes had negative best one-row margin.

These numbers are not coverage because the diagnostic runs timed out, but they explain why the residual-capacity row is a genuine missing pruning mechanism in late branch space.

The attempted branch-1 prefix splitter to depth 10 timed out at 240 s after emitting 427,370 partial frontier nodes (`branch1_prefix_d10_frontier.jsonl`, summary `branch1_prefix_d10_summary.json`), so it is not a proof.  On the first 500 emitted prefixes, `pair_cover_frontier_analysis.py` found 476 one-row closures and 11 additional closures by two-row exact capacity covers using only the first 64 cover rows.  This supports the idea that small weighted/integer row combinations can add strength beyond single rows, but it remains a measurement on a partial frontier.

## Current interpretation

The new bound is mathematically sound and useful, but its current implementation has not solved the remaining distinct branches.  It changes the computational picture in three ways:

1. Larger Wang rows should not be selected solely by static cap<=5.  Cap-7 rows especially become active when the future domain has shrunk, and short certificate heads show exact residual-capacity contradictions at depth 10--13.
2. Adding many rows as ordinary saturation constraints is not automatically better; all cap<=10 slowed branch 4, while a small selected cap-7 prefix looked cheaper and may be more useful.
3. The remaining problem appears to need coverage-preserving branch splitting and replayable small certificates, not just longer monolithic pruning counts.  A completed split frontier would allow independent replay of each subbranch by either a one-row certificate, a small two-row/weighted cover, mixed cut, or a smaller DFS closure.

No rank-19 E11 core, rank-22 full decomposition, or full rank>=21 proof was obtained in this ARTIFACT.

## Background long-run results received before analysis close

Two 1,800-second monolithic branch runs using cap<=5 propagation, all cap-6/7 cover rows from depth 12, and the 1,440 K=15 mixed cuts completed as processes but timed out internally, so they are not exclusions:

- `cover67_mixed1440_branch0_d12_1800s.json`: branch 0, rep 1, `timeout=true`, `complete=false`, no stored support, max depth 18, 7,192,577 recursive calls, 7561815 candidate tests, 369,238 cover over-cap rejections, 5,092,230 global-shortage prunes, 722,502 mixed prunes, 518,822 cover prunes, and 14 nodes at depth 18.
- `cover67_mixed1440_branch1_d12_1800s.json`: branch 1, rep 4, `timeout=true`, `complete=false`, no stored support, max depth 15, 7,602,177 recursive calls, 7627558 candidate tests, 25,381 cover over-cap rejections, 5,057,382 global-shortage prunes, 1,493,789 mixed prunes, 66,376 cover prunes, and 26 nodes at depth 15.

These long runs sharpen the search picture without proving anything: branch 0 in particular has very deep surviving prefixes under this row family, so monolithic DFS with late one-row cover scans is unlikely to finish cheaply.  The result favors coverage-preserving splitting, selected larger rows used as ordinary constraints or early cover rows, and small replayable capacity-cover certificates over simply extending the same long run.
