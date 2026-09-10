# quotient tightening, branch CEGAR, and branch-state propagation notes

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

Active goal remains the exact rank problem for \(T_{\langle3,3,3\rangle}\) over \(\mathbb F_2\): either a verified rank-\(\le 22\) decomposition or a complete rank-\(\ge 21\) proof. Nothing in this note proves the final result.

## Static bottom-up tightening interpretation

The review note clarified a mathematical limit of the static descendant cascade. If a local feasibility test for a parent \(U\) already imposes all strict-child inequalities \(|T\cap V|\le c(V)\) for every strict \(V\subset U\), then any later bound on a child \(V\) derived only from strict descendants of \(V\) was already implied for the original test. Thus a correctly certified local witness for a parent cannot be destroyed by replacing children with descendant-only compiled bounds. analysis's dim-6 cap-5 witnesses and any correctly tested dim-5 cap-4 witnesses should be preserved; repeated static recensus without changing scope is not meaningful mathematics.

analysis therefore did **not** spend the ARTIFACT re-running the dim-5 cap-4 cascade after the dim-4 deductions. The useful static rows from analysis were preserved and merged into cap<=5 branch-search tables:

- `workspace/data/quotient_lift/tightening/rank2_cap5_plus_dim5cap3_dim4cap4tight_rows.bin`, SHA256 `a2eae9afbcd76dd102e258fcde29c058c24b951d1fcfb4d2004eafe27002aa50`, 360,541 masks; rank2 caps include corrected dim-5 cap-3 -> cap-2 and dim-4 cap-4 -> cap-3 replacements.
- `workspace/data/quotient_lift/tightening/rank3_cap5_plus_dim5cap3_dim4cap4tight_rows.bin`, SHA256 `1a86912577044bf779ae1bc0f385da721f7a5c5a53bd9c8e6f3147dc79e57db1`, 358,618 masks; rank3 analog.

The complete all-row corrected tables from analysis remain:

- `workspace/data/quotient_lift/tightening/rank2_all_plus_dim5cap3_dim4cap4tight_rows.bin`, SHA256 `6471990605ce99b2eb8073f8d689268011b5aa84cc7d6a97a57323819b611476`.
- `workspace/data/quotient_lift/tightening/rank3_all_plus_dim5cap3_dim4cap4tight_rows.bin`, SHA256 `c470232dfa7e5a39b0e6b5ade5cd9cc276e2e8ce6c5b2f7d4d770d7827cedaff`.

## Pending analysis exact runs

All three analysis long exact DFS tasks timed out and are not branch exclusions:

- rank2 branch 2 corrected-tight minedpair DFS: timeout, complete=false, recursive_calls=1,392,641, max_depth=12, pair_prunes=1,240,633, pair_forces=823,805.
- rank3 branch 0 corrected-tight minedpair DFS: timeout, complete=false, recursive_calls=1,212,417, max_depth=13, pair_prunes=1,538,192, pair_forces=691,743.
- rank2 branch 1 corrected-tight pair32 DFS: timeout, complete=false, recursive_calls=2,523,137, max_depth=12, pair_prunes=1,261,702, pair_forces=1,014,515.

## CEGAR probes on corrected dim4+dim5 all-row tables

Script: [branch_cegar_custom.py](../../occupation_and_completion/code/branch_cegar_custom.py).

Using the complete corrected all-row tables and initial active cap<=3 rows:

- rank2 branch 1 (`tightening/dim5dim4tight_cap3_rank2_branch1_cegar.json`): round 0 support `[2,11,16,19,22,32,33,40,41,96,99,105,128,165,184,189,192,215,231]`, 228 violations with cap histogram {4:113,5:34,7:72,10:8,13:1}; round 1 UNKNOWN. No closure.
- rank2 branch 2 (`tightening/rank2_b2_cegar/dim5dim4tight_cap3_rank2_branch2_cegar.json`): round 0 support `[4,5,6,7,11,16,17,24,25,32,42,73,104,128,148,189,215,224,254]`, 293 violations with cap histogram {4:144,5:62,7:77,10:10}; round 1 UNKNOWN. No closure.
- rank3 branch 0 (`tightening/rank3_b0_cegar/dim5dim4tight_cap3_rank3_branch0_cegar.json`): three supports were found with 213, 95, and 110 corrected-table violations respectively; round 3 UNKNOWN. No closure.

These probes show that dim4+dim5 static tightening changes the active row population but does not by itself settle the remaining hard quotient branches.

Focused pair rows exported from these probes:

- rank2 branch 1 top160: `tightening/rank2_branch1_tight_pair_rows_top160.bin`, SHA256 `0907b0150ed0161be9192ef1d9bd8a305283bcd956e6c74755a7454bd9035ace`.
- rank2 branch 2 top160: `tightening/rank2_b2_cegar/rank2_branch2_tight_pair_rows_top160.bin`, SHA256 `5ca33a75574ae2d58bb1fdf3829f16c6e90e685550eb03b12e8d8c1aba739aac`.
- rank3 branch 0 top160: `tightening/rank3_b0_cegar/rank3_branch0_tight_pair_rows_top160.bin`, SHA256 `cef3ebfd939cba9c3f73012910370965d02821e02b292dfc1b9a180a63db9ec5`.

Three long pair-propagation DFS tasks were launched and remain unresolved at note time:

- `s27_t12_tool1`: rank2 branch 2 with analysis cap<=5 tightened table plus rank2 branch2 top160 pair rows, timeout 1500s.
- `s27_t12_tool2`: rank3 branch 0 analog, timeout 1500s.
- `s27_t12_tool3`: rank2 branch 1 analog, timeout 1500s.

## Branch-state residual local tightening

Script: [residual_local_tighten.py](../code/residual_local_tighten.py).

Mathematical form: for a branch with forced points \(P\) and forbidden points, a row \(W\) crossing a parent \(U\) gives residual capacity \(c(W)-|P\cap W|\) on future choices inside \(F\cap U\). This is branch-conditioned information, unlike static child-only tightening. The script computes an exact maximum for selected candidate parent rows using all crossing rows from the supplied corrected table.

A bug was found and repaired in the local enumerator: it originally sorted candidates by degree while using the chosen local index as a cutoff, which could miss combinations. After repair it enumerates in increasing local-index order. Replayed top-80 probes gave no tightened rows:

- rank2 branch 2 top80: `residual_fixed/rank2_b2/rank2_b2_residual_top80_fixed_branch_residual_tightening.json`, tightened_count=0.
- rank2 branch 1 top80: `residual_fixed/rank2_b1/rank2_b1_residual_top80_fixed_branch_residual_tightening.json`, tightened_count=0.
- rank3 branch 0 top80: `residual_fixed/rank3_b0/rank3_b0_residual_top80_fixed_branch_residual_tightening.json`, tightened_count=0.

Interpretation: at the root branch state, the mined violated rows still have enough local witnesses under all crossing residual row bounds. This negative result does not rule out residual-cover pruning deeper in the search, where selected points and future domain are much more constrained.

## Residual cover and combined pair-cover DFS

Existing residual cover engine: [cover_bitset_dfs.cpp](../code/cover_bitset_dfs.cpp). It implements the sound one-row extension test \(u+|F\setminus R|<\text{need}\), where \(u=c(R)-|P\cap R|\). It is slow when all 417k cover rows are scanned, but it revealed substantial branch-state pruning:

- rank2 branch 1 with all complete corrected rows as cover rows and cover checks from depth 8: `tightening/rank2_b1_cover_pilot/rank2_b1_cover_pilot_240s.json`; timeout, recursive_calls=540,673, cover_prunes=45,286, cover_row_tests=11,011,545,313, max_depth=11. This is pruning evidence, not closure.
- Five rows from the cover certificate head were exported to `tightening/rank2_b1_cover_pilot/rank2_b1_cover_cert_head5_rows.bin`, SHA256 `2dac7157c0c6ccd3fc634ce7962f93be4a7ae1afcf0b7b019893aec49ac2f497`. A 120s replay using only those five rows still produced cover_prunes=6,061, showing that compact state-specific cover rows can have real effect but do not alone close the branch.

The mined top160 rows were also used as cover rows:

- rank2 branch 1 cover-top160 120s: cover_prunes=32,309.
- rank2 branch 2 cover-top160 120s: cover_prunes=53,556.
- rank3 branch 0 cover-top160 120s: cover_prunes=52,324.

New combined runner: [pair_cover_dfs.cpp](../code/pair_cover_dfs.cpp), compiled to `workspace/scripts/pair_cover_dfs`, SHA256 `f3e5e15c1505b9a9cc21468b17481f4195bc6596e8f871cb11fa021b6e735edd`. It combines the analysis repaired signed-pair propagation with analysis residual-cover pruning. Soundness review [pair_cover_soundness_test-61666f4852.py](../code/pair_cover_soundness_test-61666f4852.py) passed 150 random small systems plus structured cases; result [pair_cover_soundness_test-379d3a6ec0.json](../results/domain_dfs_soundness/pair_cover_soundness_test-379d3a6ec0.json), SHA256 `379d3a6ec0c9613e4e81e9863e961d52aebaa0023e052f3519f5f4502e6aad0c`, status ok with total_brute=114 and total_cpp=114.

Short combined pair-cover pilots with cover checks from depth 8 all timed out but show interaction:

- rank2 branch 1: `tightening/rank2_b1_paircover/rank2_b1_paircover_top160_180s.json`; recursive_calls=196,609, pair_prunes=279,315, cover_prunes=15,240, max_depth=12.
- rank2 branch 2: `tightening/rank2_b2_paircover/rank2_b2_paircover_top160_180s.json`; recursive_calls=212,993, pair_prunes=221,555, cover_prunes=31,284, max_depth=12.
- rank3 branch 0: `tightening/rank3_b0_paircover/rank3_b0_paircover_top160_180s.json`; recursive_calls=196,609, pair_prunes=293,885, cover_prunes=26,603, max_depth=13.

The combined runner is not yet proof-producing for any branch. Its value is that it joins two sound mechanisms that prune different parts of the tree. The next work should compare longer pair-only vs pair-cover runs and improve cover-row selection/adaptive cover indexing before treating it as a closure route.
