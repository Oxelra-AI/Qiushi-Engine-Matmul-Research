# execution notes: code LP, capacity branches, and core near-miss filtering

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

The corrected Wang occupation system for a hypothetical rank-20 decomposition over \(\mathbb F_2\) can be read as a projective binary \([20,9]\) code: the 20 distinct A-factors are columns, and each 3x3 matrix functional \(M\) gives a codeword of weight \(\#\{t:\langle M,a_t\rangle=1\}\). The dim-8 Wang rows say that a rank-\(r\) functional has weight at least \(3r\). analysis tested whether cheap MacWilliams/Delsarte-type relaxations or proof-producing branch CNFs can settle the T-level \(s=20\) capacity problem.

## Code-theoretic LP/MILP relaxations

Script: [wang_code_lp.py](../code/wang_code_lp.py).

Runs and outputs:

- [simple_lp.json](../results/wang_code_lp/simple_lp.json): split weight enumerator + nonnegative MacWilliams dual constraints is feasible.
- [first_lp.json](../results/wang_code_lp/first_lp.json): adding first moment constraints is feasible; the LP can concentrate all 20 columns in rank-1 points, so first moments alone are very weak.
- [pair_lp.json](../results/wang_code_lp/pair_lp.json): adding pair-category second moments remains feasible. The LP solution has fractional/integral-like column counts `rank1=0, rank2=10, rank3=10` in one relaxation.
- [simple_milp_dualint.json](../results/wang_code_lp/simple_milp_dualint.json), `first_milp_dualint.json`, `pair_milp_dualint.json`: adding integrality for split/dual/pair variables remains feasible. The strongest pair MILP returns column rank counts `rank1=8, rank2=4, rank3=8` and integer weight enumerator
  \[
  A_w: 1 + 2y^4+3y^5+23y^6+32y^7+48y^8+130y^9+90y^{10}+28y^{11}+82y^{12}+51y^{13}+7y^{14}+12y^{15}+3y^{16}.
  \]
  Its dual enumerator is nonnegative/integer with nonzero weights 4--17.

Script: [wang_code_triple_moment.py](../code/wang_code_triple_moment.py).

- [triple_lp.json](../results/wang_code_lp/triple_lp.json): third-moment relaxation with 260 triple categories is feasible.
- [triple_milp.json](../results/wang_code_lp/triple_milp.json): integer third-moment relaxation is also feasible in ~2.5 s after building categories. It returns column rank counts `rank1=9, rank2=5, rank3=6` and integer enumerator
  \[
  A_w: 1 + 8y^4 + 45y^6 + 36y^8 + 128y^9 + 47y^{10} + 128y^{11} + 100y^{12} + 3y^{14}+15y^{16}+y^{18}.
  \]

Interpretation: ordinary MacWilliams constraints, rank-split first/second/third moments, and integer aggregate categories do **not** exclude the \([20,9]\) support. Any eventual nonexistence proof must use more of the orbit-refined subspace structure than these global moments capture. This makes the suggested code view useful, but the cheap LP is not enough.

## T-level branch status with dim<=3 and dim8 cuts

Existing analysis CP-SAT branch outputs:

- Rank-3 branch: [enhanced_s20_dim3_branch_rank3_pilot.json](../../occupation_and_completion/results/wang_capacity_branch_pilots/enhanced_s20_dim3_branch_rank3_pilot.json) was INFEASIBLE with all dim<=3 cuts.
- Rank-2 branch: background `s7_t43_tool1` delivered [enhanced_s20_dim3_branch_rank2.json](../../occupation_and_completion/results/wang_capacity_branch_rank2/enhanced_s20_dim3_branch_rank2.json), also INFEASIBLE with all dim<=3 cuts.
- Rank-1 branch: background `s7_t42_tool1` delivered [enhanced_s20_dim3_branch_rank1.json](../../occupation_and_completion/results/wang_capacity_branch_rank1/enhanced_s20_dim3_branch_rank1.json); after five solved candidates and 834,700 cuts, iteration 6 was UNKNOWN. The last candidates still had higher-dimensional violations.

Independent HiGHS MIP checks:

- [mip_s20_dim3_branch_rank1.json](../../occupation_and_completion/results/wang_capacity_branch_pilots/mip_s20_dim3_branch_rank1.json) found a dim<=3 feasible rank-1-branch support with rank histogram `{rank1:15, rank2:3, rank3:2}` in ~183 s.
- Full Wang check of that support, [mip_s20_dim3_branch_rank1_full_capacity_check.json](../../occupation_and_completion/results/wang_capacity_branch_pilots/mip_s20_dim3_branch_rank1_full_capacity_check.json), finds 851 violations (dims 4--8, max excess 3). Thus it is only a dim<=3 witness, not an admissible A-support.
- [t_level_s20_dim3_full_capacity_check.json](../../occupation_and_completion/results/wang_capacity_mip/t_level_s20_dim3_full_capacity_check.json) similarly checks the unbranched dim<=3 HiGHS support and finds 807 full violations.
- An independent HiGHS MIP for the rank-2 branch, [mip_s20_dim3_branch_rank2.json](../../occupation_and_completion/results/wang_capacity_branch_pilots/mip_s20_dim3_branch_rank2.json), timed out at 900 s; it does not reproduce the CP-SAT infeasibility. Therefore rank-2 branch infeasibility is not yet a mathematical proof even though CP-SAT found it.
- Adding all dim-8 hyperplane/code-weight constraints to the unbranched selected-dimension MIP ([t_level_s20_dims1238.json](../../occupation_and_completion/results/wang_capacity_code_mip/t_level_s20_dims1238.json)) timed out at 600 s with no solution or infeasibility proof.
- CP-SAT with initial dim 1,2,3,8 cuts ([t_level_s20_dims1238_lazy.json](../../occupation_and_completion/results/wang_capacity_code_cpsat/t_level_s20_dims1238_lazy.json)) found two candidates and then UNKNOWN. Candidate 2 has rank histogram `{rank1:18, rank2:2}`, passes dims 1,2,3,8 by construction, but full check `t_level_s20_dims1238_iter2_full_capacity_check.json` still has 302 violations in dims 4--7. Branch rank-1 version (`t_level_s20_dims1238_branch_rank1_lazy.json`) behaves similarly and remains UNKNOWN.

## Proof-producing branch CNF

Script: [wang_capacity_cnf_branch.py](../../occupation_and_completion/code/wang_capacity_cnf_branch.py).

Rank-3 branch CNF for T-level \(s=20\) with Wang dim<=3 constraints:

- CNF: `workspace/data/wang_capacity_cnf/t_s20_dim123_branch_rank3.cnf`
- Metadata: [t_s20_dim123_branch_rank3.meta.json](../../occupation_and_completion/results/wang_capacity_cnf/t_s20_dim123_branch_rank3.meta.json)
- DRAT proof: `workspace/data/wang_capacity_cnf/t_s20_dim123_branch_rank3.drat`
- CaDiCaL log: `workspace/data/wang_capacity_cnf/t_s20_dim123_branch_rank3.cadical2.log`
- DRAT verifier log: `workspace/data/wang_capacity_cnf/t_s20_dim123_branch_rank3.drat_trim.log`
- Kissat cross-check log: `workspace/data/wang_capacity_cnf/t_s20_dim123_branch_rank3.kissat.log`

The CNF has 6,088 variables and 668,175 clauses. CaDiCaL returned UNSAT with proof; `drat-trim` returned `s VERIFIED`; Kissat independently returned UNSAT. Hashes recorded in shell output:

- CNF SHA256 `541bb859660aaa2cb1de0132cc257e0d9b8517fcb8f76fc6720599fd3c801994`
- DRAT SHA256 `6fb2b982bc39ea697d3c6e16b6d3bc437f0d555a8042c909a329348a339f504b`
- metadata SHA256 `91abbdf756414ca2d89282491443c58dd1c6c458d2fd300f59f362461e2f40a4`
- verifier log SHA256 `df992634b8757e0606b57c333eedb7015e4283b732101368324b05971117ba20`

This is a compact independently replayable exclusion of the all-rank-3 A-support branch under dim<=3 Wang occupation constraints. It is still not a T-level lower bound, because rank-1 remains open and rank-2 needs a proof-producing reproduction.

A background task `s8_t34_tool1` is running the analogous rank-2 branch CNF/DRAT proof in `workspace/data/wang_capacity_cnf_rank2/` using [run_rank2_branch_cnf_proof.sh](../../occupation_and_completion/code/run_rank2_branch_cnf_proof.sh).

## Core near-miss A-support filtering

Script: [check_nearmiss_capacity.py](../../occupation_and_completion/code/check_nearmiss_capacity.py).

Using research_record's rank-21 core pools and equal-W deficiency-one near misses:

- [near_miss_capacity_E11.json](../../occupation_and_completion/results/nearmiss_capacity/near_miss_capacity_E11.json): all 815 E11 equal-W rank-19 near-miss A-multisets fail complete Wang-derived E11-core capacity constraints. Failures are often small: 32 have max excess 1, 783 have max excess 2.
- [near_miss_capacity_E13_E22_E31.json](../../occupation_and_completion/results/nearmiss_capacity/near_miss_capacity_E13_E22_E31.json): all 626 H3 near-miss A-multisets fail, more strongly; max excess ranges 4--10.
- Summary: [near_miss_capacity_summary.json](../../occupation_and_completion/results/nearmiss_capacity/near_miss_capacity_summary.json).

Interpretation: research_record's sampled rank-21 equal-W near-miss surfaces are not viable fixed-A supports for rank-19 cores under Wang occupation constraints. This does not prove core rank >=20; it rules out those exact A-multisets and helps explain why local two-replacement repair was failing.

## Peer artifact incorporated

Read and hashed research_record's E11 quotient orbit compression:

- Summary: `data/e11_subspace_orbits/e11_subspace_orbit_summary.json`
- Arrays: `data/e11_subspace_orbits/e11_subspace_orbits.npz`
- SHA256 checked: `fcb43b3f4f20f27a126e31835435f0ef3c3195df95b893d5c3767aa3ac5a0260`

This compression states that the 417,199 E11 core constraints form 1,496 orbits under the verified quotient action, with constant dimension/L/cap on orbits. It is useful for future replayable E11 proof objects but is not itself a lower bound.

## Current scientific interpretation

The T-level capacity route is now sharper: all-rank-3 A-supports are certifiably excluded already by low-dimensional Wang cuts; rank-2 is very likely similarly excluded by CP-SAT but needs DRAT verification; any surviving rank-20 capacity support must be in the rank-1 branch and is heavily rank-1 dominated in the solver candidates. Global code moment relaxations remain feasible even through third moments, so they do not provide a cheap Delsarte proof. The decisive work now is either (i) produce proof objects for rank-2 and then attack the rank-1 branch with higher-dimensional orbit cuts or canonical projective-code enumeration, or (ii) if a fully Wang-admissible rank-1 branch support is found, hand it to fixed-A B/C solvers as a much smaller construction surface.

## Late analysis additions after background delivery

### Rank-2 branch proof delivered

Background task `s8_t34_tool1` completed the proof-producing rank-2 branch CNF.

Files under `workspace/data/wang_capacity_cnf_rank2/`:

- CNF: `t_s20_dim123_branch_rank2.cnf`
- metadata: `t_s20_dim123_branch_rank2.meta.json`
- DRAT: `t_s20_dim123_branch_rank2.drat`
- CaDiCaL log: `t_s20_dim123_branch_rank2.cadical.log`
- DRAT verifier log: `t_s20_dim123_branch_rank2.drat_trim.log`
- status: `t_s20_dim123_branch_rank2.status.json`

The CNF has 18,142 variables and 18,547,589 clauses, using all Wang dim<=3 constraints with rank-1 A-points excluded and a canonical rank-2 point fixed. CaDiCaL returned UNSAT, and `drat-trim` returned `s VERIFIED` after checking 663,771 core lemmas and 177,101,896 resolution steps.

Hashes checked by shell:

- CNF SHA256 `129d6159a63518933bfd61459e20e4b2c33fc8fdb13279709283f2c5fd1aa519`
- DRAT SHA256 `1875971f9df357abff575c0be74422c4b14855b5067419fc16069b31008968c9`
- metadata SHA256 `e3d62b0a64e067446f2256a5d656d14c917512d4839c2f219d5e970a95bba264`
- verifier-log SHA256 `3112b41f400b99209dfbd8951790ea56e750f0febcac769def69afce4c42ff42`
- status SHA256 `7e1868aaa735217d0071966640f0c4224e4b80203f98df3f3e74b8d8543fa000`

Together with the rank-3 branch proof, this gives a proof-producing exclusion of every T-level rank-20 A-support whose A-factors all have matrix rank at least 2, already using Wang constraints of dimension at most 3. Therefore any actual \(\mathbb F_2\) rank-20 decomposition of \(T_{\langle3,3,3\rangle}\) must have at least one rank-1 A-factor. By the same matrix-multiplication slot symmetry, the analogous statement should hold in the B and C slots after transporting the Wang table, but the stored proof object here is A-side.

This restores the rank-1 codimension-one core as a mathematically necessary surface for any rank-20 T decomposition: if such a decomposition exists, restrict along the hyperplane killing a rank-1 A-factor and project to the quotient; the corresponding E11-type core has a 19-term A-side support, hence a rank-19 core decomposition. The converse is not true for rank 20; a rank-19 core decomposition only gives the known possible route to a rank<=22 decomposition after adding the rank-3 pivot slice.

### Pure rank-1 A-support subbranch

Script: [rank1_only_capacity.py](../../occupation_and_completion/code/rank1_only_capacity.py) compresses the full 8,283,458 Wang constraints to intersections with the 49 rank-1 projective A-points. It found 427,912 distinct intersections and 149,444 nonvacuous constraints. CP-SAT solved the full pure-rank1 subbranch with fixed E11 as INFEASIBLE in about 136 s after a 173 s compression pass; output [rank1_only_capacity_no_cnf.json](../../occupation_and_completion/results/wang_capacity_rank1_only/rank1_only_capacity_no_cnf.json).

An independent HiGHS MIP cross-check ([rank1_only_capacity_mip.py](../../occupation_and_completion/code/rank1_only_capacity_mip.py), output `rank1_only_capacity_mip.json`) timed out at 300 s, so the pure-rank1 exclusion is not yet a proof object. It is still useful computational evidence: any remaining T-level rank-20 capacity support, if it exists, must contain a rank-1 A-factor but not consist solely of rank-1 A-factors. The observed dim1,2,3,8 lazy candidates with 18--20 rank-1 points fit this picture but still have full Wang violations.
