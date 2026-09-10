# E11 prefix-completion coupling experiments

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Scientific purpose

The analysis canonical A-multiset tree produced 119,957 complete-Wang surviving canonical prefixes already at depth 4, so Wang-only augmentation is unlikely to scale to depth 19 by naive continuation. analysis tested whether exact tensor equations can be coupled to a prefix before a full A-multiset is generated.

The active finite-field route remains:

\[
R_{\mathbb F_2}(\mathrm{E11}) \le 19 \Longrightarrow R_{\mathbb F_2}(T_{333}) \le 22
\]

by adding the three removed elementary E11-slice products. None of the experiments below proves or disproves rank 19 for E11 or rank 22/23 for the original problem.

## Exact prefix-completion SAT

New script:

- [e11_prefix_completion_xor_sat.py](../code/e11_prefix_completion_xor_sat.py)

For fixed prefix A-masks `p_0,...,p_{k-1}`, it asks whether there is a rank-`r` CPD of the E11 core whose first `k` A-factors equal the prefix, with all remaining A-factors and all B/C factors free. Since CPD terms are unordered, SAT is existence of a decomposition whose A multiset contains that prefix. UNSAT would remove the entire subtree containing that prefix, up to quotient-symmetry canonicalization. The script uses CryptoMiniSat native XOR and decodes/verifies SAT models.

Calibration:

- Full known rank-21 E11 A-list passed: [rank21_full_known_native.json](../results/e11_prefix_completion_tests/rank21_full_known_native.json), SAT, decoded diff 0, 15,855 variables, 46,095 CNF clauses plus 648 native XORs.
- Full 19-term fixed negative passed as UNSAT: [local_search_9viol_full_native.json](../results/e11_prefix_completion_tests/local_search_9viol_full_native.json), UNSAT in 8.8 s.
- Depth-4 prefixes were not resolved: `[1,2,3,4]` and `[80,122,191,213]` both returned UNKNOWN at 180 s; sorting the free A suffix did not resolve them in 300 s. A known rank-21 4-prefix also returned UNKNOWN, so prefix satisfiability itself is hard in this direct formulation.

## Optimized prefix-completion SAT

New script:

- [e11_prefix_completion_opt_xor_sat.py](../code/e11_prefix_completion_opt_xor_sat.py)

This removes fixed-prefix A variables from the contribution layer: fixed terms contribute their `B_t \otimes C_t` products directly to Brent XORs, while only the free suffix uses variable A bits and `alpha * p` products. The optimized encoder is logically equivalent for prefix containment but much smaller for long prefixes.

Calibration:

- Full known rank-21 list: [rank21_known_full_opt_native.json](../../quotient_cores/results/e11_prefix_opt_rank21_full/rank21_known_full_opt_native.json), SAT, decoded diff 0, 2,079 variables, 5,103 CNF clauses plus 648 native XORs.
- Full 19-term negative: [local_search_full_opt_native.json](../../quotient_cores/results/e11_prefix_opt_full_local/local_search_full_opt_native.json), UNSAT in 9.47 s, 1,881 variables, 4,617 clauses plus 648 native XORs.
- Prefixes of the 19-term negative remained unresolved even near full depth:
  - length 18: [local_search_pref18_opt_native.json](../../quotient_cores/results/e11_prefix_opt_local_pref18/local_search_pref18_opt_native.json), UNKNOWN at 180 s, 2,537 variables, 6,562 clauses plus 648 native XORs.
  - length 16: [local_search_pref16_opt_native.json](../../quotient_cores/results/e11_prefix_opt_local_pref16/local_search_pref16_opt_native.json), UNKNOWN at 180 s.
  - length 12: [local_search_pref12_opt_native.json](../../quotient_cores/results/e11_prefix_opt_local_pref12/local_search_pref12_opt_native.json), UNKNOWN at 180 s.
- Known rank-21 4-prefix remained UNKNOWN at 180 s in the optimized form, confirming that shallow prefix-completion SAT is not a practical refuter in the current encoding.

## A-quotient necessary test for prefixes

New script:

- [e11_make_quotient_core.py](../../quotient_cores/code/e11_make_quotient_core.py)

If a rank-19 E11 decomposition contains a prefix `P`, then after quotienting the A-space by `span(P)` the projected tensor has rank at most `19-|P|`. This is exact and can refute a prefix if the quotient rank is too large.

Runs:

- Prefix `[1,2,3,4]`: quotient shape `(5,9,9)`, remaining rank bound 15, quotient rank-15 SAT in 0.40 s with decoded verification ([q_1_2_3_4_rank15_native.json](../../quotient_cores/results/e11_prefix_quotient_1234_sat/q_1_2_3_4_rank15_native.json)). Therefore quotienting does not refute this prefix.
- Prefix `[80,122,191,213]`: quotient shape `(4,9,9)`, remaining rank bound 15; native SAT returned UNKNOWN at 300 s ([q_leaf0_rank15_native.json](../../quotient_cores/results/e11_prefix_quotient_leaf0_sat/q_leaf0_rank15_native.json)). flip-cpd independently found many verified rank-15 decompositions of this quotient in `workspace/data/q_leaf0_flip_workspace/`, so the quotient condition does not refute the prefix.
- Known rank-21 4-prefix quotient `(4,9,9)` at remaining rank 17 was SAT in 2.8 s with decoded verification ([q_rank21_pref4_rank17_native.json](../../quotient_cores/results/e11_prefix_quotient_rank21_pref4_sat/q_rank21_pref4_rank17_native.json)), supporting the quotient construction semantics.

The quotient test is mathematically clean, but it is generally too weak: rank-15 quotient decompositions exist for sampled depth-4 prefixes while full prefix completion remains unresolved.

## Prefix completion with low-dimensional Wang constraints

New scripts:

- [e11_prefix_completion_wang2_xor_sat.py](../code/e11_prefix_completion_wang2_xor_sat.py)
- [e11_prefix_completion_opt_wang2_xor_sat.py](../code/e11_prefix_completion_opt_wang2_xor_sat.py)

They add all exact singleton caps and the 438 dimension-2 cap-1 triple exclusions from the verified E11 Wang cache to the prefix-completion Brent SAT. The optimized version also eliminates fixed-prefix contribution variables.

Results:

- Full fixed support still UNSAT, as expected.
- Depth-4 prefixes `[1,2,3,4]` and `[80,122,191,213]` became large half-million-clause instances and remained UNKNOWN around 300 s. The optimized version reduced tensor-equation variables but the equality-indicator/at-most clauses dominate at shallow depth.
- Length-18 prefix with one free A term still remained UNKNOWN at 300 s in optimized Wang2 SAT ([local_search_pref18_opt_wang2_native.json](../../quotient_cores/results/e11_prefix_opt_wang2_pref18/local_search_pref18_opt_wang2_native.json)), despite only 2,792 variables and 10,183 CNF clauses. Monolithic prefix SAT is therefore not a good shallow subtree refuter in this form.

## Complete-Wang prefix completion scan

New scripts:

- [e11_prefix_wang_completion_scan.py](../code/e11_prefix_wang_completion_scan.py)
- [e11_prefix_wang_completion_dfs.py](../code/e11_prefix_wang_completion_dfs.py)

For a prefix and a small number of remaining A factors, these scripts test exact completion against all 417,199 E11 Wang occupation inequalities using the dense membership matrix. This is A-side necessary evidence only; it does not solve B/C. The DFS version uses zero-slack propagation instead of copying the whole occupancy vector per tuple.

Results:

- Length-18 prefix `[1,2,3,4,12,16,20,28,32,36,92,97,108,130,144,195,208,216]` has no possible last A mask satisfying complete Wang occupation. File: [local_pref18_wang_completion.json](../results/e11_prefix_wang_completion/local_pref18_wang_completion.json); it tested all 255 last masks in 0.20 s. The best full completion is the known 9-violation support with last mask 252, so the fixed-support Brent UNSAT was not the first reason this subtree dies.
- Length-16 prefix `[1,2,3,4,12,16,20,28,32,36,92,97,108,130,144,195]` also has no 3-term complete-Wang completion. Corrected file: [local_pref16_wang_dfs_v2.json](../results/e11_prefix_wang_completion/local_pref16_wang_dfs_v2.json). The DFS visits root plus five one-term branches and then each branch has no allowed next point. The file's `best_partial_dead_end_recorded` is explicitly only a partial zero-violation dead end, not a full completion.
- Depth-4 prefix `[80,122,191,213]` with 15 remaining terms is still broad. A node-limited exact DFS visited 20k nodes in 32.9 s and did not reach a full survivor or refutation: [leaf0_depth4_wang_dfs_node20k.json](../results/e11_prefix_wang_completion/leaf0_depth4_wang_dfs_node20k.json). It found partial zero-violation paths of length 11 with 4 unfilled terms and then no allowed continuation in that explored branch.

This is the most useful analysis evidence: complete-Wang zero-slack propagation can refute long prefixes extremely quickly and can guide a brancher, but shallow prefixes still have a broad search tree. Tensor-equation SAT did not yet add effective shallow pruning.

## related analysis structural proof artifact cross-check

related analysis published stable rank-2 no-rank1 branch files for the T-level `s=20` Wang dim<=3 proof. I checked the files in `data/wang_capacity_cnf_rank2/`:

- generator script sha256 `052fdf9407cfb338094f285894afb3295ac71b8f54f020bdbe164e654ee0f77d`
- wrapper sha256 `6726bba9041408a8ff8005439df6bcda9231bf9185023622a5dcae95ec242623`
- CNF sha256 `129d6159a63518933bfd61459e20e4b2c33fc8fdb13279709283f2c5fd1aa519`
- DRAT sha256 `1875971f9df357abff575c0be74422c4b14855b5067419fc16069b31008968c9`
- drat-trim log sha256 `3112b41f400b99209dfbd8951790ea56e750f0febcac769def69afce4c42ff42`
- meta sha256 `e3d62b0a64e067446f2256a5d656d14c917512d4839c2f219d5e970a95bba264`
- status sha256 `7e1868aaa735217d0071966640f0c4224e4b80203f98df3f3e74b8d8543fa000`

The meta records branch rank 2, fixed point 17, 462 allowed A points (rank 2 or 3), 18,142 variables, 18,547,589 clauses, and 812,542 dim<=3 Wang rows used. The drat-trim log says `s VERIFIED` with 177,101,896 resolution steps. This supports related analysis's reported T-level structural reduction within its stated Wang dim<=3 branch, but it is still not by itself a full rank lower bound.

## Current judgment

The review proposal was correct: adding tensor equations only at full generated A-multisets is too late. However, the first exact prefix-completion SAT encodings did not supply practical shallow pruning. Complete-Wang prefix propagation, not Brent prefix SAT, currently gives the useful subtree refutations. The next construction should therefore not extend Wang-only depth records or monolithic prefix SAT. It should build a direct coupled E11 brancher that:

1. maintains complete-Wang slack exactly at prefixes;
2. uses quotient-rank tests only as a cheap necessary filter when the quotient dimension/rank bound is genuinely tight;
3. calls optimized fixed-A Brent solving on complete-Wang full supports;
4. learns high-depth no-completion prefixes from complete-Wang DFS and high-value fixed-A UNSAT proofs;
5. if possible, incorporates B/C compatibility incrementally in a way stronger than the current prefix-completion SAT formulation.

No rank-19 E11 witness, no full E11 lower-bound certificate, no rank-22 matrix multiplication algorithm, and no rank-23 optimality proof has been obtained in this ARTIFACT.
