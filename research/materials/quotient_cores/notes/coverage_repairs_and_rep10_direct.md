# execution notes: coverage repair and rep10 direct branch tests

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Why this ARTIFACT changed the plan

The singleton/pair hierarchy from analysis is useful as a source of structure and proof targets, but it cannot be used by deleting variables from a proof-producing CNF unless the deleted cases themselves are certified. A CNF over only singleton-surviving or pair-surviving higher-rank variables would certify only the conditional reduced problem. For a formal branch exclusion, either every singleton/pair implication used in the reduction must be independently certified, or the replay formula must keep the original branch variables and encode explicit Wang rows whose contradiction is checked.

Two coverage repairs followed.

1. [singleton_hr_feasibility_survey.py](../code/singleton_hr_feasibility_survey.py) was patched so a singleton solver status other than `INFEASIBLE`, `OPTIMAL`, or `FEASIBLE` is recorded as unknown rather than as infeasible.
2. [general_singleton_pair_survey.py](../code/general_singleton_pair_survey.py), `exhaustive_canonical_pairs.py`, and `pair_and_triple_survey.py` were patched so survivor sets are `FEASIBLE/OPTIMAL + UNKNOWN`, not only explicitly feasible orbits.

The audit script [audit_and_manifest.py](../code/audit_and_manifest.py) wrote the durable coverage manifest
[coverage_and_proof_targets.json](../results/coverage/coverage_and_proof_targets.json) and a corrected survivor file
[rep2_k17_survivors_corrected.json](../results/coverage/rep2_k17_survivors_corrected.json).

## Important bookkeeping correction

The analysis file [rep2_k17_survivors.json](../results/singleton_survey/rep2_k17_survivors.json) has inconsistent summary fields: orbit 17 was `UNKNOWN` in the row records but appears in both `infeasible_reps` and `feasible_reps`. The corrected interpretation is:

- rep2/k=17 singleton-INFEASIBLE orbits: `[10, 12, 20]` only;
- rep2/k=17 singleton-UNKNOWN orbits: `[17]`;
- rep2/k=17 singleton feasible/optimal orbits: `[25, 28, 33, 34, 35, 80, 84, 96, 98, 160, 161, 224, 225]`;
- conservative survivors: `[17, 25, 28, 33, 34, 35, 80, 84, 96, 98, 160, 161, 224, 225]`.

Any pair enumeration that omitted the unknown orbit 17 would be incomplete. The running analysis rep2/k=17 task used `rep2_k17_survivors.json`; its output must therefore be audited against the corrected survivor set before claiming CP-SAT closure.

## rep10 k-range correction

Because the second fixed point in branch rep10 is rank 2, rep10 still has a possible total rank-1 count `k=1`. Closing only `k=2..17` would not cover the branch. This ARTIFACT handled `k=1` directly.

### rep10 exact k=1 evidence

Two direct original-branch CP-SAT probes were run, both keeping all branch variables and excluding only earlier second-orbit points:

1. Small 14,478-row family:
   - file: [rep10_exact_k1_dim1_through46_no_rank1proj.json](../results/rep10_k1/rep10_exact_k1_dim1_through46_no_rank1proj.json)
   - rows: dim 1 plus rows of dims 4 and 6 through fixed `(E11,10)`;
   - exact rank-1 count: 1;
   - rank-1 projected rows disabled;
   - result: `INFEASIBLE`;
   - build: about 10.04 s; solve: about 30.42 s.

2. Larger full-through-E11 family:
   - file: [rep10_exact_k1_fullthroughE11_dim123_t48_rank1proj.json](../results/rep10_k1/rep10_exact_k1_fullthroughE11_dim123_t48_rank1proj.json)
   - rows: 1,234,292 Wang rows plus 38,756 rank-1 projected rows;
   - exact rank-1 count: 1;
   - result: `INFEASIBLE`;
   - build: about 59.92 s; solve: about 282.53 s.

These are CP-SAT evidence, not proof-checked lower-bound components.

### rep10 exact k=17 direct confirmation

A direct original-branch CP-SAT probe for exact `k=17` using the same 14,478-row family also returned `INFEASIBLE`:

- file: [rep10_exact_k17_dim1_through46_no_rank1proj.json](../results/rep10_k17/rep10_exact_k17_dim1_through46_no_rank1proj.json);
- build: about 10.25 s; solve: about 27.38 s.

This direct formula avoids relying on singleton-variable elimination for k=17, though it is still not formally certified.

## rep10 hierarchy result received during analysis

The managed analysis task `s24_t30_tool1` finished and wrote [rep10_full_k_descent.json](../results/singleton_survey/rep10_full_k_descent.json).

At the CP-SAT hierarchy level:

- exact k=16,15,14 closed by all 24 singleton orbit representatives being infeasible;
- exact k=13 closed by 45/45 canonical pair classes infeasible among the 42 surviving higher-rank points;
- exact k=12 did not close at the pair-relaxation level: 477/481 canonical pair classes infeasible, but four pair classes were feasible, first `[12,14]` with support `[1,10,12,14,16,24,56,128,192,256,292,320,365,438,511]` (only 15 total points because the query is a pair relaxation, not a full support at k=12).

A conservative clique test was then run from the k=12 pair graph:

- script: [pair_graph_clique.py](../code/pair_graph_clique.py);
- output: [rep10_k12_pairgraph.json](../results/rep10_pairgraph/rep10_k12_pairgraph.json);
- surviving HR points after singleton tests: 204;
- feasible/unknown/missing pair graph edges: 40;
- clique number found: 3;
- required additional HR points for k=12 in rep10: `20 - 12 - 1 = 7` (subtracting the permanent rank-2 point 10);
- therefore k=12 is closed at the same CP-SAT pair-evidence level, provided every pair exclusion used and the singleton eliminations are eventually certified.

A k=11 singleton-only/pair-count run was also performed:

- output: [rep10_k11_singletons_paircount.json](../results/rep10_pairgraph/rep10_k11_singletons_paircount.json);
- 7 singleton-infeasible orbits, 17 survivor orbits;
- 260 surviving HR points;
- 757 canonical pair classes, too many for the current small pair enumeration setting.

Thus the hierarchy has useful structure down to k=12, but k<=11 remains open at the hierarchy level.

## New proof-target machinery

Two scripts were built:

- [rep10_exactk_row_core_cp.py](../code/rep10_exactk_row_core_cp.py): extracts CP-SAT row-core targets for a given exact k while keeping the original branch variables.
- [fixed_branch_rowcore_cnf.py](../../occupation_and_completion/code/fixed_branch_rowcore_cnf.py): converts an explicit row-core JSON with `core_keys` into a CNF that keeps the original branch variables, total support cardinality, optional exact rank-1 count, and exactly those Wang rows.

Row-core shrink tasks for rep10 k=1 and k=17 completed but did not shrink: the assumption-core query timed out/UNKNOWN at 120 s, and the final unassumed 14,478-row formulas remained CP-SAT `INFEASIBLE` in about 30 s (k=1) and 26 s (k=17). The row-core files are:

- [rep10_k01_dim1_through46_rowcore.json](../results/rep10_rowcores/rep10_k01_dim1_through46_rowcore.json);
- [rep10_k17_dim1_through46_rowcore.json](../results/rep10_rowcores/rep10_k17_dim1_through46_rowcore.json).

A CNF/DRAT attempt for rep10 exact k=1 was submitted as `s25_t21_tool1` and is still unresolved at the time of this note.

## Running work left for next ARTIFACT

Managed tasks that may deliver later:

- `s24_t20_tool1`: rep2/k=17 exhaustive canonical pairs. Must be audited for conservative survivor coverage including the UNKNOWN orbit 17.
- `s25_t11_tool2`: rep16/k=15 exhaustive pairs with `--max-pairs 5000`.
- `s25_t21_tool1`: rep10 exact k=1 CNF/DRAT proof attempt.
- `s25_t38_tool1`: direct original-branch CP-SAT scan for rep10 exact k=2..12 using the 14,478-row family.

## Current scientific status

No rank-22 algorithm and no rank-23 optimality proof has been obtained. The verified finite-field lower bound is still only `R_F2 >= 20` plus earlier DRAT-verified local branch exclusions. This ARTIFACT strengthens the execution route by correcting coverage, adding rep10 k=1 CP-SAT evidence, exposing rep10 k=12 as pair-graph closed at CP-SAT level, and creating proof-target scripts that do not hide CP-SAT reductions inside smaller formulas.
