# repeated-direction E11-core certificate and symmetry compression

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Mathematical scope

This note concerns only the E11 codimension-one core over \(\mathbb F_2\) at length 19.  A rank-19 core decomposition with a repeated projected A-direction must repeat one of the six projective directions whose one-dimensional Wang capacity is 2.  Excluding this branch does **not** prove the E11 core has rank at least 20, because distinct projected A-directions remain open; it also does not settle characteristic-zero rank or full \(T_{\langle3,3,3\rangle}\) rank.

## Induced quotient action

Script: `workspace/scripts/core_repeat_symmetry_and_cnf.py --symmetry-only`

Output: [induced_core_symmetry.json](../../symmetry_and_residuals/results/repeat_branch_certificate/induced_core_symmetry.json)

The stabilizer of the deleted direction \(E_{11}\) inside the standard left/right \(GL_3(\mathbb F_2)\) action with transpose has 1152 elements; without transpose it has 576 elements and with transpose it has 576.  The induced action on the quotient \(\mathbb F_2^9/\langle E_{11}\rangle\) is a permutation action on the 255 nonzero projected directions.

The six directions with capacity two are exactly
\[
[1,2,3,4,32,36]
\]
with quotient labels
\[
E_{12},\ E_{13},\ E_{12}+E_{13},\ E_{21},\ E_{31},\ E_{21}+E_{31}.
\]
These are the two rank-one rulings through the deleted \(E_{11}\) direction.  The no-transpose stabilizer has two orbits
\[
\{1,2,3\},\qquad \{4,32,36\},
\]
and transpose exchanges them.  The full stabilizer has one orbit on all six points.  Therefore any repeated-direction core A-multiset can be transported to one with the representative `p=1` (quotient direction \(E_{12}\)) repeated twice.

## Fixed representative proof-producing CNF

Script: `workspace/scripts/core_repeat_symmetry_and_cnf.py --fixed-repeat 1`

Clean fixed-repeat compact CNF:
- CNF: `workspace/data/repeat_branch_certificate/fixed_repeat_p1.cnf`
- metadata: [fixed_repeat_p1.meta.json](../results/repeat_branch_certificate/fixed_repeat_p1.meta.json)
- fixed repeat: `p=1`, label \(E_{12}\), multiplicity 2
- base token variables before auxiliary: 259
- final CNF: 951878 variables, 1850250 clauses
- constraints encoded: total multiplicity; 12165 compact Wang rows; 255 contraction lower bounds; 252 unconditional quotient-rank cuts

Verified CaDiCaL/DRAT run:
- status: `UNSATISFIABLE`
- CaDiCaL time: 219.253 s
- DRAT verification by `drat-trim`: `s VERIFIED`, 507.638 s
- DRAT output: `workspace/data/repeat_branch_certificate/drat_p1/fixed_repeat_p1.drat`
- status JSON: [fixed_repeat_p1.status.json](../results/repeat_branch_certificate/drat_p1/fixed_repeat_p1.status.json)
- CNF SHA256: `742f9bd17a0fe64e1dbde0fe756588570e338ce0697752cf232165d0c1906c01`
- DRAT SHA256: `e4afe4b92441ef733653fa6419a9f77664ad976de26b7d1195b9b168124a35f8`
- drat-trim log SHA256: `282af50b7101c9bdfcf7fc5eec7a37a0f87825fea2ff565af2c8ce75974eb33b`

Together with the induced quotient-action computation and the row-transport check in [symmetry_row_transport_check.json](../../symmetry_and_residuals/results/repeat_branch_certificate/symmetry_row_transport_check.json), this gives an independently replayable finite-field structural result: no length-19 nonzero projected A-direction multiset for the E11 core that satisfies the complete Wang occupation consequences can contain a repeated projected A-direction.  Hence any actual rank-19 core decomposition over \(\mathbb F_2\), whose occupation data must satisfy those complete Wang consequences and whose zero projection is excluded by the core table's zero-dimensional row, must have 19 distinct projected A-directions.

## Smaller Wang-only proof object

A greedy HiGHS shrink of the same fixed-repeat instance found an infeasible subset using only Wang rows:

- script: [shrink_fixed_repeat_iis.py](../../quotient_cores/code/shrink_fixed_repeat_iis.py)
- summary: [shrink_summary.json](../results/repeat_branch_certificate/iis_shrink_p1/shrink_summary.json)
- emitted CNF: `workspace/data/repeat_branch_certificate/iis_shrink_p1/fixed_repeat_p1_iis.cnf`
- metadata: [fixed_repeat_p1_iis.meta.json](../results/repeat_branch_certificate/iis_shrink_p1/fixed_repeat_p1_iis.meta.json)
- selected constraints: 262 Wang rows, no contraction lower bounds, no quotient-rank cuts
- selected rows by dimension: dim2=89, dim4=21, dim5=152
- selected rows by lower bound: L=9 (3 rows), L=12 (68), L=15 (102), L=16 (19), L=17 (70)
- CNF: 24895 variables, 53255 clauses

Verified CaDiCaL/DRAT for the smaller CNF:
- status: `UNSATISFIABLE`
- CaDiCaL time: 31.512 s
- drat-trim: `s VERIFIED`, 23.735 s
- DRAT: `workspace/data/repeat_branch_certificate/iis_shrink_p1/drat/fixed_repeat_p1_iis.drat`
- CNF SHA256: `673426778d1c211ac35b014a3c1baa6f2b0595a2c242f948074d580816234dc9`
- DRAT SHA256: `3f9c1a06cb4eb5f0e2193e9a5be752a708945eb9ae6bfafa9490a14aeb52b419`
- drat-trim log SHA256: `06189eefc71bad881aba868753cce40508d173c2777f57305305788d66c417fe`

This is a much more compact certificate for the normalized repeated direction.  Because it uses only Wang occupation rows, it also shows the repeated branch was already forbidden by a small subset of complete Wang consequences once the repeated direction is fixed.  The quotient-rank work was still important for discovering and focusing this branch, but the final compact certificate does not depend on quotient cuts.

## Independent solver cross-check

Script: [fixed_repeat_milp_replay.py](../code/fixed_repeat_milp_replay.py)

Output: [fixed_repeat_milp_replay.json](../results/repeat_branch_certificate/fixed_repeat_milp_replay.json)

HiGHS fixed each of the six capacity-two directions to multiplicity two in the compact model and returned infeasible for all six:

\[
(1,0.119s),\ (2,0.297s),\ (3,3.993s),\ (4,0.080s),\ (32,0.075s),\ (36,0.079s).
\]

This is not the proof object, but it is a semantic cross-check that the symmetry-reduced representative is not an artifact.

## Full-table CNF expansion assessment

Script: [core_cnf_expansion_assessment.py](../../quotient_cores/code/core_cnf_expansion_assessment.py)

Output: [cnf_expansion_assessment.json](../results/repeat_branch_certificate/cnf_expansion_assessment.json)

With sequential-counter expansion:

- compact fixed-repeat Wang rows alone: about 290k clauses and 129k auxiliary variables before contraction/qcut clauses;
- compact fixed-repeat full CNF with qcuts/contractions actually built above: 1.85M clauses;
- full-table fixed-repeat Wang rows (417198 nontrivial rows, excluding the zero/ambient tautological distinction used in the encoding): about 63.9M Wang clauses and 30.0M auxiliary variables before contraction/qcut clauses;
- full-table no-fixed token model: about 66.3M Wang clauses and 31.2M auxiliary variables.

The full core table including dimensions 0 through 8 contains 417199 rows; the 417198 count above is the nontrivial encoded Wang-row count used by the full-table SAT assessment.

Thus the full 417198-row core table is not a small proof-producing SAT instance merely because it has 255--261 multiplicity variables.  The compact learned-row formulation and the smaller Wang-only fixed-repeat proof are currently the appropriate certified objects; full-table feasibility remains a separate difficult computation.

## Relation to related analysis record

related analysis reports a characteristic-zero cyclic/traceless obstruction via a Jennrich-commutator theorem closing their `(10,4)` BILR branch.  This is independent of the finite-field E11-core evidence here.  The E11 work remains relevant for finite-field upper/lower-bound routes and non-cyclic constructions, while related analysis's result should be preserved as characteristic-zero cyclic-route evidence rather than conflated with the \(\mathbb F_2\) Wang/support problem.
