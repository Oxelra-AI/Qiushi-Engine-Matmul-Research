# Wang occupation support proof skeleton for the fixed-E11 branch over F2

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

This is a research-facing mathematical assembly note for the finite-field Wang route.  It records the objects, implications, finite branch partitions, and proof leaves currently available for the rank-20 A-support problem over \(\mathbb F_2\).  It is not a final result for the original rank-22 / rank-23 problem: several leaves remain open, and the Wang table still needs an independent re-expansion from the 496 Wang certificate orbits.

## 1. Ambient support problem

Let
\[
P_A=(\mathbb F_2^9\setminus\{0\})
\]
be the projective A-factor space, represented in code by nonzero 9-bit masks.  A length-20 tensor decomposition over \(\mathbb F_2\) gives a multiset \(S\subset P_A\) of 20 A-factor directions, counted with multiplicity.

The Wang table is a finite set of pairs \((\Phi,L(\Phi))\), where \(\Phi\le \mathbb F_2^9\) is an A-side restriction subspace and \(L(\Phi)\) is a certified lower bound for the corresponding restricted tensor.  For every length-\(s\) decomposition,
\[
 |S\cap(\Phi\setminus\{0\})| \le s-L(\Phi).
\]
For the rank-20 support problem this becomes
\[
 |S\cap(\Phi\setminus\{0\})| \le 20-L(\Phi).
\]
The local expanded table is

- `workspace/data/wang_f2_lb20/wang_subspace_lut.pkl`

and contains 8,283,458 subspaces with `coverage_ok=true` and `conflict_count=0`.

All one-dimensional rows have \(L=19\).  Hence every projective A-direction has capacity one in a length-20 Wang-admissible support.  The multiset is therefore a 20-point set for this support problem.

Evidence file:

- [dim1_lut_lb19_check.json](../../occupation_and_completion/results/wang_capacity_rank1_count_cnf/dim1_lut_lb19_check.json)

## 2. First split by matrix rank of A-factors

The action of \(GL(3,2)\times GL(3,2)\rtimes C_2\) is transitive on rank-1 matrices, transitive on rank-2 matrices, and transitive on rank-3 matrices.

analysis closed the branches with no rank-1 A-factor using Wang dimension \(\le 3\) rows and independent DRAT verification:

- all factors rank 3: `workspace/data/wang_capacity_cnf/`
- factors rank 2 or 3 with at least one rank-2 representative fixed: `workspace/data/wang_capacity_cnf_rank2/`

Thus any remaining length-20 Wang-admissible support must contain a rank-1 A-factor.  By transitivity, fix that direction to
\[
E_{11}=1.
\]

## 3. Fixed-E11 second-point partition

With E11 fixed, the Stab(E11) action has 1,152 elements and partitions the other 510 projective points into eight orbits with representatives
\[
2,10,16,17,20,84,160,161.
\]
The branch rule is: the second selected point is fixed to one of these representatives and all earlier-orbit points are omitted.  This partitions every fixed-E11 support with at least two distinct points exactly once.

Executable partition certificate:

- script: [certify_wang_branch_partition.py](../code/certify_wang_branch_partition.py)
- output: [fixed_e11_partition_certificate.json](../../finite_certification/results/wang_branch_partition/fixed_e11_partition_certificate.json)

The output records:

```json
{
  "single_orbits_partition_non_E11_points": true,
  "all_high_pair_orbits_partition_pairs": true,
  "remaining_exact18_pair_orbits_partition_pairs": true
}
```

Previously verified fixed-E11 second-point leaves:

- rep 17: `workspace/data/wang_capacity_e11_fixed/rep_017_trim_retry/`
- rep 20: `workspace/data/wang_capacity_e11_fixed/rep_020/`
- rep 84: `workspace/data/wang_capacity_e11_fixed/rep_084/`
- rep 160: `workspace/data/wang_capacity_e11_fixed/rep_160/`
- rep 161: `workspace/data/wang_capacity_e11_fixed/rep_161/`

Open fixed-E11 second-point branches at the full support level:

- rep 2
- rep 10
- rep 16

## 4. Rank-1 count split inside the fixed-E11 branch

Let \(k\) be the number of rank-1 A-directions in the 20-point support.  The rank-1 projected Wang system is sound for the full support problem because
\[
|S_{r=1}\cap\Phi| \le |S\cap\Phi| \le 20-L(\Phi).
\]

Using only projected rows with rank-1 intersection size at most 9, the exact-19 rank-1 CNF is DRAT-verified unsatisfiable:

- fixed E11: [rank1_count_ge19_size_le09.status.json](../../occupation_and_completion/results/wang_capacity_rank1_count_cnf/rank1_count_ge19_size_le09.status.json)
- no fixed point retry: [rank1_count_ge19_nofixed_size_le09.status.json](../../occupation_and_completion/results/wang_capacity_rank1_count_cnf/nofixed_retry/rank1_count_ge19_nofixed_size_le09.status.json)

Therefore \(k\le18\) for any remaining support.  Exact-18 rank-1 sets are not excluded by projection alone: the witness

- [rank1_count_18_full_projection_witness.json](../../occupation_and_completion/results/wang_capacity_rank1_count_cnf/rank1_count_18_full_projection_witness.json)

passes the full Wang table as an 18-point support, but it is not a 20-point tensor decomposition and it does not automatically admit higher-rank completion.

## 5. Exact k = 18 finite high-pair branch

If \(k=18\), then exactly two selected A-points have matrix rank 2 or 3.  Single-high prefix tests prove that an exact-18 support cannot contain a higher-rank point in Stab(E11) single orbits 10, 84, or 161.  Verified proof directories:

- `workspace/data/rank1_fixed_high_filtered_cnf/high10_e11_exact18_max7/`
- `workspace/data/rank1_fixed_high_filtered_cnf/high84_e11_exact18_max7/`
- `workspace/data/rank1_fixed_high_filtered_cnf/high161_e11_exact18_max7/`

The remaining exact-18 higher-rank points are all rank-2 points in single orbits 17, 20, and 160.  The partition certificate recomputes that these 276 points have 69 unordered Stab(E11) pair orbits, covering \(\binom{276}{2}=37,950\) pairs disjointly.

All 69 high-pair orbit representatives are DRAT-verified unsatisfiable:

- Pair indices 0--4: `workspace/data/rank1_fixed_high_filtered_cnf/pair_000_*` through `pair_004_*`
- Pair indices 5--6: `workspace/data/rank1_pair_filtered_proof_batch/pilot_005_006/`
- Pair indices 7--68: `workspace/data/rank1_pair_filtered_proof_batch/batch_007_068/`

Filter breakdown: 66 pairs closed at max-intersection-size ≤ 7; 3 pairs needed max ≤ 9
(pair indices 2 = (17,26), 28 = (20,38), 65 = (160,304)).  For those 3, the max-7
filtered row family is SAT and must not be counted as a proof leaf.

Status summary: [wang_branch_status_summary-9a369b1.json](../results/wang_branch_partition/wang_branch_status_summary-9a369b1.json)
(exact18_pair_verified_count = 69, exact18_pair_missing_proof_count = 0).

**The exact k=18 branch is now completely closed.**

## 6. Residual-row subtraction soundness

For any fixed selected prefix \(F\subset P_A\), a Wang row \((\Phi,L(\Phi))\) gives the residual inequality
\[
 |X\cap(\Phi\setminus\{0\})| \le 20-L(\Phi)-|F\cap(\Phi\setminus\{0\})|,
\]
where \(X\) denotes the remaining unfixed selected points.  This is just the original occupation inequality with the fixed terms moved to the right-hand side.

The exact-18 fixed-high scripts compress full Wang rows by their intersection with the 49 rank-1 points and retain the tightest residual capacity for each intersection mask.  Keeping a filtered subfamily, such as all compressed rows with rank-1 intersection size at most 7 or 9, is sound because every retained row is a consequence of an original Wang row after subtracting fixed high points.  Such filtering can weaken the formula; it cannot create a false unsatisfiability if the CNF and DRAT replay are correct.

Relevant scripts:

- [rank1_fixed_high_cnf.py](../../occupation_and_completion/code/rank1_fixed_high_cnf.py)
- [rank1_fixed_high_filtered_cnf.py](../../occupation_and_completion/code/rank1_fixed_high_filtered_cnf.py)
- [rank1_pair_filtered_proof_batch.py](../../occupation_and_completion/code/rank1_pair_filtered_proof_batch.py)

## 7. k = 1..17 range machinery

The exact-18 pair approach will not scale to lower \(k\), where the number of higher-rank selected points grows.  analysis introduced a range-level encoding to avoid enumerating triples, quadruples, and larger high-point configurations.

New scripts:

- [wang_fixed_e11_range_cpsat.py](../code/wang_fixed_e11_range_cpsat.py)
- [wang_fixed_e11_range_ablation.py](../code/wang_fixed_e11_range_ablation.py)
- [wang_fixed_e11_range_cnf.py](../code/wang_fixed_e11_range_cnf.py)

The range formula fixes E11 and optionally a second-point representative, constrains \(1\le k\le17\), uses total support size 20, encodes all Wang rows in dimensions 1--3, encodes dimensions 4--8 through the fixed prefix, and adds the full compressed rank-1 projection.

Current probes:

- no second representative fixed: [e11_k01_17_dim123_throughE11_rank1proj.json](../results/wang_fixed_e11_range_cpsat/e11_k01_17_dim123_throughE11_rank1proj.json), result `UNKNOWN` after 600 s;
- rep 2: [e11_rep002_k01_17_dim123_throughfixed_rank1proj.json](../results/wang_fixed_e11_range_cpsat/rep002_k01_17/e11_rep002_k01_17_dim123_throughfixed_rank1proj.json), result `OPTIMAL` with rank histogram `{1:17,2:3}`; full LUT scan found 246 violations; one seeded rerun became `UNKNOWN`;
- rep 10: [e11_rep010_k01_17_dim123_throughfixed_rank1proj.json](../results/wang_fixed_e11_range_cpsat/rep010_k01_17/e11_rep010_k01_17_dim123_throughfixed_rank1proj.json), result `INFEASIBLE` in CP-SAT, but DIMACS replay is very large and did not solve within 900 s;
- rep 16: [e11_rep016_k01_17_dim123_throughfixed_rank1proj.json](../results/wang_fixed_e11_range_cpsat/rep016_k01_17/e11_rep016_k01_17_dim123_throughfixed_rank1proj.json), result `OPTIMAL` with rank histogram `{1:14,2:6}`; full LUT scan found 555 violations; one seeded rerun became `UNKNOWN`.

The range machinery is the correct replacement for naive high-point tuple enumeration, but rep2 and rep16 need fundamentally stronger row selection, not just more solver time.

analysis built [wang_fixed_e11_symm_range_cpsat.py](../code/wang_fixed_e11_symm_range_cpsat.py) which adds orbit-closure of seed rows under Stab(E11, rep) and lex-leader symmetry breaking.  Results:

- rep 2 with orbit-closed seeds (11,040 keys from 394 raw): `UNKNOWN` after 600 s;
- rep 2 without seeds but with lex-leader: `OPTIMAL` {1:16,2:2,3:2}, 547 full-LUT violations;
- rep 10 with through-dim-6 only: `UNKNOWN` after 600 s;
- rep 16 with orbit-closed seeds (2,796 from 200 raw): `UNKNOWN` after 600 s.

The lex-leader approach prevents the solver from finding orbit-equivalent solutions but does not close the model.  The violated rows concentrate in dims 5--7 at lb=12--15, pointing to specific restricted tensors where Wang's backtracking search hit its iteration limit.

The remaining viable approaches for k=1..17 are:
1. Find a compact enough CNF for rep10 (already CP-SAT INFEASIBLE, needs a smaller DIMACS);
2. Raise the Wang occupation lower bounds on the weak dim-5/6 subspaces through deeper recursion;
3. Develop an alternative rank-1-count-aware proof mechanism that avoids the full-LUT encoding.

## 8. Current mathematical route to an F2 improvement

A proof of \(R_{\mathbb F_2}(T_{333})\ge21\) by this route would require:

1. Wang table foundation independently reproduced from the 496 certificate orbits.
2. No-rank-1 branches closed by existing DRAT leaves.
3. Fixed-E11 branch covered by the second-point partition above.
4. Reps 17,20,84,160,161 covered by existing fixed-E11 DRAT leaves.
5. Reps 2,10,16 covered for all \(k=1,\ldots,18\):
   - exact \(k=18\) needs all 69 high-pair leaves verified;
   - \(k=1,\ldots,17\) needs range-level proof objects or a finer finite branch with partition script support.

Only after these items are finished and independently checked would the finite-field support proof imply that no rank-20 decomposition over \(\mathbb F_2\) exists.  Even that result would be a finite-field lower-bound ARTIFACT, not the original characteristic-zero rank-23 optimality theorem.

## Cyclic three-slot consequence for hypothetical length-20 decompositions

The matrix multiplication tensor is cyclically invariant under the standard identification of the three factor spaces (up to the usual cyclic permutation of the bilinear input and output slots).  Therefore Wang's occupation implication is not only an A-factor necessary condition.  Applying the same argument after cyclically permuting the tensor slots gives the identical projective support restrictions for the B-factor support and for the C-factor support of any length-20 decomposition over \(\mathbb F_2\).

Consequently any hypothetical rank-20 decomposition over \(\mathbb F_2\) must satisfy, separately in each of its three factor lists:

1. at least one rank-1 projective direction occurs, by the verified no-rank-1 branch exclusions;
2. no projective direction is repeated, because every one-dimensional Wang row has lower bound 19 and hence capacity 1 at length 20;
3. at most 18 rank-1 projective directions occur, by the verified rank-1 projected count proof;
4. after moving a rank-1 direction to \(E_{11}\), the same fixed-\(E_{11}\) branch information applies in that slot, including the closed second-point representatives \(17,20,84,160,161\) and the closed exact-\(k=18\) leaves.

This does not by itself prove a new lower bound, because it is still three separate support-level necessary information.  Its value is that any fixed-A lift or B/C-factor solve should impose Wang support restrictions on B and C as well, rather than treating those factor supports as unconstrained once an A-support has been selected.  A candidate A-support that survives the A-side table should therefore be passed forward as a coupled three-slot support problem.
