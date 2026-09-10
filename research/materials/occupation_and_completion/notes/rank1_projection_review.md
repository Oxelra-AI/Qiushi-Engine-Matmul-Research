# review: rank-1 projection bound for fixed-E11 Wang supports

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Scientific purpose

The active finite-field route tries to close the remaining T-level Wang occupation problem for a hypothetical length-20 decomposition of \(T_{\langle3,3,3\rangle}\) over \(\mathbb F_2\).  Previous proof objects already exclude all A-supports with no rank-1 matrix, and fixed-E11 second-orbit branches 17, 20, 84, 160, and 161.  The remaining open branches are rank-1-heavy, so the rank-1 projection of the Wang occupation table is now load-bearing.

## New proof component

Let \(R_1\) be the 49 projective rank-1 A-points in \(\mathbb F_2^{3\times 3}\).  For every Wang subspace \(\Phi\), a length-20 A-support satisfying Wang occupation must obey
\[
  \#(A\cap \Phi) \le 20-L(\Phi).
\]
Therefore the rank-1 subset obeys the weaker projected inequalities
\[
  \#(A\cap R_1\cap \Phi) \le 20-L(\Phi).
\]

[rank1_projected_count_cnf.py](../code/rank1_projected_count_cnf.py) encoded exact selection of 19 rank-1 points with \(E_{11}\) fixed, using only the 65,814 projected Wang rows whose rank-1 intersection size is at most 9.  The selected row families are:

| intersection size | cap | rows |
| ---: | ---: | ---: |
| 5 | 4 | 441 |
| 7 | 5 | 1778 |
| 7 | 6 | 26208 |
| 9 | 5 | 637 |
| 9 | 6 | 294 |
| 9 | 8 | 36456 |

These rows produce 139,643 direct subset-forbidding clauses.  With the exact-19 sequential counter and the \(E_{11}\) unit, the DIMACS has 1,189 variables and 141,924 clauses.

Artifacts:

- CNF: `workspace/data/wang_capacity_rank1_count_cnf/rank1_count_ge19_size_le09.cnf`
- metadata: [rank1_count_ge19_size_le09.meta.json](../results/wang_capacity_rank1_count_cnf/rank1_count_ge19_size_le09.meta.json)
- DRAT: `workspace/data/wang_capacity_rank1_count_cnf/rank1_count_ge19_size_le09.drat`
- CaDiCaL log: `workspace/data/wang_capacity_rank1_count_cnf/rank1_count_ge19_size_le09.cadical.log`
- DRAT-trim log: `workspace/data/wang_capacity_rank1_count_cnf/rank1_count_ge19_size_le09.drat_trim.log`

Hashes:

- CNF: `f10cda120b66e4d3fc954ae7ac5f8e5824d5187cfbe424e1804e110f03df7cd3`
- metadata: `7c29381ecb2f4be6f53d7fd733970702eae8b8649b907fbaf678ed4b0e61758a`
- DRAT: `c98a4ad1b4247bb3c431a1bc2b4edacb75dd5e6de4d4e1b074ad3cdb35e3c441`
- CaDiCaL log: `ac38ef4c8fe03d0333bbb60ccc9bc7068e4c83a38a190e5da7fb9c3b4e6184c1`
- DRAT-trim log: `5b8cc691bce396ad233aa9ac5f4daef667e04d4c1abc837fd37a86bbb1d4868a`

CaDiCaL returned `s UNSATISFIABLE` with exit 20.  `drat-trim` returned `s VERIFIED` in 391.052 seconds.  review independently checked the row arithmetic, clause count, and implication in `independent-verification-record`.

## Consequence

The CNF encodes exact 19, not directly at least 19.  The projected Wang inequalities are upper bounds, hence are closed under deleting selected points.  If a projected support containing \(E_{11}\) had at least 19 rank-1 points, one could keep \(E_{11}\) and delete down to exactly 19, contradicting the DRAT-verified UNSAT result.  Therefore every fixed-E11 full Wang-admissible length-20 support contains at most 18 distinct rank-1 A-directions.

To relate directions to factor occurrences, I checked all one-dimensional LUT rows in [dim1_lut_lb19_check.json](../results/wang_capacity_rank1_count_cnf/dim1_lut_lb19_check.json): there are 511 dimension-1 rows and all have lower bound 19.  Thus in a length-20 Wang-admissible support each A-direction has capacity \(20-19=1\).  Repetition of an A-direction is impossible.  The distinct-direction bound is therefore also a bound on rank-1 A-factor occurrences within the Wang-support problem.

A direct lower witness for the projection is stored in [rank1_count_18_full_projection_witness.json](../results/wang_capacity_rank1_count_cnf/rank1_count_18_full_projection_witness.json); it contains 18 rank-1 points including \(E_{11}\), and full LUT scanning in `rank1_count_18_full_projection_witness.full_capacity_check.json` found zero violations.  This shows the rank-1 projection itself reaches 18, but it is not a length-20 tensor decomposition and does not show that two higher-rank points can be added.

## Branch impact

Combining this analysis proof component with previous proof components gives the following finite support picture over \(\mathbb F_2\):

1. No-rank1 length-20 A-supports are already excluded by the analysis DRAT-verified rank-3-only and rank-2/3 branches.
2. Pure rank1 length-20 A-supports are excluded by the analysis DRAT-verified size<=9 projection CNF.
3. Fixed-E11 supports now have at most 18 rank-1 A-factors, so every remaining fixed-E11 support has at least two higher-rank A-factors.
4. Fixed-E11 second-orbit branches 17, 20, 84, 160, and 161 are DRAT-verified UNSAT; branches 2, 10, and 16 remain open.  Branch 10's large pair-through dim6,7,8 CNF did not finish: the managed run ended with CaDiCaL exit 0 after 1800 seconds, so it is not a proof object.

The next execution work should exploit the new count bound: split rep 2 and rep 16 by the first higher-rank point under the stabilizer of the fixed rank-1 pair, and split rep 10 by the next higher-rank point, while imposing rank1-count \(\le18\), the full rank-1 projection, and the high-dimensional Wang rows through the current prefix.  Every SAT support must be scanned against the complete 8,283,458-row LUT; any complete support should be tested by exact fixed-A B/C solving.

## Upstream validation still needed

The proof object proves the generated CNF.  Its use in a tensor-rank theorem still rests on the Wang LUT and action semantics.  research_record has confirmed matching hashes for `workspace/data/wang_f2_lb20/wang_subspace_lut.pkl` (`4704acba23a97d40aa65d5a65222dcb679461fdccf3e41dbeed2a634894a3b33`) and its metadata (`17ab772ff7a2a35f04d7ac60d9e1f0137ce0b34a297bb9c4a96fcff1077207d5`), and has begun independent reconstruction.  this investigation should not present a new finite-field lower-bound theorem until that independent reconstruction, or an equivalent derivation, confirms the row values and coordinate/action conventions.

## Additional analysis validation after peer exchange

research_record independently confirmed the main LUT and analysis fixed rank-1 projection proof hashes:

- related analysis LUT `workspace/data/wang_f2_lb20/wang_subspace_lut.pkl`: `4704acba23a97d40aa65d5a65222dcb679461fdccf3e41dbeed2a634894a3b33`
- LUT metadata: `17ab772ff7a2a35f04d7ac60d9e1f0137ce0b34a297bb9c4a96fcff1077207d5`
- fixed-E11 exact-19 projection CNF: `f10cda120b66e4d3fc954ae7ac5f8e5824d5187cfbe424e1804e110f03df7cd3`
- related analysis also saw `s VERIFIED` in the fixed-E11 rank-1 projection trim log.

I then generated the no-fixed analogue in a separate writable subdirectory, avoiding the stale unwritable empty DRAT from the first attempt:

- CNF: `workspace/data/wang_capacity_rank1_count_cnf/nofixed_retry/rank1_count_ge19_nofixed_size_le09.cnf`
- metadata: [rank1_count_ge19_nofixed_size_le09.meta.json](../results/wang_capacity_rank1_count_cnf/nofixed_retry/rank1_count_ge19_nofixed_size_le09.meta.json)
- DRAT: `workspace/data/wang_capacity_rank1_count_cnf/nofixed_retry/rank1_count_ge19_nofixed_size_le09.drat`
- CaDiCaL log: `workspace/data/wang_capacity_rank1_count_cnf/nofixed_retry/rank1_count_ge19_nofixed_size_le09.cadical.log`
- DRAT-trim log: `workspace/data/wang_capacity_rank1_count_cnf/nofixed_retry/rank1_count_ge19_nofixed_size_le09.drat_trim.log`

Hashes:

- CNF: `90d2f0559d1219bbb5437d704518ce23900e9b587324f60990682d3bd977ebe5`
- metadata: `f2bda46429c0c068ab9ace0e0ef286537490e166081113d2d9dacd6152195a02`
- DRAT: `46a7e94d4456eaffd2e3c123681069bbcfb02ebe571915a315c908048702cf82`
- CaDiCaL log: `dad111f78b9565eabd9c83f0402f5e374cc23f8d8c4af189d4fff9df31349873`
- DRAT-trim log: `2f1e5cf3834a651fbe0fb1ff8c126378bd2c22502d89281770f866c3345687b9`

The no-fixed CNF has 1,189 variables and 141,923 clauses; CaDiCaL reported `s UNSATISFIABLE` and exit 20, and `drat-trim` reported `s VERIFIED` in 752.334 seconds.  This proves the same rank-1 projection bound without relying on transitivity or a fixed rank-1 point: no projected Wang-admissible subset of 49 rank-1 points can have 19 selected directions.  Together with the dimension-1 LUT check ([dim1_lut_lb19_check.json](../results/wang_capacity_rank1_count_cnf/dim1_lut_lb19_check.json), 511/511 one-dimensional rows have LB 19), any length-20 full Wang-admissible A-multiset over \(\mathbb F_2\) has at most 18 rank-1 A-factor occurrences and no repeated A-direction.

## Branch probes using the count bound

I built [wang_capacity_cpsat_fixed_e11_rank1count.py](../code/wang_capacity_cpsat_fixed_e11_rank1count.py), adding explicit rank-1 count constraints to the fixed-E11 CP-SAT brancher while retaining selected Wang row blocks and the full compressed rank-1 projection.  Syntax checked by AST parse.

Initial near-saturated probes:

- rep 2, exact 18 rank-1, pair-through dimensions 4--8 plus rank-1 projection: CP-SAT `OPTIMAL`, support rank histogram `{1:18,2:1,3:1}`; full LUT scan found 119 violations, max excess 2.  After adding those 119 violated rows as seeds, CP-SAT again found an exact-18 support with the same rank histogram; full scan still found 106 violations, max excess 1.
- rep 16, exact 18 rank-1, pair-through dimensions 4--8 plus rank-1 projection: CP-SAT `OPTIMAL`, support rank histogram `{1:18,2:2}`; full LUT scan found 68 violations, max excess 1.  After adding those 68 violated rows as seeds, CP-SAT returned `INFEASIBLE` in about 296 seconds.  This is useful solver evidence for the rep16 exact-18 slice but is not a theorem component until reproduced as CNF/DRAT or another checkable proof object.
- rep 2, exact 17 rank-1: CP-SAT found support `{1:17,2:2,3:1}`; full scan found 474 violations, max excess 2.
- rep 16, exact 17 rank-1: CP-SAT found support `{1:17,2:1,3:2}`; full scan found 218 violations, max excess 2.
- rep 10 with pair-through dimensions 6,7,8 and rank1-count <=18 remained `UNKNOWN`; the previous large CNF/DRAT attempt for the same row block ended with CaDiCaL exit 0 after 1800 seconds and is not a proof object.

These probes suggest that the next decisive execution should split the remaining mixed branches by the first higher-rank point and convert small infeasible slices, starting with rep16 exact18 plus its 68 seed rows, into proof-producing CNFs.  Full-LUT zero-violation supports have not appeared in related analysis, so nothing has yet been available for exact fixed-A B/C solving.
