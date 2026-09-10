# S-level coset obstruction for the orbit-445 quotient-lift route

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

The active problem remains the exact rank of the 3x3 matrix multiplication tensor.  The current finite-field E11 work is an intermediate route: an E11 rank-19 decomposition over F2 would lift by the verified +3 elementary slice relation to a full F2 rank-22 decomposition of T333.  The analysis quotient-lift work showed that the minimal contraction cover no longer selects a small set of V-orbits, so this ARTIFACT moved from individual quotient CPD schemes to the matrix subspace
\[
S=\langle b_j\otimes c_j\rangle\subset B\otimes C
\]
that they generate.

## Collapsing the orbit-445 rank-11 quotient pool to S

For V represented by prefix `[1,2,8,64]`, flip-cpd found 542 verified quotient decompositions of rank 11 for the quotient tensor.  The new script

- [e11_s_orbit_collapse.py](../../quotient_cores/code/e11_s_orbit_collapse.py)

extracts S from each quotient scheme and acts on S by the E11 quotient stabilizer that preserves V.  The result is in

- [orbit445_rank11_s_orbits.json](../../quotient_cores/results/s_orbits/orbit445_rank11_s_orbits.json)
- [orbit445_rank11_s_bases.npz](../../quotient_cores/arrays/s_orbits/orbit445_rank11_s_bases.npz)

Main numbers:

- V-stabilizer size: 96.
- All 542 quotient schemes have dim S = 11.
- The 542 schemes give 542 distinct S spaces.
- Within the sampled pool there are 539 observed S-orbits: 536 singleton observed orbits and 3 two-member observed orbits.

Thus the analysis 6504 scheme/cover UNSATs were not repeated tests of a small family of S spaces.  They sampled hundreds of distinct matrix subspaces.

## Exact S-only coset test

For fixed V and S, the quotient-A data and term ordering disappear.  The relevant question is whether
\[
R_V + V\otimes S
\]
contains an F2 tensor of rank at most s, where s = 19 - q.  For orbit 445, q = 11 and s = 8.  I built

- [e11_s_coset_rank_sat.py](../code/e11_s_coset_rank_sat.py)

which computes the S-level contraction profile, enumerates all residual A-vector multisets satisfying the contraction lower bounds, and runs the fixed-A native-XOR SAT instance for each multiset.

A positive regression was also built:

- [e11_s_coset_positive_regression.py](../code/e11_s_coset_positive_regression.py)
- [positive_regression.json](../results/s_coset/positive_regression.json)

It uses the known E11 rank-21 decomposition from analysis.  There S has dimension 17, the known residual A-assignment `[1,2,4,8]` is the unique valid cover at residual rank 4, and the S-only SAT instance returns SAT in about 0.01 s.  This checks that the S-level encoding can find a real intersection when one is present.

For the orbit-445 rank-11 pool:

- `data/s_coset/orbit445_rank11_allS.json`

Main numbers:

- distinct S tested: 542 / 542 from the pool;
- m-profile is identical for all 542 spaces:
  \[(3,3,3,3,3,6,3,3,3,6,3,3,3,6,3);\]
- every S has exactly 12 valid residual A-vector multisets;
- all 542 x 12 S/cover instances are UNSAT;
- encoding size is 836 variables and 324 native XOR equations per cover.

This proves that none of the sampled S spaces from the rank-11 quotient pool has `R_V + V tensor S` meeting rank at most 8 over F2.  It is stronger than the analysis scheme-level exclusion because it no longer depends on a particular quotient A-part or lift correction matrix.

## Algebraic explanation: tight contraction row/column-space obstruction

The SAT exclusions are explained by a direct matrix-rank argument.  For each nonzero phi in V*, compute
\[
m_\phi(S)=\min_{M\in R_\phi+S}\operatorname{rank} M.
\]
If a residual rank-s decomposition uses A-vectors a_t and a contraction phi is tight, meaning exactly m_phi(S) of the a_t satisfy phi(a_t)=1, then the phi-contracted matrix is expressed as exactly its rank many rank-one matrices.  Therefore every participating rank-one term b_t c_t must have b_t in the column space and c_t in the row space of some minimum-rank matrix in the coset R_phi+S.  If a residual term participates in several tight contractions, its b_t and c_t must lie in the intersections of those allowed spaces.

Scripts:

- [e11_s_tight_space_obstruction.py](../../quotient_cores/code/e11_s_tight_space_obstruction.py)
- [e11_s_tight_space_scan.py](../../quotient_cores/code/e11_s_tight_space_scan.py)

For S index 0, cover `[2,2,3,4,5,8,9,12]`, the tight contractions are `[1,2,4,6,8,10,13]`.  Six of the eight residual A-terms have empty row- or column-space intersections; for example the term with A-vector 3 participates in tight contractions `[1,2,6,10,13]` and has no allowed b or c vector.  This gives a readable reason for UNSAT.

The full scan

- [orbit445_rank11_allS_tight_space_scan.json](../../quotient_cores/results/s_tight_obstruction/orbit445_rank11_allS_tight_space_scan.json)

found:

- all 542 sampled S spaces have all 12 covers blocked by this tight row/column-space argument;
- no surviving S/cover pair was found in the rank-11 quotient pool;
- runtime about 52 s.

This is the first obstruction in the quotient-lift line that depends only on V and S rather than on individual quotient schemes.

## Random S controls

To test whether the obstruction is only a flip-cpd artifact, I sampled random 11-dimensional S spaces containing the fixed quotient slice space S_min for V = `[1,2,8,64]`.

Files:

- [e11_s_random_tight_space_scan.py](../../quotient_cores/code/e11_s_random_tight_space_scan.py)
- [orbit445_random_dim11_tight_space_scan100.json](../../quotient_cores/results/s_random_controls/orbit445_random_dim11_tight_space_scan100.json)

Across 100 random S spaces:

- all 100 had every valid cover blocked by the same tight row/column-space argument;
- valid cover counts were 12 in 78 samples, 44 in 18 samples, and 116 in 4 samples;
- no random S produced a surviving cover.

A separate small exact SAT control over random S spaces with 12 covers tested 5 random S spaces and found all covers UNSAT.  The longer cover-44 SAT run produced only UNSAT/UNKNOWN before timeout, so the tight-space calculation is currently the useful fast test.

## Present interpretation

The orbit-445 quotient-lift subroute has moved from local scheme negatives to S-level algebraic structure:

1.  The sampled rank-11 quotient pool contains 542 distinct dim-11 S spaces and almost no sampled symmetry duplication.
2.  The S-only coset test excludes every sampled S exactly.
3.  The exclusions are explained by tight contraction row/column-space intersections, not by the earlier contraction cover alone.
4.  Random S controls suggest the obstruction may hold for much more than the sampled quotient-generated S spaces, but no exhaustive proof over all dim-11 S containing S_min has been obtained.

This does not prove E11 rank >= 20 and does not settle T333 rank.  It does, however, give a concrete mathematical object for the next ARTIFACT: prove or refute, for V = `[1,2,8,64]`, that every dim-11 S containing the quotient slice space and satisfying quotient rank-one generation is blocked by the tight contraction row/column-space argument.  If that cannot be turned into orbit-level coverage, the principal effort should move toward related analysis's full-tensor finite-field branch composition and a renewed characteristic-zero projective pairing-incidence formulation.

## related analysis full-T finite-field branch update checked during this ARTIFACT

After the S-level work, related analysis reported a no-fixed rank-1 projected DRAT proof for the full T-level Wang branch.  I hash-checked the files at

- `data/wang_capacity_rank1_count_cnf/nofixed_retry/rank1_count_ge19_nofixed_size_le09.cnf`
- `data/wang_capacity_rank1_count_cnf/nofixed_retry/rank1_count_ge19_nofixed_size_le09.drat`
- `data/wang_capacity_rank1_count_cnf/nofixed_retry/rank1_count_ge19_nofixed_size_le09.drat_trim.log`

The independent check confirmed the following file identities:

- CNF `90d2f0559d1219bbb5437d704518ce23900e9b587324f60990682d3bd977ebe5`
- DRAT `46a7e94d4456eaffd2e3c123681069bbcfb02ebe571915a315c908048702cf82`
- trim log `2f1e5cf3834a651fbe0fb1ff8c126378bd2c22502d89281770f866c3345687b9`

The trim log states `s VERIFIED` after 102,280,380 resolution steps.  Together with related analysis's earlier rank-2/no-rank1 branch proof and rank-1-count work, this pushes the remaining full-T F2 Wang branch into mixed supports with at least two rank-2/3 A-points.  It still does not produce a full-LUT admissible E11 support, an E11 rank-19 witness, or a characteristic-zero result.
