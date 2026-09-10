# review: how the E11 core controls the next full-tensor lower-bound ARTIFACT

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Strict mathematical bridge

Work over \(\mathbb F_2\).  Suppose a length-20 decomposition of the full matrix-multiplication tensor exists:
\[
T_{\langle3,3,3\rangle}=\sum_{i=1}^{20} a_i\otimes b_i\otimes c_i .
\]
The existing proof-producing Wang-occupation branches exclude every length-20 A-support with no rank-one \(a_i\).  Hence any such decomposition has at least one rank-one A-factor.

The standard left/right action on the A matrix slot, with the corresponding preserving action on the full matrix-multiplication tensor, is transitive on nonzero rank-one \(3\times3\) matrices over \(\mathbb F_2\).  After applying such an automorphism, take one rank-one A-factor to be \(E_{11}\).  Project the A slot to
\[
\mathbb F_2^9/\langle E_{11}\rangle.
\]
The selected term vanishes.  The quotient of \(T\) is the E11 core.  The T-level one-dimensional Wang row has lower bound 19 for every nonzero A-direction, so a length-20 full decomposition cannot contain a second \(E_{11}\) term.  Therefore the quotient decomposition has exactly 19 nonzero projected A-factors.  If any projected direction repeats, it is in the repeated projected-A branch of the E11 core; analysis now has a DRAT-verified occupation certificate excluding that branch.  Thus every still-possible quotient of a rank-20 full decomposition would be a length-19 E11-core decomposition with 19 distinct projected A-directions.

Consequently, a rigorous exclusion of the remaining distinct length-19 E11-core branch would exclude all full length-20 decompositions and prove
\[
R_{\mathbb F_2}(T_{\langle3,3,3\rangle})\ge 21.
\]
The old adjacent-pair/matching full-support tree would then become an alternative finite-field proof route rather than an additional logical dependency for the \(\ge21\) ARTIFACT.

Conversely, an exact rank-19 E11-core decomposition over \(\mathbb F_2\) would lift to a full rank-\(\le 22\) decomposition by adding the deleted \(E_{11}\)-slice, whose \(B\otimes C\) matrix rank is 3 in the existing restricted-core records.  This is why the E11 core is now a two-sided decisive interface: it can either produce a finite-field rank-22 candidate or, if excluded, advance the full lower bound to 21 over \(\mathbb F_2\).

## Reviewed status of analysis certificate

Independent review file: [repeated_certificate_review.json](../../finite_certification/results/review/repeated_certificate_review.json).

The analysis repeated projected-A result is accepted as a settled reduction for subsequent work.  The reviewed primary certificate is the small fixed-\(p=1\) Wang-only CNF/DRAT object:

- CNF: `workspace/data/repeat_branch_certificate/iis_shrink_p1/fixed_repeat_p1_iis.cnf`
- CNF SHA256: `673426778d1c211ac35b014a3c1baa6f2b0595a2c242f948074d580816234dc9`
- DRAT: `workspace/data/repeat_branch_certificate/iis_shrink_p1/drat/fixed_repeat_p1_iis.drat`
- DRAT SHA256: `3f9c1a06cb4eb5f0e2193e9a5be752a708945eb9ae6bfafa9490a14aeb52b419`
- `drat-trim` log: `s VERIFIED`, CNF header 24895 variables and 53255 clauses.

The small formula uses total length, tokenized one-dimensional capacities, fixed two copies of the representative projected direction \(p=1\) (label \(E_{12}\)), and 262 selected Wang occupation rows.  It does not use contraction lower bounds or quotient-rank cuts.  Deterministic re-encoding reproduces the CNF hash.  The induced E11 quotient stabilizer has one orbit on the six capacity-two projected directions
\[
[1,2,3,4,32,36],
\]
and the transport check verifies that all 262 selected rows preserve their Wang lower-bound values under all 1152 induced stabilizer permutations.  The internal `exists=false` entry for the status JSON itself is only a file-info snapshot written before the status file existed; the actual status file exists and was read.

## What must not be inferred

This certificate does not prove the E11 core has rank at least 20, does not prove \(R_{\mathbb F_2}(T)\ge21\), does not construct a rank-22 algorithm, and says nothing by itself about characteristic-zero rank 23 optimality.  It only removes repeated projected A-directions from any hypothetical length-19 E11-core decomposition over \(\mathbb F_2\).

The fact that the compact contradiction is Wang-only also means the quotient-rank framework should be preserved as a useful mechanism, but not credited for this specific proof.  Its remaining value should be tested on the distinct branch, where complete Wang occupation may or may not already be inconsistent.

## Current priority after this review

The best next work is the distinct projected-A E11-core branch, with two possible outcomes:

1. prove no distinct 19-point A-support satisfies the complete core Wang table (or produce a proof-backed reduced subsystem implying that), which together with the no-rank-one full-tensor certificates would prove \(R_{\mathbb F_2}(T)\ge21\);
2. find a complete-Wang-admissible distinct support and immediately run fixed-A domain, transversality, quotient-rank, and exact rank-one \(B/C\) completion.  Only an exact reconstruction of the core tensor would be a construction path to full rank \(\le22\).

Solver `UNKNOWN`, timeouts, or low-violation supports should remain search evidence only.  A support with any complete-Wang violation is not an admissible core support, no matter how clean it looks under B/C tests.

## Addendum after review verification and distinct-branch runs

review independently checked the bridge and found the implication sound when stated over \(\mathbb F_2\) with quotient tensor language.  The clean way to pass from rank \(\le20\) to the exact length handled by the CNFs is: take a shortest decomposition of length \(s\le20\); one-dimensional Wang rows give \(s\ge20\), so \(s=20\).  Thus the length-20 support certificates are sufficient for excluding rank at most 20.

The same review reading emphasized a more refined full-rank-20 target.  A length-19 core decomposition with distinct projected A-directions may still fail to lift to a full rank-20 decomposition.  In a fixed complement write
\[
T=E_{11}\otimes M_0+T_{\rm rest},\qquad M_0=\sum_{k=1}^3E_{1k}\otimes E_{k1}.
\]
A rank-20 full decomposition through this core would require, for some choice of lift bits \(\epsilon_i\),
\[
\operatorname{rank}\left(M_0+\sum_{i:\epsilon_i=1} b_i c_i^T\right)\le1.
\]
Therefore an exact lower-bound route can either exclude every distinct rank-19 E11-core decomposition, or more directly exclude every exact distinct core completion satisfying this residual rank-\(\le1\) lift condition.  Conversely, any exact rank-19 core decomposition still gives a full rank-\(\le22\) decomposition by adding three rank-one terms for \(M_0\).

The directly requested table check from review was performed: the T-level row \(L_T(\langle E_{11},E_{12}\rangle)\) equals 17, so in the E11 quotient at length 19 the point corresponding to \(E_{12}\) has capacity two.  analysis is therefore not redundant; it is the certificate that removes these six capacity-two repeated projected directions.

The delivered analysis background computations were read.  The pure complete E11-core CP-SAT model with 417,198 Wang rows plus 255 contraction lower bounds returned `UNKNOWN` after 1801.9 s ([complete_core_cpsat_pure_1800.json](../../finite_certification/results/repeat_branch_certificate/complete_core_cpsat_pure_1800.json)).  The distinct-only complete model with 417,197 Wang rows plus 255 contraction lower bounds returned `UNKNOWN` after 1202.1 s ([complete_core_distinct_cpsat_1200_v2.json](../../finite_certification/results/repeat_branch_certificate/complete_core_distinct_cpsat_1200_v2.json)).  These runs do not settle the distinct branch.

A high-L row experiment explored the distinct branch after the repeated-direction reduction.  With all rows of lower bound \(L\ge17\) and contraction lower bounds, CP-SAT quickly found distinct supports; the best reproduced the analysis 15-violation support.  With all rows of lower bound \(L\ge15\), CP-SAT found a new distinct support
\[
[1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]
\]
with 12 complete Wang violations, all of type \(L=12\), zero zero-domain terms, linear membership pass, no reported transversality failure, and no tested size-2 quotient-rank violation ([threshold_L15_300s.json](../results/distinct_line_cover/threshold_L15_300s.json)).  A run with all rows of lower bound \(L\ge14\) returned `UNKNOWN` after 361.4 s (`threshold_L14_360s.json`).  The scientific reading is that the remaining search surface is now pushed into lower-L rows, not that the support is admissible: any complete-Wang violation still forbids the support as an exact core decomposition.
