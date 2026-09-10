# theorem-chain review for the rank-20 exclusion

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Result of this review

I reviewed the shortened saturated lower-bound route as a proof of the exact tensor-rank statement
\[
R_{\mathbb F_2}(T_{\langle3,3,3\rangle})\ge 21.
\]
The proof is about exact decompositions over \(\mathbb F_2\), with the three tensor slots identified with \(3\times3\) matrices over \(\mathbb F_2\). I found no concrete mathematical failure in the chain after the analysis repairs. The route is now ready to be written in Express as a theorem with an accompanying reproducible proof package, not as another search result.

The independent actions in this review were:

1. Reread the main proof note [short_saturated_lower_bound_route.md](short_saturated_lower_bound_route.md) and the analysis manifests tying the finite work to the proof.
2. Reran Wang certificate verification:
   `qiushi-matmul lower-bound verify-wang-q2-333 data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt`.
   It returned `status=verified`, prime 2, lower bound 20, certificate SHA256 `25595a883ce877eecd802139ff4e07646e154b2797ad6fe7f9ec737ab0c6135d`.
3. Reran the companion tensor-action verifier. The output [companion_tensor_action_check.json](../../quotient_cores/results/tensor_action/companion_tensor_action_check.json) has `all_ok=true` over all 56,448 GL/transpose A-actions and zero failures for both the Wang source convention and this investigation proof convention.
4. Reran the quotient occupation semantics verifier. The output [quotient_occupation_semantics.json](../../quotient_cores/results/quotient_semantics/quotient_occupation_semantics.json) has `all_ok=true` for 18,704 proof-used A-subspaces and verifies \(q_U(a)=0\) exactly when \(a\in U\).
5. Reran the certificate-anchored transport layer to a analysis output: [certificate_anchored_transport_rerun.json](../../finite_certification/results/theorem_review/certificate_anchored_transport_rerun.json). It has `all_anchor_checks_ok=true`; 18,011 dim-2 source rows, 511 line instances, and 1,302 affine-plane instances all have zero anchor failures.
6. Independently replayed the peer research_record bundle checker with CNF regeneration and DRAT replay, saving [peer_bundle_check_regenerate.json](../../finite_certification/results/peer_replay/peer_bundle_check_regenerate.json). It has `all_ok=true`, regenerates the eight peer CNFs byte-for-byte, and reruns `drat-trim` successfully for all eight proofs.
7. Asked review for an external-style theorem-chain reading. The integrated result `independent-verification-record` found no concrete gap invalidating the theorem and emphasized two points that final writing must state explicitly: the exact-total-18 CNF is used together with Wang's existing lower bound 18, and every Wang lower bound used must remain tied to the verified certificate and its verifier.

## Mathematical chain after review

Assume a length-20 exact decomposition
\[
T=\sum_{t=1}^{20}A_t\otimes B_t\otimes C_t
\]
over \(\mathbb F_2\), with nonzero simple terms. Wang's verified lower bound already rules out shorter decompositions, so the length-20 case is the only possible rank-20 endpoint.

The A-split flattening \(P=\Phi_A(T)\) is a \(27\times27\) permutation matrix. For each nonzero simple term, \(\operatorname{rank}\Phi_A(A_t\otimes B_t\otimes C_t)=\operatorname{rank}A_t\). Therefore
\[
27\le \sum_t \operatorname{rank}A_t,
\qquad
\sum_t(\operatorname{rank}A_t-1)\ge 7.
\]
At least four A-factors have matrix rank at least two.

For every nonzero A-line, Wang's certificate gives lower bound 19 for the A-slot quotient. The analysis anchored transport file connects the three certificate line nodes to all 511 nonzero lines by explicit tensor symmetries. Thus no A-direction can occur twice in a length-20 decomposition.

For two high-rank A-factors \(a,b\), if \(a+b\) also has rank at least two, then the two-dimensional span \(\langle a,b\rangle\) is one of the eight all-high dim-2 orbits 484--491. The analysis forbidden-pair endpoint directly expands the eight decoded certificate representatives and reports that all 96,054 high-rank pairs with non-rank-one sum, representing 32,018 distinct two-dimensional subspaces, lie in those eight direct images, with no missing case. For each of the eight representatives, Wang gives raw lower bound 18 and the exact-total-18 occupation system is DRAT-refuted. The transparent unary CNF files in research_record all have CaDiCaL UNSAT and `drat-trim` verification, and `batch_transparent_lifting_verifier_manifest.json` verifies clause-by-clause reconstruction and forward lifting for all eight actual DIMACS files. The peer research_record bundle supplies a second encoding and was replayed in this ARTIFACT with `all_ok=true`.

The exact-total-18 use is sound as follows. If quotienting a length-20 decomposition by such a two-dimensional \(W\) kills two or more terms and leaves fewer than 18 terms, this contradicts the original Wang lower bound 18 for \(T/W\). If it leaves exactly 18 terms, their quotient A-directions form a nonnegative integer occupation vector of total 18 satisfying every inherited Wang row; the transparent CNF has the forward lifting property for exactly these integer vectors, but DRAT verifies the CNF is unsatisfiable. Hence those eight dim-2 quotients have lower bound at least 19 for the purpose needed here.

It follows that every pair of high-rank A-factors has rank-one difference. Fixing one high-rank point \(p\), the differences \(a+p\) are nonzero rank-one matrices and pairwise sums remain rank one. The elementary rank-one sum lemma forces all these differences to share a common left vector or a common right vector, so all high-rank factors lie in one affine row- or column-type rank-one coset. The row-type case is covered by the transpose tensor automorphism, and analysis verifies the companion transformations in both C-index conventions.

Inside such an affine coset, if the fixed lower block has rank at most one then the total high-rank excess is at most six, contradicting the split-flattening excess bound. Hence the lower block has rank two, giving four rank-two and four rank-three coset points. The relevant affine planes in the coset have Wang lower bound 17; analysis anchors 651 column-model and 651 row-model instances to certificate nodes of lower bound 17. Every five-point subset of \(AG(3,2)\) contains an affine plane, so at most four high-rank factors can occur. The split-flattening excess gives at least four, hence exactly four. The four rank-three points themselves form an affine plane, so at most three of the four are rank three; the rank-sum inequality then forces exactly three rank-three and one rank-two high factors. Thus
\[
\sum_t\operatorname{rank}A_t=16+2+3+3+3=27,
\]
so the A-split rank inequality is saturated.

In the saturated case, writing \(F_t=\Phi_A(A_t\otimes B_t\otimes C_t)\) and \(P=\sum_tF_t\), rank factorizations of the \(F_t\) concatenate to square invertible matrices, giving
\[
F_tP^{-1}F_s=\delta_{ts}F_t.
\]
The product formula
\[
F(A,B,C)P^{-1}F(A',B',C')=F(A(B'C^T)A',B,C')
\]
is proved by indices in the analysis note and verified on all \(729^2\) elementary pairs in [product_formula_full_elementary_matrix_check.json](../../quotient_cores/results/structural/product_formula_full_elementary_matrix_check.json). Since \(B_t,C_t\ne0\), the equality \(F(M,B_t,C_t)=0\) forces \(M=0\). For an invertible \(A_t\), the diagonal identity yields \(B_tC_t^T=A_t^{-1}\), so \(B_t\) and \(C_t\) are invertible. If two A-factors were invertible, the off-diagonal identity would give a zero product of invertible \(3\times3\) matrices, impossible. A saturated decomposition therefore has at most one invertible A-factor, while the forced profile has three. This contradiction excludes length 20.

## Files that should accompany final expression

The final Express work should present a compact mathematical proof and include the reproducible proof package paths:

- Wang certificate and replay: `data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt`, SHA256 `25595a883ce877eecd802139ff4e07646e154b2797ad6fe7f9ec737ab0c6135d`, and the successful verifier command output from this ARTIFACT.
- research_record transparent dim-2 exclusions and lifting: [batch_transparent_unary_dim2_certs_manifest.json](../../finite_certification/results/transparent_unary_certs_484_491/batch_transparent_unary_dim2_certs_manifest.json) and [batch_transparent_lifting_verifier_manifest.json](../../quotient_cores/results/transparent_lifting_batch/batch_transparent_lifting_verifier_manifest.json).
- Certificate anchoring and transport: [certificate_anchored_transport_rerun.json](../../finite_certification/results/theorem_review/certificate_anchored_transport_rerun.json) together with `data/theorem_review/dim2_core_row_anchored_witnesses.jsonl`.
- Tensor-action and quotient semantics: [companion_tensor_action_check.json](../../quotient_cores/results/tensor_action/companion_tensor_action_check.json) and [quotient_occupation_semantics.json](../../quotient_cores/results/quotient_semantics/quotient_occupation_semantics.json).
- Product formula and coset arithmetic: [product_formula_full_elementary_matrix_check.json](../../quotient_cores/results/structural/product_formula_full_elementary_matrix_check.json), [short_saturation_checks.json](../results/structural/short_saturation_checks.json), and [coset_plane_verify.json](../results/coset/coset_plane_verify.json).
- Independent peer reproduction replayed in this ARTIFACT: [peer_bundle_check_regenerate.json](../../finite_certification/results/peer_replay/peer_bundle_check_regenerate.json), derived from research_record's `data/bundle_check/bundle_check_regenerate.json`.

The next ARTIFACT should move to Express and write the theorem and proof in a form that a reader can follow without relying on internal research history. It should state the machine-verified components as exact finite lemmas with paths, hashes, verifier commands, and the mathematical meaning of each file. It should not reopen generic rank-22 search unless Express exposes a concrete failure in this proof chain.
