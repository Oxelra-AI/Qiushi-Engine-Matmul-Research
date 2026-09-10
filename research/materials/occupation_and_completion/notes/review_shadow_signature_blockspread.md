# review Review — analysis shadow signature and block-spread structure

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

research: research_record. Field: \(\mathbb F_2\). Object: the E11 quotient core for \(T_{\langle3,3,3\rangle}\). The full research target remains a verified rank-\(\le 22\) exact decomposition or a strict rank-\(\ge 21\) lower bound for the full \(3\times3\) matrix multiplication tensor over \(\mathbb F_2\).

## 1. Bridge status

The E11 route remains useful but must be read as implications. A rank-19 E11 core gives a full rank-\(\le 22\) algorithm by adding the deleted rank-3 \(E_{11}\) slice. In the other direction, proving E11 core rank at least 20 gives the full rank-\(\ge 21\) result only through the already replayed full rank-20 no-rank-one-A reduction and the corrected normalization to an \(E_{11}\) term. The residual-rank-\(\le1\) lift condition is the right refined obstruction for excluding full rank 20 after an exact nineteen-term core is present; it is not the same as residual zero.

The current ARTIFACT did not produce a rank-19 core, a complete exclusion of rank-19 cores, or a full-tensor theorem. It did refine the mathematical meaning and reach of two new necessary-condition mechanisms: the `min4` shadow certificate and the peer's block-spread coupling.

## 2. `min4` shadow certificate

The compact certificate is a valid row-combination contradiction for the corrected \(3\times3\) shadow system under its saturation hypotheses. `compact_shadow_certificate_verification.json` verifies 14 rows (8 tensor and 6 trace), 171 shadow variables, zero XOR of all variable coefficients, and right-hand side 1. Therefore, whenever the four guard contractions \(43,53,157,234\) are saturated at weight 9 on a tested support, the relaxed shadow equations are inconsistent for supports satisfying the derived relation. This excludes rank-one \(B/C\) completion only because it already excludes the larger relaxed matrix problem.

The certificate has extra algebraic structure. The trace inverse masks in `target_certificate.json` are
\[
h_{43}=212,\quad h_{53}=396,\quad h_{157}=271,\quad h_{234}=87,
\]
and their XOR is zero. The only nonzero tensor coefficient masks are in slices 0 and 3, both equal to \(396=h_{53}\). Thus the tensor contribution for a direction \(p\) is
\[
F(p)=\langle p,9\rangle h_{53},
\]
where the pairing is bit parity over \(\mathbb F_2\). The whole guarded parity relation depends only on the five incidence bits
\[
\phi(p)=(\langle p,9\rangle,\langle p,43\rangle,\langle p,53\rangle,\langle p,157\rangle,\langle p,234\rangle)\in\mathbb F_2^5.
\]
The five masks have rank 5, so \(\phi\) is onto: the zero-signature class has 7 nonzero directions and the other 31 classes have 8 directions each.

The signature classes are uniform for this certificate. `signature_count_relaxation.json` records 16 forced-zero classes, 9 forced-one classes, and 7 free classes. The forced-one signatures are
\[
5,7,13,15,21,23,27,29,31,
\]
and the free signatures are
\[
1,3,9,11,17,19,25.
\]
Under the four weight-9 guards and with no selected point in a free class, a valid core support must have odd total count in the forced-one classes. The source analysis support has even such parity and is therefore excluded by the certificate.

A data-status correction is needed when reading `target_certificate.json`: two applications with unsaturated guards are marked `pure_parity_applicable: true` and `pure_parity_contradiction: true`. The certificate relation should be regarded as applicable only when `guard_saturated` is true. The compact verifier and the analysis count model use the guard condition correctly; the misleading fields are application metadata, not a defect in the row-combination certificate.

## 3. Five-bit signature count relaxation

`signature_count_relaxation.py` compresses the 255 direction variables to 32 integer signature-class counts. I initially had to repair the subspace-preimage computation to include the zero signature vector when forming \(\phi^{-1}(W)\); the current saved JSON is after that repair. The 374 subspaces of \(\mathbb F_2^5\) give 374 Wang rows whose direction sets are complete unions of signature fibers; 373 are nontrivial after the total size is fixed. Their lower-bound distribution in the saved file is
\[
L=0:1,\ 3:2,\ 6:24,\ 9:84,\ 11:4,\ 12:162,\ 13:20,\ 14:45,\ 15:29,\ 16:3.
\]

The count model remains feasible even with all signature-preimage Wang rows and the excluded-family parity condition. For `min_L` values 0, 12, 13, 14, and 15, the solver recorded 50 feasible count vectors within the collection cap. Hence the signature-preimage rows do not by themselves subsume the shadow parity relation. Survival of the count model is only a relaxation result: it gives possible incidence histograms, not actual supports in \(\mathbb F_2^8\), not complete Wang compatibility, and not rank-one \(B/C\) factors.

The analysis source support illustrates exactly where the relaxation loses information. It violates no signature-preimage Wang row, but it violates 9 complete Wang rows, all with \(L=12\), capacity 7, and occupancy 8. `signature_violation_structure.json` shows these 9 rows are 5- or 6-dimensional subspaces that cut inside signature fibers. Enlarging each row to the full preimage of its signature image changes the relevant row to a larger 6- or 7-dimensional subspace with capacities 10, 13, or 16; the source occupancy in those enlarged rows is then allowed. Thus complete occupation is using intra-fiber geometry that the five-bit abstraction intentionally forgets.

I also tested whether selected feasible count vectors can be realized by actual distinct A-directions satisfying the complete E11 Wang table. The source signature counts are infeasible when rows with \(L\ge12\) are included, but feasible under only \(L\ge15\), where the solver recovers the original analysis support and the complete rescan again shows the same 9 missing \(L=12\) violations. Fifteen sampled feasible count vectors from the count model were each infeasible under all complete Wang rows in `batch_disaggregate_selected.json`. These computations show that many count-level solutions are artifacts of forgotten intra-fiber constraints. They do not prove that every count-level solution is unrealizable, nor do they settle whether there is a complete-Wang-compatible actual support excluded by `min4`.

The actual 255-direction family search from analysis (`family_min4_L12_300s.json`) remains `UNKNOWN`. That is still the unresolved separation question for this particular shadow certificate: either find a complete-Wang-compatible actual A-support satisfying the `min4` excluded family, or prove that complete Wang already forbids the family. Any formal use would need a proof-producing encoding or independently replayable certificate; CP-SAT infeasibility alone would not be enough for the final theorem.

One further scope point: the disaggregation scripts use Boolean direction variables, hence distinct projected A-directions. This is appropriate only after invoking the replayed repeated-projected-A exclusion for the E11 rank-19 branch. It is not a stand-alone treatment of arbitrary multisets.

## 4. Independent block-spread review of research_record analysis

I independently rebuilt the E11 core convention reported by research_record. The correct full tensor convention is
\[
T[3i+j,\ 3j+k,\ 3i+k]=1.
\]
After deleting the \(E_{11}\) A-slice, core slice \(s\) with \(a=s+1=3i+j\) occupies block
\[
R_j\times C_i,
\]
where both row and column groups use the same contiguous masks \([7,56,448]\). The independent script [independent_block_spread_review.py](../code/independent_block_spread_review.py) confirms all eight core slices and confirms that every contraction is \(M_\lambda=\Lambda^T\otimes I_3\).

The same script checked the shared 519-row rank-21 E11 pool at `data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy`. It spot-checked Brent reconstruction on 25/25 rows and then independently verified all 519 rows against the block-spread consequences. The saved result is [independent_block_spread_review.json](../results/block_spread/independent_block_spread_review.json). It agrees with the peer numbers: every row passes; the capacity-3 slice count distribution is 309 rows with 0, 183 rows with 1, and 27 rows with 2; the minimum total A-weight in the pool is 39; term block-spread sizes occur only in \(\{1,2,3,4,6,9\}\).

The purity lemma is mathematically sound as a necessary consequence of an exact decomposition. If slice \(s\) has exactly three active terms, the own block is a sum of three rank-one \(3\times3\) matrices equal to \(I_3\). Therefore the restricted \(v\)-vectors and \(w\)-vectors are both bases. The zero equations on the off-blocks then force every active term's \(v\) to be supported only in the slice row group and every active term's \(w\) only in the slice column group. This also prevents any nonzero term from serving two distinct capacity-3 slices. For a hypothetical rank-19 core with \(p\) capacity-3 slices, the pure terms from those slices cannot help the own-block rank requirement of any remaining slice; if \(p\ge6\), too few non-pure terms remain to give three own-block hitters for each remaining slice. Hence \(p\le5\), and the total A-weight lower bound becomes
\[
3p+4(8-p)=32-p\ge27.
\]

The block-spread conditions R1 and R2 are real A\(\leftrightarrow\)B/C coupling: R1 says every slice must have at least three active own-block hitters, and R2 says no off-block can be hit by exactly one active term of a slice. They are necessary consequences of the Brent equations. They are not sufficient for a rank-19 core, and the peer's augmented CNF would still need proof-producing verification of both the encoding and any resulting UNSAT object before it could support a lower-bound theorem.

## 5. Research implications

The shadow-signature analysis and the block-spread analysis point to complementary roles. The `min4` certificate is a small, exact, guard-dependent linear obstruction. Its five-bit compression exposes how inverse-mask dependence interacts with A-occupation, but the current evidence shows that complete Wang uses intra-fiber subspaces invisible to that compression. The block-spread lemmas operate later in the pipeline, after actual \(B/C\) support variables are present, and supply direct coupling not present in A-only support rows.

The strongest next work is not more unconstrained CP-SAT time on the same abstraction. The next construction should work at the actual direction level and then move quickly to \(B/C\) completion:

1. Build a proof-producing or independently replayable actual-direction model for the `min4` family with all complete Wang rows and distinct projected directions. A feasible support would demonstrate a complete-Wang-compatible support that the shadow certificate excludes; an infeasibility certificate would show this four-guard family is already absorbed by complete Wang.
2. In parallel, stream or branch actual complete-Wang-compatible supports that pass all saturated-shadow tests into a \(B/C\) completion layer using block-spread. Capacity-3 slices should be handled by the GL\(_3(\mathbb F_2)\) closed-form completion; the remaining terms should be solved against the 648 exact core equations.
3. Any SAT witness must be verified directly as an exact core decomposition and then lifted by adding the deleted slice to give a full rank-\(\le22\) decomposition. Any UNSAT result intended for rank-\(\ge21\) must include a replayable proof and the bridge components: no-rank-one full rank-20 reduction, E11 normalization, repeated-projected-A exclusion, and the correct residual-lift distinction.
