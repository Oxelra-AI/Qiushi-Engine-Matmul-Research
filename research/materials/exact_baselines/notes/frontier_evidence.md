# frontier/evidence map for 3×3 matrix multiplication tensor rank

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Active target
Determine or materially advance the exact tensor rank / bilinear complexity of the 3×3 matrix multiplication tensor \(T_{\langle3,3,3\rangle}\): either an exact rank \(\le 22\) bilinear algorithm, or a rigorous lower-bound route that can exclude rank \(\le 22\) over an explicitly stated domain. Do not assume upper-bound or lower-bound direction in advance.

## research and runtime facts checked in this ARTIFACT

## Exact baseline artifacts produced/checked

- Reproduced installed integer rank-23 construction:
  - command: `qiushi-matmul construction reproduce cn122-3x3-r23 --output data/cn122_r23_reproduce`
  - output scheme: [scheme.qmm](../results/cn122_r23_reproduce/scheme.qmm)
  - reproduction receipt: [receipt.json](../results/cn122_r23_reproduce/receipt.json)
  - evidence: independent Python and native C++ verifiers agree; 729 Brent identities checked; rank 23; integer domain; scheme sha256 `47fa58e6cd795ad6b28da0dc417251bc2efe41d1b00beca4f0f7e07c94cbe561`.
- Re-ran verifier on the reproduced scheme after correcting the write-target mount:
  - command: `qiushi-matmul verify data/cn122_r23_reproduce/scheme.qmm --backend both --receipt data/cn122_r23_reproduce/verify_receipt.json`
  - receipt path: [verify_receipt.json](../results/cn122_r23_reproduce/verify_receipt.json)
  - result: status `verified`, evidence_status `exact_upper_bound`, both independent verifiers agree, 729 identities checked.
- Verified installed characteristic-2 lower-bound certificate:
  - command: `qiushi-matmul-env qiushi-matmul lower-bound verify-wang-q2-333 $QIUSHI_PLATFORM_ROOT/runtime/releases/qiushi-matmul-1f-20260904.7/upstream/tensor-rank-lower-bound/certs/matrix/cert_matrix_q02_n333.pb.txt`
  - certificate sha256 `25595a883ce877eecd802139ff4e07646e154b2797ad6fe7f9ec737ab0c6135d`
  - result: status `verified`, domain prime 2, claimed/proven lower bound 20. Verifier log swept constrained dimensions 9 down to 0 and concluded `UNCONSTRAINED TENSOR RANK LOWER BOUND: 20` for `matrix_q02_n333`.

## Literature/source picture grounded by actual files read

### General public status
The first source pass supports the expected frontier: exact rank of \(T_{\langle3,3,3\rangle}\) remains unresolved; rank 23 is the smallest known exact rank for general 3×3 multiplication; rank 22 is not publicly known. The best arbitrary-field/general lower bound available in the retrieved sources remains 19, while a new certified finite-field result improves the \(\mathbb F_2\) lower bound to 20.

### Exact rank-23 upper-bound landscape

- Laderman (1976) is the classical rank-23 noncommutative upper bound; actual original source still should be read/retrieved later for exact provenance, but it is repeatedly cited by all read sources.
- Courtois–Bard–Hulme `\cite{courtois2011general}` (`Knowledge/objects/papers/A-New-General-Purpose-Method-to-Multiply-3x3-Matrices-Using-Only-23-Mult--09015d6b7c56--d768596b2261/object.md`) solved Brent equations modulo 2 then lifted to a 23-product general noncommutative solution. It gives explicit product formulas and inequivalence evidence by rank-distribution invariants; it explicitly says rank 22 was still unknown.
- Ballard–Ikenmeyer–Landsberg–Ryder `\cite{ballard2018geometry}` (`Knowledge/objects/papers/The-geometry-of-rank-decompositions-of-matrix-multiplication-II-3-times--46f3e0d13763--105aa912f86a/object.md`) constructs and analyzes cyclic-symmetric rank-23 decompositions over \(\mathbb C\). Important inherited concepts: De Groote symmetry group, families/orbits of decompositions, rank triples, incidence/pairing graphs, projective point-line configurations in \(\mathbb P^2\), and caution that numerical searches may approach border-rank decompositions rather than exact rank decompositions.
- Perminov `\cite{perminov2025fast}` (`Knowledge/objects/papers/Fast-Matrix-Multiplication-via-Ternary-Meta-Flip-Graphs--220fe3ebfde7--150d6111dde1/object.md`) supplies GPU ternary/meta-flip methodology and many rank/addition improvements for other formats, but no rank-22 result for 3×3. Its distinction between ternary integer coefficients \(\{-1,0,1\}\) and \(\mathbb F_3\) is important.
- Sun `\cite{sun2026exact}` (`Knowledge/objects/papers/An-Exact-56-Addition-Rank-23-Scheme-for-General-3-3-Matrix-Multiplicatio--e2ce8fb08e72--0b482e08683f/object.md`) gives a 56-addition rank-23 algorithm derived from a 58-addition Perminov scheme by cyclic automorphism and scheduling; it does not claim rank optimality. It is useful as a clean exact rank-23 benchmark and scheduling example, not as progress on rank 22.

### Lower-bound and exact-search landscape

- Landsberg `\cite{landsberg2012lower}` (`Knowledge/objects/papers/New-lower-bounds-for-the-rank-of-matrix-multiplication--fe4c79cff1ba--b50c936262b4/object.md`) gives asymptotic complex lower bounds via border-rank equations plus polynomial restriction. For small \(n=3\), the p=1/Bläser-type bound is not close to 23. The source is still valuable conceptually because it turns border-rank equations into rank lower bounds by saving degree in restricted variables; this suggests one way a stronger proof would need a much sharper small-instance invariant.
- Yang `\cite{yang2025faster}` (`Knowledge/objects/papers/Faster-search-for-tensor-decomposition-over-finite-fields--5f0371c05c9c--d880b52d0572/object.md`) develops exact finite-field CPD search. It states \(19\le R(\langle3,3,3\rangle)\le23\), rank 22 open since 1976. Correct domain-transfer point: an integer rank-\(r\) decomposition always reduces modulo any prime to a decomposition of length at most \(r\); terms may become zero or merge, but this only shortens the expression. Thus nonexistence of rank \(\le r\) over \(\mathbb F_p\) rules out integer rank \(\le r\). It does not rule out arbitrary rational/complex decompositions with denominators or characteristic-sensitive behavior. Finite-field construction/lifting is separate. The new exact algorithms are still far from directly resolving 3×3 rank 22.
- Yang `\cite{yang2024ruling}` (`Knowledge/objects/papers/Ruling-Out-Low-rank-Matrix-Multiplication-Tensor-Decompositions-with-Sym--67780cbdf115--0a17695103fc/object.md`) uses SAT over \(\mathbb F_2\) to rule out restricted symmetry classes: no cyclic+transpose or cyclic+specific-sandwich symmetric decompositions of rank ≤21, no cyclic-symmetric rank ≤15. These are restricted-domain/symmetry results, not a rank-22 exclusion.
- Installed finite-field lower-bound runtime `tensor-rank-lower-bound` (README inspected through runtime) proves \(R_{\mathbb F_2}(\langle3,3,3\rangle)\ge20\) by a certificate-verified framework with constrained subspaces, orbit classification under a rank-preserving symmetry group, and four proof mechanisms including flattening, forced product, degenerate reduction, and backtracking. This is currently the strongest verified finite-field lower-bound artifact in the runtime.

## Important distinction of coefficient domains

- Integer/rational/real/complex rank-23 schemes establish general upper bounds if exact Brent identities hold over \(\mathbb Z\) or a suitable ring.
- A rank-22 exact scheme over \(\mathbb Z\), \(\mathbb Q\), \(\mathbb C\), or a finite field would each have different implications. A finite-field rank-22 scheme over \(\mathbb F_2\) would not automatically lift to characteristic zero; an integer rank-22 scheme would reduce modulo primes unless terms degenerate in a way requiring care.
- The verified \(\mathbb F_2\) lower bound 20 does not approach 23 yet; it only rules out rank ≤19 over \(\mathbb F_2\), but it is a real improvement over old 19 for that field and may reveal proof primitives worth rebuilding.

## Candidate high-value research routes from analysis

1. **Lower-bound framework route: strengthen finite-field constrained-subspace certificates.**
   - Why valuable: exact, certificate-checkable, already improves \(\mathbb F_2\) from 19 to 20 for 3×3; if its proof primitives can be sharpened or new constraints/orbits/invariants added, it could raise the finite-field lower bound or expose structural obstructions relevant to rank 22.
   - Near work: read the arXiv 2603.07280 paper if retrievable; audit the verifier/trust base; understand what the certificate’s constrained tensors mean; run small experiments on adjacent formats or altered symmetry groups only if they explain the bottleneck.
   - Main obstacle: a jump from 20 to 23 is huge; raw scaling of the same DP/search may not be enough. Need identify a structural bottleneck and possibly invent a stronger local rank-lower-bound primitive.

2. **Upper-bound search route: exact rank-22 search with representation-informed constraints.**
   - Why valuable: a verified rank-22 scheme would settle the main target in the upper-bound direction.
   - Inherited assets: installed continuous search command; pinned corpora with many rank-23 schemes; ternary flip/meta-flip methods; SAT/local-search literature; exact verifiers; known symmetry/orbit invariants.
   - Near work: inspect the continuous-search output format and run small pilot rank-22 searches to understand whether it is numerical candidate search, exact flip search, or something else; analyze rank-23 neighbors and invariants for terms that could collapse under flips or border degenerations.
   - Main obstacle: many previous searches failed; blind random search is unlikely to be decisive. It needs constraints or representations learned from rank-23 families, rank-lowering mechanisms, finite-field obstructions, or geometric configurations.

3. **Geometry/invariant route: use the rank-23 family structure as a map of what rank-22 would have to violate.**
   - Why valuable: Ballard et al. show rank-23 decompositions have rich projective point-line and symmetry structures. A rank-22 scheme, if it exists, may sit outside the abundant rank-23 families or require a different incidence type; if impossible, a refined invariant may prove it.
   - Near work: compute invariants for the verified cn122 scheme and known rank-23 corpora (rank triples, type polynomial, incidence/pairing graphs, support sparsity, stabilizer hints) to build a data map, then look for equations or unavoidable conditions under rank ≤22.
   - Main obstacle: invariants distinguish families but usually do not prove nonexistence. Need connect them to algebraic constraints or finite-field certificates.

4. **Hybrid route: finite-field exact search + lifting/exclusion.**
   - Why valuable: \(\mathbb F_2\) SAT and exact CPD search have found many rank-23 schemes and certify restricted impossibilities; finite-field nonexistence can rule out classes of integer decompositions by reduction.
   - Near work: inspect public corpora and runtime source lists; identify whether existing code has rank-22 partial runs, clause encodings, and solution repositories; design a low-cost pilot that measures residual structure rather than just rerunning a known infeasible search.
   - Main obstacle: finite-field rank behavior can differ from characteristic zero; F2 lower-bound 20 still leaves 20–22 open even over F2.

## Immediate next work suggested

- Read/obtain the exact paper for arXiv:2603.07280 if possible; otherwise study the runtime source/verifier and certificate format directly.
- Have review reconstruct the finite-field lower-bound certificate method for `matrix_q02_n333` at the mathematical level: what are the constrained subspaces, what rank inequalities are recursively certified, and what proof primitive is currently limiting the lower bound at 20?
- In parallel or soon after, have review inspect and run a small controlled `qiushi-matmul search continuous --rank 22` pilot (short steps, saved output) to learn the output format and whether it can produce useful residual/invariant information without overclaiming.
- Build a scriptable invariant extractor for `.qmm` and known JSON/M files: rank triples/type polynomial, sparsity, support overlaps, simple symmetry tests. Start with the verified `cn122_r23_reproduce/scheme.qmm` and known rank-23 files.

## Unresolved from analysis

- Original Laderman and Bläser 2003 exact papers should still be retrieved/read directly; current knowledge of them is partly through later sources and runtime summaries.
- The exact mathematical content of arXiv:2603.07280 has not yet been read because the first retrieval returned no object; the runtime README and certificate verification nevertheless establish a local verified \(\mathbb F_2\) lower-bound artifact.
- No rank-22 candidate, no rank-23 optimality proof, and no new lower bound were produced in analysis; this ARTIFACT only established evidence surfaces, source map, and serious routes.
