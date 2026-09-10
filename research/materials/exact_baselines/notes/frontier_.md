# frontier reconstruction for T_{<3,3,3>} exact rank

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

research: research_record. Goal: determine or materially advance exact tensor rank/bilinear complexity of 3x3 matrix multiplication by either an exact rank <=22 construction or a rigorous rank-23 optimality/lower-bound result over a stated field or algebraic structure.

This note records what was actually retrieved/read in analysis and what it currently implies for route choice. It is a working research note, not a final claim.

## Active object and evidence standards

Use the trilinear matrix-multiplication tensor convention
\[
M_{<l,m,n>} = \sum_{i,j,k} a_{ij}\otimes b_{jk}\otimes c_{ki},
\]
where a rank-r bilinear algorithm is a decomposition into r rank-one tensors. For 3x3 over a field K, the Brent equations are 729 cubic equations in 27r coefficient variables; for r=23 this is 621 base coefficient variables before Boolean/Tseitin auxiliary variables. Literature and runtime use variants with output transpose; conversions must be verified.

Strict separation:
- integer/rational/real/complex exact decompositions are upper bounds in their stated domain only after exact verification;
- a mod-p decomposition is a construction over that field; it may or may not lift;
- a mod-p nonexistence result excludes decompositions over any integral domain that reduce well modulo p, but is not automatically a characteristic-zero lower bound unless the reduction argument is fully stated;
- numerical/ALS/AlphaTensor candidates and border-rank degenerations are not exact rank algorithms;
- rank-23 addition improvements are useful structure/search evidence, not solutions to rank 22 vs 23.

## Dated frontier snapshot from sources read or retrieved

### Classical upper bound and lower bounds

- Laderman, 1976, `\cite{laderman1976noncommutative}` / `\cite{laderman1976noncommutative}` source URL via ProjectEuclid/AMS: original noncommutative rank-23 algorithm for 3x3 matrices. The retrieval preview confirms title, date, Bulletin AMS 82(1):126-128, communicated Oct. 9 1975, and purpose: noncommutative algorithm using 23 multiplications. Need fuller source reading from PDF if exact formula/provenance matters.
- Sedoglavic 2018, `Knowledge/objects/papers/Laderman-matrix-multiplication-algorithm-can-be-constructed-using-Strass--ad37af0c79dc--9779576ef7ae/object.md`, `\cite{sedoglavic2017laderman}`: gives a geometric reconstruction of Laderman from Strassen/isotropies, states no new rank bound, records Laderman tensor type and induced 2x2 subalgorithms. Useful for structural inheritance rather than a new bound.
- Bläser lower-bound lineage: retrieval found metadata for the 1999/2003 arbitrary-field `5/2 n^2 - 3n` style lower bound (`\cite{blaser1999sup}`, `\cite{blser1999lower}`, `\cite{blser1999lowera}`) and Wang's paper quotes the more small-format result `R(<n,m,n>) >= 2mn+2n-m-2` over arbitrary fields, giving `R(<3,3,3>) >= 19`. Full Bläser source still needs direct reading if we build on it.
- Landsberg 2012, `Knowledge/objects/papers/New-lower-bounds-for-the-rank-of-matrix-multiplication--fe4c79cff1ba--b50c936262b4/object.md`, `\cite{landsberg2012lower}`: complex-field asymptotic rank lower bound via border-rank equations and restriction. It improves Bläser only for large n, not for n=3; p=1 square gives weak numeric value for 3. Good conceptual source for turning border equations into rank bounds, but not close to 23.
- Landsberg--Ottaviani/Landsberg--Michalek border-rank sources (`\cite{landsberg2011lower}`, `\cite{landsberg2016geometry}` and related): for n=3, known border-rank lower bounds reach about 16/17 in later work, strictly separated from exact rank. They explain why border-rank geometry does not directly answer exact rank 22.
- Wang 2026, `Knowledge/objects/papers/Automated-Lower-Bounds-for-Small-Matrix-Multiplication-Complexity-over-F--d7e0d98ca98f--3c257f9fb1dd/object.md`, `\cite{wang2026automated}` / `\cite{wang2026complexity}`: computer-assisted finite-field lower bound `R(<3,3,3>) >= 20` over `F_2`, improving Bläser's 19 in that field. Method: classify restriction subspace orbits on first matrix, dynamic programming, flattening, forced products, degenerate reduction, and substitution/backtracking; proof certificates are verifiable. This is directly relevant because it gives a certified lower-bound framework but still far from 23.

### Search and rank-23 decomposition frontier

- Heule--Kauers--Seidl SAT/local-search 2019/2021: `Knowledge/objects/papers/Local-Search-for-Fast-Matrix-Multiplication--62e3553bd423--2f6a56f18c8c/object.md`, `\cite{heule2019local}`, and `Knowledge/objects/papers/New-ways-to-multiply-3-3-matrices--4639c02bea71--66e79e7df0e1/object.md`, `\cite{heule2019ways}`. Key facts read: Brent equations over `F_2`, SAT Tseitin encoding, type-3 term pairing, streamlining and neighborhood search. They found >13,000 inequivalent rank-23 schemes and parameterized families with dimension at least 17, but no rank-22 scheme and no exhaustive impossibility proof. The plain rank-22 Challenge 4 CNF remains an explicit benchmark.
- `matrix-challenges` repository: `Knowledge/objects/code/matrix-challenges--687bcef3570e--8594c00d57bd/object.md`, `\cite{marijnheule2019matrix}`. Challenge 4 is a plain formula for 22 multiplications over `F_2`; Challenge 1--3 concern rank-23 subproblems. This is a concrete benchmark for exact finite-field search, not a proof surface by itself.
- Palladinos SAT certificates 2026: `Knowledge/objects/code/palladin-sat-challenges--4dd5c4c398ad--888477704863/object.md`, `\cite{palladin2026palladin}` plus paper object found by grep. It provides complete satisfying assignments for all 21 top-level Challenge 1--3 CNFs and shows Challenge 2 expected-UNSAT instances were SAT as encoded; Challenge 3 has a type-3-free rank-23 scheme over F2. It explicitly does not address Challenge 4/rank 22. This matters because some earlier SAT intuitions about hard subinstances were misleading: semantic tensor transformations can satisfy constraints expected to block schemes.
- Kauers--Moosbauer flip graph 2022/2023: `Knowledge/objects/papers/Flip-Graphs-for-Matrix-Multiplication--d7db535d2ded--4964ffd10a99/object.md`, `\cite{kauers2022flip}`. Defines flips and reductions among exact schemes. Random walks frequently descend to rank 23 for 3x3 over F2 but no rank 22. Open issues: same-level connectivity, reverse reductions, multi-term replacements, reduction discovery, component symmetries. This indicates a representation route: rank-22 search may require operations beyond simple two-term flips or stronger invariants on components.
- Arai--Ichikawa--Hukushima 2024, `\cite{arai2023adaptive}`: adaptive flip graph with plus transitions and edge constraints; for 3x3 still rank 23. Useful for search dynamics rather than a result on rank 22.
- Yang 2024, `Knowledge/objects/papers/Ruling-Out-Low-rank-Matrix-Multiplication-Tensor-Decompositions-with-Sym--67780cbdf115--0a17695103fc/object.md`, `\cite{yang2024ruling}`: exact SAT over `F_2` in symmetry classes. Reported: no `<cycle,transpose>`-symmetric rank <=21, no `<cycle,phi_F>`-symmetric rank <=21, no cyclic-symmetric rank <=15; cyclic rank-16 remained very hard. This is restricted evidence only. It warns against over-weighting symmetric ansatzes, although symmetry remains useful for tractable search.
- Ballard--Ikenmeyer--Landsberg--Ryder 2018, `Knowledge/objects/papers/The-geometry-of-rank-decompositions-of-matrix-multiplication-II-3-times--46f3e0d13763--105aa912f86a/object.md`, `\cite{ballard2018geometry}`: several cyclic rank-23 decompositions, symmetry groups, equivalence/family tools. Important quote from source: rank 22 may be much rarer than border-rank 22; numerical searches may converge to border-rank decompositions with probability nearly one. This is central for route taste: do not treat lack of numerical rank-22 as strong evidence of nonexistence without understanding border-rank attraction.
- Recent addition-minimized rank-23 schemes: Perminov 58-addition (`\cite{perminov2025addition}`), Mårtensson--Wagner--Stapleton 59 (`read_path` in Knowledge), Sun 56 (`\cite{sun2026exact}`). These are rank-23 exact upper-bound improvements in additions, typically ternary coefficients and exact Brent verification, but they do not lower rank. Their search methods and compressed structures may be useful raw material.

### Border rank/geometric representation context

- Landsberg--Michalek 2016/2017, `\cite{landsberg2016geometry}`: normal-form lemma for border-rank algorithms with symmetry; border-substitution lower bound gives `underline R(M_n) >= 2n^2 - n + 1`, for n=3 around 16. It explicitly notes rank 19--23 and border rank 16--20 at that time. Valuable for understanding why lower-bound geometry is far from exact rank 23.
- Conner--Harper--Landsberg 2023, `\cite{conner2023lower}`: border apolarity gives `underline R(M_3) >= 17` over C. It also notes barriers for rank/determinantal methods. Need full reading later if a lower-bound route uses apolarity.
- Dolezalek--Michalek 2026, `\cite{dolelek2026nonlinear}`: nonlinear/Kronecker-Koszul flattenings beyond cactus barrier; not yet tested extensively on larger matrix multiplication. Possible lower-bound innovation route but would likely target border rank first and still may not reach exact rank 23.

## Runtime and local artifact state

Read `Skills/qiushi-matmul-rank22/SKILL.md`: runtime provides exact arithmetic verification, SAT/flip-graph/numerical/search corpora, and strict evidence separation. `qiushi-matmul doctor --json` returned status ok, CUDA true, native verifier true, Python 3.12.13, release `qiushi-matmul-1f-20260904.7`, upstream_count 8.

`qiushi-matmul source list` exposes pinned upstream snapshots:
- FastMatrixMultiplication @ e703f18...
- Matrix-Multiplication-Tensor-Decomposition @ 4108df9...
- alphatensor @ 1949163...
- cn122_add55 @ 34949f9...
- flip-cpd @ 9eeb17f...
- matrix-challenges @ 150b2e...
- tensor-rank-lower-bound @ d96d787...
- ternary_flip_graph @ b942f00...

`qiushi-matmul frontier` returned snapshot as of 2026-09-04: general lower/upper 19/23 and prime_2 lower/upper 20/23, with warning that it is not a substitute for fresh literature search.

`qiushi-matmul construction list` shows only `strassen-2x2-r7` and `cn122-3x3-r23`; no built-in rank-22 construction. I reproduced `cn122-3x3-r23` to `data/cn122_3x3_r23_repro/`. Runtime receipt states exact upper-bound evidence: integer domain, rank 23, both Python and native C++ checked 729 identities, failure_count 0, SHA256 `47fa58e6cd795ad6b28da0dc417251bc2efe41d1b00beca4f0f7e07c94cbe561`. Files:
- [scheme-47fa58e6cd.qmm](../results/cn122_3x3_r23_repro/scheme-47fa58e6cd.qmm)
- [receipt-5567241e82.json](../results/cn122_3x3_r23_repro/receipt-5567241e82.json)

`qiushi-matmul lower-bound verify-wang-q2-333 <certificate>` exists, indicating local verifier support for Wang's F2 lower-bound certificate. The certificate path has not yet been located or verified in this ARTIFACT.

## Why rank 22 vs 23 has resisted, as currently understood

1. Direct Brent equations are small enough to state but highly nonlinear: 729 cubic constraints with large symmetry and many auxiliary encodings; general Groebner approaches are infeasible.
2. Search spaces over `F_2` are finite but enormous. SAT/local search found many rank-23 schemes but did not make Challenge 4 tractable. Rank-23 diversity does not imply easy interpolation to rank 22.
3. Many methods exploit restrictions (ternary coefficients, symmetry, streamlining, type-3 pairing, flip reachability). Negative results in those subspaces do not settle the unrestricted problem.
4. Numerical methods are confounded by border-rank behavior. Border-rank degenerations may attract optimization runs; exact rank-22 decompositions, if they exist, may be isolated/rare or outside common coefficient restrictions.
5. Current rigorous lower-bound methods are far from 23. Classical arbitrary-field lower bound reaches 19 for 3x3; Wang reaches 20 over F2 by certificate-based substitution/orbit DP. Border-rank lower bounds around 16/17 do not directly imply exact-rank 23.
6. The symmetry group both helps and hides difficulty. De Groote/sandwich/cyclic/transpose actions generate huge equivalence classes; canonicalization is expensive and incomplete choices can create misleading subproblems (as seen in Palladinos Challenge-2 certificates).

## Serious route candidates after analysis

### Route A: finite-field lower-bound development from Wang certificate framework

Near-term: locate and verify Wang's F2 `R(<3,3,3>) >= 20` certificate with the runtime; read the verifier/source. Then understand the dynamic-programming proof object orbit-by-orbit enough to identify which orbits block a target 21, 22, or 23 lower bound. This is scientifically valuable because it is a rigorous lower-bound surface, not heuristic search.

High-value extension possibilities:
- test the framework over `F_3`/other small fields and identify whether the obstruction to >20 is method-internal or field-specific;
- search for stronger substitution rules, forced-product variants, or multi-factor restriction DP that can certify 21+ over F2;
- connect certificate failures to structural invariants of candidate low-rank decompositions.

Risk: even a strong F2 lower bound cannot alone prove characteristic-zero rank 23 unless it reaches 23 and a reduction argument covers the target domain; current bound 20 is far from 23.

### Route B: exact rank-22 search over F2/integer with semantic rather than raw CNF representation

Use matrix-challenges Challenge 4 and the SAT/local-search corpus, but avoid plain solver scaling as the main idea. Palladinos shows semantic tensor transformations and complete assignment reconstruction can solve constraints believed difficult. A valuable route is to rebuild rank-22 search at the semantic level: type-3 core distributions, de Groote orbit actions, normal forms, rank-redundancy removal, and possibly learned/proven constraints from rank-23 families.

Near-term evidence-changing actions:
- inspect Challenge 4 CNF dimensions and encoder semantics;
- implement/obtain a verifier that maps base-variable assignments to tensor residuals for rank 22;
- run small controlled probes (not long blind search) to learn which structural constraints are truly restrictive.

Risk: unrestricted rank-22 search remains enormous; negative solver time is weak evidence unless it proves a well-defined restricted space.

### Route C: structural study of rank-23 families and possible degeneration/drop mechanisms

Use exact rank-23 corpus (Laderman/Sedoglavic, Ballard cyclic decompositions, Heule families, addition-minimized ternary schemes, runtime `cn122`) to search for algebraic patterns that would be necessary for a rank drop: reducibility under flips, linear dependencies by shared factor, type/rank triples, induced 2x2 projections, tangent/null directions, and near-miss term drops.

Near-term:
- normalize several rank-23 decompositions into one `qmm`/tensor format and compute invariant summaries;
- test single-term and multi-term drops exactly to see residual structure;
- analyze whether reductions from rank 23 to 22 would force a forbidden configuration in projections or restricted subspaces.

Risk: addition-minimized rank-23 schemes may only optimize implementation cost, not approach rank-22 structure. Need avoid treating near-misses as proof.

### Route D: new lower-bound/invariant route inspired by determinant/slice or nonlinear flattenings

There are metadata-only 2026 claims (e.g. Zenodo rank-23 proof via `det(S_A)=f^3`) that must not be trusted without source/proof reading and independent checking. However, they hint at possible slice-determinant or singular-locus invariants. More reliable geometric sources (Dolezalek--Michalek nonlinear flattenings, Conner--Harper--Landsberg border apolarity) suggest exploring invariants beyond linear flattenings/cactus barriers.

Near-term:
- retrieve/read any claimed rank-23 proof package if available, but with high skepticism and exact verification;
- independently derive the slice determinant invariant for `M_3` and test it on rank-r symbolic/numeric/rand samples;
- ask whether such invariants can distinguish rank <=22 from `M_3` rather than only border/cactus varieties.

Risk: many claimed proofs of famous exact-rank results are unreliable; this route needs stringent verification and likely review/math-tool checking before investment.

## judgment

The best immediate next work is still Explore, not Execute. We now have a usable source map and a verified rank-23 baseline artifact, but not enough field depth to choose a main line. The strongest next action should combine: (i) verifying/understanding Wang's finite-field lower-bound certificate framework, because it is the newest rigorous progress directly on 3x3 rank; (ii) inspecting the rank-22 Challenge 4 semantic encoding and runtime/source surfaces, because it is the most concrete upper-bound/search benchmark; and (iii) reading full Bläser/de Groote/Heule/Ballard details as needed for exact assumptions and symmetry normal forms. A premature long raw search would likely duplicate known hard work; a premature paper/write-up would drift from the goal.
