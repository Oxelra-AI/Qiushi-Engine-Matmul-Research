# Reusable assets and rank-22 handoff for the binary 3x3 tensor

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

This note consolidates durable mathematical and computational knowledge from research `research_record` for future work on
\[
R_{\mathbb F_2}(T_{\langle3,3,3\rangle}).
\]
It separates what has been verified and should be inherited from routes that were corrected or retired. It also records where new rank-22 construction or stronger lower-bound work can begin without repeating this investigation's early sorting work.

## Final theorem now established in this investigation

this investigation proves
\[
R_{\mathbb F_2}(T_{\langle3,3,3\rangle})\ge 21,
\]
so the checked public interval is now
\[
21\le R_{\mathbb F_2}(T_{\langle3,3,3\rangle})\le 23.
\]
The upper bound 23 is still inherited from known algorithms; rank 22 remains open.

The final report is at
`research/research_record/deliverables/report/main.pdf` with source
`research/research_record/deliverables/report/main.tex`.  The replayable proof package is
`research/research_record/deliverables/report/proof_package/`.
The final package manifest hash is
`393771fcad83a10d89f625ab15d21710210f65266f41b0460d97867d0ef35a7c`.

The proof package contains 78 payload files, Wang's pinned certificate and `.btp` sidecar, the expanded LUT, an independent C++ re-expander, an independent quotient-row generator, the CNF encoder, eight CNF/DRAT pairs, the strict bundle verifier, and peer-research reproduction records. Standard DRAT replay, byte-identical CNF regeneration, packaged Wang verification, and isolated copied-package replay all returned `all_ok=true` before final review.

The latest official Wang arXiv record was checked directly: arXiv:2603.07280v11, last revised 2026-08-29, still states only
\(R_{\mathbb F_2}(\langle3,3,3\rangle)\ge20\) and keeps the public interval \([20,23]\).  The durable resolution file is
[wang_v11_resolved.json](../../exact_baselines/results/frontier_recheck/wang_v11_resolved.json).

## Canonical convention and symmetries

Use the convention
\[
T[3i+j,\,3j+k,\,3i+k]=1,
\qquad
T(A,B,C)=\operatorname{tr}(ABC^T).
\]
A simple tensor is written
\(A_t\otimes B_t\otimes C_t\), with each factor a \(3\times3\) matrix over \(\mathbb F_2\).

Under this convention the important tensor symmetries are:
\[
(A,B,C)\mapsto(A^T,C,B),
\]
from \(\operatorname{tr}(ABC^T)=\operatorname{tr}(A^TCB^T)\), and
\[
(A,B,C)\mapsto(B,C^T,A^T),
\]
from cyclic trace.  The earlier map involving transposes in all three slots is not correct for this convention.  Transpose preserves matrix rank, so the saturation conclusions transfer across slots when the corresponding split rank sum is at equality.

The A-, B-, and C-slot split flattenings are all \(27\times27\) permutation matrices.  For the A-slot,
\[
\Phi_A(A_t\otimes B_t\otimes C_t)
= A_t\otimes \operatorname{vec}(B_t)\operatorname{vec}(C_t)^T,
\]
so
\[
\operatorname{rank}\Phi_A(A_t\otimes B_t\otimes C_t)=\operatorname{rank}(A_t).
\]
Every rank-\(n\) decomposition therefore satisfies
\[
\sum_t\operatorname{rank}(A_t)\ge 27,
\]
and similarly in the B- and C-slots after applying the verified slot symmetries or the direct split-flattening computation.

## Wang quotient data and the new dimension-two raises

Wang's certificate supplies lower bounds \(L(W)\le R(T/W)\) for A-slot quotients by subspaces \(W\le\mathbb F_2^9\).  The occupation inequality used throughout is
\[
m(W)\le n-L(W),
\]
where \(m(W)\) is the number of first-slot factors lying in \(W\) in a length-\(n\) decomposition.

Verified Wang-owned values used by the theorem:

- all 511 A-lines have \(L=19\);
- the complete LUT contains all 8,283,458 subspaces with Gaussian-binomial dimension counts
  \(1,511,43435,788035,3309747,3309747,788035,43435,511,1\);
- for the normalized column coset span
  \(S=\langle272,4,2,1\rangle\), one has \(L(S)=14\);
- the rank-one family \(R\subset S\) has \(L(R)=15\);
- the fourteen affine-plane hyperplanes in that normalized \(S\) have \(L=17\).

this investigation's new finite propositions are the eight all-high two-plane raises.  The two-dimensional A-subspaces split into 14 orbits under \(GL_3(\mathbb F_2)\times GL_3(\mathbb F_2)\) plus A-transpose.  Exactly the representatives 484--491 have all three nonzero elements of matrix rank at least two; they contain 32,018 planes in total.  Wang's raw value for each representative is \(L=18\).  this investigation proves \(L\ge19\) for these eight representatives using DRAT-verified infeasibility of the target-18 occupation systems, with integer multiplicities retained.  Orbit 489 has one quotient direction with cap 2, so a distinct-support encoding is unsound there; the final Boolean-copy/unary encodings handle this.

The exact finite rows for each two-plane proposition have 127 quotient directions and 29,210 subspace constraints.  If a quotient decomposition had length \(n_0\le18\), its occupation vector would extend to target 18 by adding slack, so target-18 infeasibility proves quotient rank at least 19.

Reusable files:

- [wang_lut_reexpand.cpp](../../finite_certification/code/wang_lut_reexpand.cpp) rebuilds the LUT from the 496 certificate nodes.
- [reexpanded_lut_compare.json](../../finite_certification/results/wang_reexpand/reexpanded_lut_compare.json) records zero mismatch with the stored LUT.
- [dim2_orbit_coverage.json](../../finite_certification/results/orbit_coverage/dim2_orbit_coverage.json) records independent two-plane orbit coverage.
- [dim2_independent_semantics.py](../../finite_certification/code/dim2_independent_semantics.py) rebuilds the two-plane row systems from quotient semantics.
- [dim2_cnf_cert.py](../../finite_certification/code/dim2_cnf_cert.py) encodes the integer systems into CNF using Boolean copies and cardinality constraints.
- [bundle_checker.py](../../finite_certification/code/bundle_checker.py) regenerates CNFs and replays DRAT proofs.
- `research/research_record/deliverables/report/proof_package/verify_proof_package.py` is the package-local entry point for public replay.

## Algebraic endpoint that made the lower bound work

For a hypothetical length-20 decomposition, the line values exclude repeated A-directions.  The A-split flattening gives total A-rank excess at least 7, so at least four A-factors have rank at least two.  If two such high-rank factors spanned an all-high plane, the new \(L\ge19\) raise would contradict the length-20 occupation cap.  Hence every pair of high-rank A-factors differs by a rank-one matrix.

Hua's adjacency geometry then puts the high-rank factors into one affine column coset
\[
p+u(\mathbb F_2^3)^T
\]
or one affine row coset
\[
p+\mathbb F_2^3v^T.
\]
The transposition symmetry reduces row type to column type.  Normalizing column type gives the coset span
\[
S=\langle272,4,2,1\rangle.
\]
The 14 affine-plane hyperplanes of this span have \(L=17\), so at length 20 each contains at most three A-factors.  Every five points of \(AG(3,2)\) contain an affine plane; therefore there are at most four high-rank factors.  Since the split rank excess requires at least four, there are exactly four.  The four rank-three labels themselves form an affine plane, so the only possible length-20 A-profile is sixteen rank-one factors, one rank-two factor, and three rank-three factors.  The A-rank sum is exactly 27.

At equality in the split rank inequality, if
\[
P=\sum_tM_t,\qquad \sum_t\operatorname{rank}M_t=\operatorname{rank}P=27,
\]
then the row and column spaces form direct sums and
\[
M_tP^{-1}M_s=\delta_{ts}M_t.
\]
For the current tensor convention,
\[
M(A_t,B_t,C_t)P^{-1}M(A_s,B_s,C_s)
=M(A_tB_sC_t^TA_s,B_t,C_s).
\]
A diagonal equation with invertible \(A_t\) forces \(B_tC_t^T=A_t^{-1}\), so \(B_t\) and \(C_t\) are invertible.  An off-diagonal equation for two invertible A-factors then forces a product of invertible matrices to be zero.  The forced profile has three invertible A-factors, contradiction.

This endpoint is the main reusable mathematical pattern: an occupation lattice can force equality in a split-flattening rank inequality, and equality converts a one-slot counting statement into strong algebraic constraints on the other slots.

## Retired or corrected routes

These routes should not be inherited as premises for later work.

- The original strided-C coordinate grouping was wrong.  Use the contiguous B/C masks and the convention above.
- Early E11 lower-bound normalization through a shared rank-one first-slot direction was not proved and is not equivalent to excluding arbitrary length-20 decompositions.  E11 remains useful for construction because a rank-19 E11 core lifts to full rank 22 by restoring the deleted slice with three terms.
- The first fast Wang-domain DFS closures from analysis were invalid: unused capacity was treated as a requirement and partial counter updates could underflow before rollback.  Only the later transactional/saturation-only DFS runs and proof-producing CNF/DRAT files should be used.
- General quotient projection must XOR an original slice into every projected quotient coordinate affected by that slice.  Keeping only one projected slice is wrong.
- The analysis complement-restriction interpretation was a different tensor question.  For codimension-one \(W=\ker\lambda\), the quotient is the contraction \(\lambda^T\otimes I_3\), with value \(3\operatorname{rank}\lambda\).
- The `coset_closure_v2` dimension-four closure language was invalid because it counted directions available in a subspace as if they were forced occupied factors.  The replacement exact tables record LUT values without that inference.
- Orbit 479 is not load-bearing: a binary two-plane with rank pattern \((1,2,2)\) already has the high-rank pair differing by the rank-one element.  Only the all-high orbits 484--491 matter for the rank-one-difference ARTIFACT.
- The scalar Wang-plus-rank-sum squeeze from analysis is disproved by corrected orbit-count models; do not use it as a global contradiction.
- Random rank-22 support failure, rank-23 deletion/swap failure, fixed-A completion failures for selected supports, and solver timeout/UNKNOWN results do not prove nonexistence.  They are only local information about tested families.
- Global equivalence transformations preserve two-term mergeability; rescanning equivalent rank-23 schemes cannot create a merge that was not present before.

## Calibration lessons that prevented false conclusions

The useful rule is to make every zero result identify exactly what mathematical object was exhausted and how the encoding represents it.

For Wang occupation systems, distinguish quotient subspaces from restrictions to complements.  Keep raw masks and projected masks separate.  Do not delete forbidden points from row masks unless the reduced domain and the remaining constraints are mathematically equivalent.  Keep integer multiplicities unless the row caps prove singleton behavior; orbit 489 shows why this matters.

For solvers, separate UNSAT with replayed proof files from timeout, UNKNOWN, heuristic failure, local search failure, or feasible relaxations.  A solver result is reusable only when the encoding has positive controls and an independently reconstructed semantic path back to the mathematical proposition.  The strongest finite input here is not just `CaDiCaL UNSAT`; it is byte-identical CNF regeneration from quotient semantics plus DRAT replay, with a second independently written research reproducing the same propositions.

For tensor symmetries, verify the trace convention every time a map is used across slots.  this investigation corrected the transpose map and later the cyclic map; both corrections mattered for proof text and rank-22 transfer statements.

For release packages, run at least one replay from a copied directory outside the live workspace.  The isolated package replay caught defects that ordinary local runs missed: deleting the mounted package root and omitting Wang's `.btp` sidecar.

## Where rank-22 work begins

The present theorem does not decide rank 22.  It leaves several stronger, now better-defined starting points.

### Rank-19 quotients and line-value raises are the same frontier object

The verified E11 quotient is obtained by deleting the \(E_{00}\) A-coordinate under the canonical convention.  A rank-19 decomposition of that \(8\times9\times9\) quotient lifts to a full rank-22 decomposition by adding three terms for the deleted matrix slice.  Conversely, proving the quotient rank at least 20 is exactly the line-value raise \(L(\langle E_{00}\rangle)\ge 20\), i.e. the statement that the E11 core has no rank-19 decomposition.  Thus "rank-19 E11 construction" and "raising a line value from 19 to 20" are not separate difficulty classes; they are opposite answers to the same quotient-rank question.

The same duality applies to any nonzero pivot line, including the rank-orbit representatives 17 and 273 used earlier in this investigation.  For a pivot line \(\langle p\rangle\), a rank-19 decomposition of \(T/\langle p\rangle\) lifts to a full rank-22 algorithm by choosing a rank-one dual functional nonzero on \(p\) and adding the corresponding rank-3 contraction slice.  A proof \(L(\langle p\rangle)\ge20\) excludes that rank-19 quotient.  No rank-19 quotient decomposition and no line-value raise to 20 was found in this investigation; earlier timeouts and local failures do not decide the object.

This is the single highest-leverage unresolved object left by the project.  It is constructive and lower-bound relevant at the same time: one outcome gives the requested rank-22 algorithm, while the opposite outcome supplies exactly the first cap needed for any occupation-saturation attempt at length 21.  Future work should attack these quotient ranks with the repaired quotient semantics, strong positive controls, exact verification, and proof-producing encodings where possible.  Fixed-A completion can reject or accept proposed A-supports, but A-side Wang admissibility alone is abundant and does not identify the bottleneck.

### Rank-22 zero-excess profiles

At rank 22, zero excess in a slot means
\[
\sum_t\operatorname{rank}(A_t)=27.
\]
The saturation lemma then applies in that slot.  At zero A-excess, at most one A-factor can be invertible.  Therefore the zero-excess A-profile \((19,1,2)\) is impossible, where the tuple records the numbers of rank-one, rank-two, and rank-three factors.  The remaining zero-excess profiles in one slot are
\[
(17,5,0)\quad\text{and}\quad(18,3,1).
\]
By the cyclic symmetry \((A,B,C)\mapsto(B,C^T,A^T)\) and transpose-rank preservation, the same restriction applies to any slot whose split rank sum is at equality.  Zero excess in one slot does not force zero excess in the others.

This is a real structural filter for rank-22 search.  It should be used with care: it says nothing about positive-excess profiles, and it is not a rank-22 lower bound by itself.

### Quantitative length-21 continuation program

To prove rank at least 22 by extending the occupation-saturation mechanism, three quotient improvements would be needed to restore the length-20 cap pattern at length 21:

1. raise all relevant line values from \(19\) to \(20\), giving line cap \(21-20=1\) and hence distinct A-directions;
2. raise all-high two-plane values from \(19\) to \(20\), again giving cap 1 and forcing pairwise rank-one differences among high-rank A-factors;
3. raise the normalized affine-plane/hyperplane values used in the coset from \(17\) to \(18\), giving cap 3 in the \(AG(3,2)\) coset.

Under exactly these three assumed improvements, the previous chain almost reruns at length 21.  The split-flattening excess is now only
\[
\sum_t(\operatorname{rank}A_t-1)\ge 27-21=6.
\]
The restored line and all-high two-plane caps give the same rank-one-difference geometry for high-rank factors.  The three-point version of the row/column coset lemma is enough for the \(|H|=3\) branch, and the four-point version handles \(|H|=4\).  The restored affine-plane cap 3 still gives \(|H|\le4\).

The finite rank-pattern arithmetic was checked in
[length21_program_check.json](../../quotient_cores/results/length21_program/length21_program_check.json) by enumerating the 14 affine planes of \(AG(3,2)\), all triples of \(3\times3\) matrices with pairwise rank-one differences, and all high-rank subsets of the normalized cosets.  It confirms:

- if the lower block has rank one, the maximum high-factor excess under the affine-plane cap is 4, below the required 6;
- if the lower block has rank two, the only high-set families with excess at least 6 are: \(|H|=3\) with three rank-three elements; \(|H|=4\) with two rank-two and two rank-three elements; and \(|H|=4\) with one rank-two and three rank-three elements;
- the first two families have total A-rank exactly 27 in a length-21 decomposition, hence are already killed by the existing saturation identity because they contain at least two invertible A-factors;
- the only surviving family is \(|H|=4\) with one rank-two and three rank-three A-factors, total A-rank 28, i.e. one unit above split-flattening equality.

This leaves two concrete research targets rather than a vague statement that the mechanism dissolves at length 21.  First, an excess-1 near-saturation lemma could close the remaining family if it proves a restriction such as: when \(\sum_t\operatorname{rank}M_t=\operatorname{rank}P+1\) for the A-split flattening, the one-dimensional overlap in the summand row/column decomposition still prevents three invertible A-factors.  Second, the retired finite H-closure models from earlier analysis should be rerun with the widened length-21 caps, because they were built precisely for the one-rank-two-plus-three-rank-three coset shape.  Either route would be a genuine new contribution beyond the present theorem.

### Excess-one near-saturation algebra checked in analysis

The clean linear-algebra extension of the saturation endpoint is as follows.  For a split-flattening decomposition \(P=\sum_t M_t\) with \(P\) invertible, set \(E_t=M_tP^{-1}\).  Then \(\sum_tE_t=I\) and \(\operatorname{rank}E_t=\operatorname{rank}M_t\).  The addition map
\[
  \bigoplus_t \operatorname{col}(E_t)\longrightarrow \mathbb F_2^{27},
  \qquad (v_t)_t\mapsto \sum_t v_t,
\]
is surjective, so its kernel has dimension
\[
  e=\sum_t\operatorname{rank}M_t-27.
\]
At \(e=0\) this recovers the direct-sum uniqueness used in the report.  At \(e=1\), there is a unique nonzero relation \(\sum_t v_t=0\) with \(v_t\in\operatorname{col}(E_t)\).  For \(w\in\operatorname{col}(E_t)\), the two decompositions \((\delta_{st}w)_s\) and \((E_sw)_s\) differ by either zero or this single relation, linearly in \(w\).  Hence, for each fixed \(t\), there is a functional \(\lambda_t\) on \(\operatorname{col}(E_t)\) such that
\[
  E_s w=\delta_{st}w+\lambda_t(w)v_s,
\]
or equivalently
\[
  E_sE_t=\delta_{st}E_t+v_s\,\mu_t^T.
\]
Thus the orthogonal-idempotent relations survive modulo a one-dimensional, rank-one correction pattern.  This is pure algebra and is independent of the hypothetical length-21 quotient raises.

I tested the first rank-level consequences in
[excess_one_lemma_check.py](../../quotient_cores/code/excess_one_lemma_check.py), with output
[excess_one_lemma_check.json](../../quotient_cores/results/excess_one/excess_one_lemma_check.json).  The script verified the split-rank relation \(\operatorname{rank}M(X,B,C)=\operatorname{rank}X\) for probe cases and 2000 random nonzero \((B,C)\) pairs.  Feeding the excess-one degraded product identities into invertible A-factors gives necessary conditions
\[
  \operatorname{rank}(B_tC_t^T+A_t^{-1})\le1,
  \qquad
  \operatorname{rank}(B_sC_t^T)\le1\quad(s\ne t)
\]
for the relevant ordered pairs.  Exhaustion over rank-at-least-two \(B,C\) factors shows that these rank inequalities alone do **not** forbid three invertible A-factors: for every triple of rank-three labels in the normalized residual coset \(S=\langle272,4,2,1\rangle\), explicit \((B_t,C_t)\) witnesses satisfy the diagonal and all six ordered off-diagonal rank-\(\le1\) tests.  Therefore a successful excess-one lemma must use the full common one-dimensional relation \(E_sE_t=\delta_{st}E_t+v_s\mu_t^T\), or additional structure from the entire decomposition, rather than only the degraded pairwise rank bounds.  This check does not affect the proved \(R_{\mathbb F_2}\ge21\) theorem, whose endpoint is exactly zero excess.

### Subfamily span constraint from split-flattening column and row structure (earlier analysis)

There is a general rank-additivity statement that should be used in fixed-A completion work.  Let
\[
  P=\sum_t M_t,
  \qquad \operatorname{rank}P=r,
  \qquad \sum_t\operatorname{rank}M_t=r+e.
\]
Assume the column spaces of the summands span \(\operatorname{col}(P)\) (in particular this holds when \(P\) is the invertible split flattening of \(T_{\langle3,3,3\rangle}\)).  The addition map
\[
  \bigoplus_t\operatorname{col}(M_t)\to\operatorname{col}(P),
  \qquad (v_t)_t\mapsto\sum_t v_t
\]
has kernel dimension \(e\).  Therefore every subset \(S\) inherits rank additivity up to the same global defect:
\[
  \dim\sum_{t\in S}\operatorname{col}(M_t)
  \ge
  \sum_{t\in S}\operatorname{rank}M_t-e,
\]
because any relation among the \(S\)-summands extends by zeros to a relation of the whole family.  The same statement holds for row spaces.

For the A-split matrix-multiplication summand,
\[
  M_t=A_t^{\mathrm{mat}}\otimes
      \bigl(\operatorname{vec}(B_t)\operatorname{vec}(C_t)^T\bigr),
\]
so
\[
  \operatorname{rank}M_t=\operatorname{rank}A_t,
  \quad
  \operatorname{col}(M_t)=\operatorname{col}(A_t)\otimes\langle\operatorname{vec}(B_t)\rangle,
  \quad
  \operatorname{row}(M_t)=\operatorname{row}(A_t)\otimes\langle\operatorname{vec}(C_t)\rangle.
\]
Consequently, for every subspace \(V\le\mathbb F_2^9\),
\[
  \sum_{t:\,\operatorname{vec}(B_t)\in V}\operatorname{rank}A_t
  \le 3\dim V+e_A,
  \qquad
  \sum_{t:\,\operatorname{vec}(C_t)\in V}\operatorname{rank}A_t
  \le 3\dim V+e_A,
\]
where \(e_A=\sum_t\operatorname{rank}A_t-27\).  Under the cyclic tensor symmetry
\((A,B,C)\mapsto(B,C^T,A^T)\), analogous statements hold for the B- and C-split flattenings with \(e_B\) and \(e_C\).  The equal-value sharing rule recorded in analysis is only the \(\dim V=1\) special case.

analysis sharpened the finite consistency run on the known rank-23 control.  Script
[subfamily_span_constraint.py](../../quotient_cores/code/subfamily_span_constraint.py) enumerates the join-closure of the observed 23 B- and C-values, and the corresponding slot-permuted values, and records
\(\sum_{v_t\in V}\operatorname{rank}(\text{current slot})-3\dim V\) for each generated subspace.  Output
[subfamily_span_constraint_rank23.json](../../quotient_cores/results/span_constraints/subfamily_span_constraint_rank23.json) has `all_orientations_ok=true` and no negative margins.  The inequality is actually tight in the rank-23 scheme: the six orientations have maximum defects equal to their slot excesses,
\[
  (3,3,2,2,2,2),
\]
with many tight subspaces; the observed values span all nine dimensions in every orientation.  Thus the strengthened statement is not merely a loose equal-B consistency observation.

Rank-22 uses of the strengthened form include:
- at zero A-excess in profile \((18,3,1)\), the rank-three A-factor fills a full B-slice and a full C-slice and cannot share either value with any other term;
- at zero A-excess in profile \((17,5,0)\), no two rank-two A-factors can lie in the same one-dimensional B- or C-slice, and a rank-two factor can share such a slice with at most one rank-one factor;
- more generally, when \(e_A=0\), any four terms with A-rank sum at least 7 must have their B-values spanning dimension at least 3, and likewise for C; at \(e_A=1\), any subfamily of A-rank sum at least 8 also needs B- and C-span dimension at least 3.

For codimension-one subspaces \(V=\ker\phi\), with \(\phi(B)=\operatorname{tr}(\Lambda^T B)\), the classical contraction lower bound gives complementary information on the number of terms outside \(V\):
\(\#\{t:\phi(B_t)\ne0\}\ge 3\operatorname{rank}\Lambda\).  The subfamily span inequality is rank-weighted and especially useful on small spans or fixed-A completion instances.  Both filters should be carried into successor fixed-support and quotient-completion pipelines.

**Why the pairwise excess-one test failed (correction of analysis).**
The saturation constraint is a global independence constraint on subspaces such as
\(\operatorname{col}(A_t)\otimes\langle\operatorname{vec}(B_t)\rangle\).  It is not reducible to collections of two-term rank inequalities.  The pairwise degraded rank tests become weak for \(3\times3\) matrices once \(e\ge3\), which is exactly where verified rank-23 schemes live.  The earlier guess that excess alone should give an immediate bound of the form “at most \(e+1\) invertible factors” should not be used without a proof using the full subspace relation.
### Construction transformations from known rank-23 algorithms

Known rank-23 schemes are verified under the canonical convention, and one such witness has slot rank sums \((30,29,29)\).  No direct two-term merge was found because no pair is linearly dependent in two slots.  Deletion/swap repairs produced Wang-admissible length-22 A-multisets but no fixed-A completion.  Since global equivalence does not change mergeability, future transformations must alter the decomposition nontrivially: plus-transitions, exact-decomposition-preserving flips, or solving a constrained completion problem with changed support.

Any proposed rank-22 scheme must be verified as an exact tensor identity over \(\mathbb F_2\), preferably by both the project verifier and an independent direct tensor-residual script.

## Practical starting commands and paths

For the completed lower-bound package:

```
python research/research_record/deliverables/report/proof_package/verify_proof_package.py --replay-drat
python research/research_record/deliverables/report/proof_package/verify_proof_package.py --replay-drat --regenerate-cnf
python research/research_record/deliverables/report/proof_package/verify_proof_package.py --rerun-wang-verifier
```

For final report integrity:

```
python scripts/final_report_checks.py
```

For future construction verification, use the matrix-multiplication skill verifier on a proposed scheme file and also retain a simple direct residual computation under the canonical tensor convention.

## Bottom line for successors

Inherit the rank-21 lower bound as a replayable theorem package, not as an informal search outcome.  Inherit the canonical convention, quotient semantics, split-flattening saturation mechanism, all-high two-plane raises, and exact package-verification workflow.  Do not inherit the retired false closures, wrong transpose maps, complement-restriction interpretation, or timeout-based exclusions.

The next frontier is no longer separating Wang's rank-20 theorem from a possible rank-21 theorem; that has been done here.  The next frontier is either a rank-22 construction, most naturally through repaired rank-19 quotient/E11 work or nontrivial transformations of rank-23 algorithms, or a new lower-bound mechanism strong enough to survive the length-21 cap widening.
