# next execution plan after corrected route assessment

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

Active goal: determine the exact tensor rank of \(T_{\langle3,3,3\rangle}\) by an exact rank-\(\le22\) algorithm or a rigorous rank-23 optimality/lower-bound result over a stated field or structure.

This plan is research-facing only. It should not be treated as final writing.

## A. Corrected evidence to preserve

1. The analysis inference from raw zero-overlap of rep2 violation rows is invalid. The CP-SAT run adaptively inserted each model's violated rows into the next formula, so later violation sets are forced to be disjoint from earlier inserted rows. The final rank-aware formula returned `UNKNOWN`; rep2 remains open.
2. Failed bounded matching runs do not prove a structural limit of witness-subset separation. idx31 closed with DRAT verification; idx20 and other strata resisted the tested parameters. The real lesson is nonuniform proof-search difficulty, not a survivor-count threshold.
3. Valid finite-field assets remain: complete Wang LUT with verified key/RREF semantics, no-rank-1 and high rank-only exclusions, pure rank-1 and exact-\(k=18\) closures, adjacent/matching cover, ruling-line transport from the checked `[1,2,3]` prefix, and 16 matching closures including idx31.
4. The new useful rep2 signal is branch-symmetric recurrence: `rep2_common_violation_orbits.py` found 6151 raw violated rows collapsing to 2416 row orbits under the setwise stabilizer of `{1,2}`; 18 row orbits are hit by all five analysis models and 99 by at least four. This is descriptive evidence for row-family promotion, not a proof.
5. The difference between the full LUT size and analysis `total_constraining_rows` is explained by preprocessing: under prefix `{1,2}`, 8,282,848 rows are binding and 610 are nonbinding/trivial; no negative-residual prefix contradiction appears. See [rep2_constraining_row_account.json](../results/corrected_strategy/rep2_constraining_row_account.json).

## B. Rep2 row-orbit promotion pilot

### Object

Normalize an adjacent rank-1 pair to prefix `[1,2]`. Remaining variables are 509 projective A-points, with target 18 selected. Include:

- exact cardinality 18;
- rank-1 structural constraint: at most 15 additional rank-1 candidates, because exact-\(k=18\) closure implies at most 17 rank-1 points total including prefix;
- valid ruling-line clauses from analysis;
- Wang rows expanded by entire setwise-stabilizer row orbits, not isolated raw rows.

### First row-orbit tiers

Use [rep2_common_violation_orbits.json](../results/corrected_strategy/rep2_common_violation_orbits.json):

- Tier 1: the 18 row orbits hit by all five analysis models.
- Tier 2: add the highest-frequency hit-4 orbits, prioritizing residual-after-prefix 4 or 5 and lower bound 14 or 15, but keep the selection recorded exactly by canonical key.
- Tier 3: add all 99 orbits hit by at least four models, only if Tier 1/2 remains SAT and produces useful fresh models.

For a row with residual capacity \(c\), the exact inequality is `sum(x_p for p in row∩candidates) <= c`. Direct CP-SAT is acceptable for a pilot. If a tier gives UNSAT, regenerate a CNF with fresh auxiliary ranges and explicit row provenance, then replay DRAT before using it as proof. If a tier gives SAT, scan the support against all 8,283,458 Wang rows; a zero-violation support should be exported immediately for fixed-A B/C solving.

### Interpretation

- A SAT model with violations is a diagnostic support only.
- Fewer violations do not measure proof progress by themselves.
- Raw row-set overlap has no route-level meaning in adaptive insertion.
- Recurring orbit families should be tested against fresh seeds or held-out models when possible.

## C. Fixed-A B/C completion interface

For any full-rank A-support matrix \(U=[a_1\cdots a_r]\), let \(M_1,\dots,M_d\) be the A-slices of the target tensor and write

\[
M_i = \sum_{s=1}^r U_{is} X_s,
\qquad X_s=b_s c_s^T.
\]

Choose an information set \(J\) of \(d\) independent A-columns and let \(K\) be the remaining columns. Then

\[
X_J = U_J^{-1} M - (U_J^{-1}U_K)X_K
\]

over \(\mathbb F_2\) (minus equals plus). Thus fixed-A Brent solving reduces to imposing rank-one conditions on all \(X_s\): every \(2\times2\) minor of each \(9\times9\) matrix is zero, and each selected rank-one tensor should be nonzero.

For the full tensor at rank 20, \(d=9,r=20\), so there are 11 free \(9\times9\) matrices. For the E11 restricted core at rank 19, \(d=8,r=19\), again there are 11 free \(9\times9\) matrices. One implementation can serve both routes.

Add contraction saturation before SAT where possible. For a matrix functional \(Q\) on A, define

\[
I_Q=\{s:\langle Q,a_s\rangle=1\},\qquad L_Q=T(Q,\cdot,\cdot).
\]

If \(|I_Q|=\operatorname{rank}(L_Q)=3\operatorname{rank}(Q)\), then the terms in \(I_Q\) form a shortest rank-one decomposition of \(L_Q\), so each corresponding \(b_s\) and \(c_s\) lies in the column/row spaces of \(L_Q\). Intersections across saturated contractions can fix or eliminate variables before the full quadratic system.

## D. E11 restricted-core rank-19 bridge

The E11 core has a verified rank-21 decomposition from the cn122 restriction and Wang lower bound 19. A rank-19 decomposition of this core gives a full \(\mathbb F_2\) rank-\(\le22\) algorithm after adding the removed rank-3 slice. Conversely, core rank at least 20, together with the existing no-rank-1 branch proof for the full tensor, strengthens the finite-field lower-bound route to \(R_{\mathbb F_2}(T)\ge21\).

Immediate computations:

1. Compute a reduction spectrum for the known 21-term E11 core scheme: for subsets \(I\) of size 3..8, use flattening ranks of \(R_I=\sum_{i\in I}t_i\) as necessary filters for whether \(R_I\) may have rank at most \(|I|-2\). A successful replacement of \(|I|\) terms by \(|I|-2\) terms would yield a rank-19 core decomposition.
2. Revisit core rank-19 A-support search only with full-LUT verification and then fixed-A B/C completion. Earlier lazy support `UNKNOWN` statuses are not evidence.
3. Use the same fixed-A completion engine as in C for any candidate support.
