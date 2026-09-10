# corrected route assessment

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

research: research_record. Goal remains exact tensor rank of \(T_{\langle3,3,3\rangle}\): an exact rank-\(\le 22\) algorithm, or a rigorous exclusion of rank \(\le22\) over a stated field or structure. This note corrects the interpretation of analysis and compares the next useful research directions without treating any smaller catalog task as the goal.

## 1. Corrections to the analysis interpretation

The analysis rank-aware CP-SAT experiment for the adjacent-pair branch solved an adaptive row-insertion sequence. Its round log is:

- round 0: impose residual-\(\le2\) Wang rows, get a mixed support with 1302 newly violated rows;
- round 1: impose those 1302 rows too, get a different support with 1392 newly violated rows;
- round 2: impose those rows too, get 843 newly violated rows;
- round 3: impose those rows too, get 1052 newly violated rows;
- round 4: impose those rows too, get 1562 newly violated rows;
- round 5: the enriched formula returns UNKNOWN after the time limit.

Since each batch from an earlier model is imposed before later models are generated, raw intersection zero between successive violation sets is expected. It does not show that iterative separation cannot converge, does not imply an estimate such as thousands of necessary rounds, and does not imply that rep2 is Wang-feasible. The only supported statement is narrower: the tested enriched formula did not settle rep2, and the five supports are useful probes of which row families current relaxations miss.

The matching runs above 275 survivors also do not prove a permanent limit of the witness-subset representation. They show nonuniform difficulty: idx31 closed with individual solver attention and DRAT replay, while idx20 and several larger strata did not close in the tested time and round budgets. Size alone is not enough to predict proof search difficulty.

## 2. Reanalysis of the analysis rep2 supports

New scripts and outputs:

- [rep2_violation_symmetry.py](../../symmetry_and_residuals/code/rep2_violation_symmetry.py)
- [rep2_common_violation_orbits.py](../code/rep2_common_violation_orbits.py)
- [rep2_rankaware_violation_symmetry.json](../../symmetry_and_residuals/results/corrected_strategy/rep2_rankaware_violation_symmetry.json)
- [rep2_common_violation_orbits.json](../results/corrected_strategy/rep2_common_violation_orbits.json)

Main facts from these outputs:

- All five analysis supports were rescanned against the full 8,283,458-row LUT.
- Raw violated rows across the five supports are disjoint, as expected from adaptive insertion.
- Under the setwise stabilizer of \(\{1,2\}\) of order 192, those raw rows collapse to 2416 violated row orbits.
- Orbit recurrence is real: 18 row orbits are hit by all five supports, 99 row orbits are hit by at least four supports, and pairwise orbit overlap ranges roughly from 0.06 to 0.15 Jaccard.
- The strongest recurring families include dimension 6 or 7 rows with lower bounds 14 or 15 and residual-after-prefix 4 or 5, plus some dimension 7/8 rows with weaker lower bounds. This suggests that useful compression may come from whole row orbits and their interactions with mixed rank-1/high-rank structure, not from raw row-set overlap.

Interpretation: the rep2 experiment remains valuable, but now as a source of recurring branch-invariant Wang-row families to promote or reason about. It is not evidence for existence or nonexistence of a full Wang-admissible support.

## 3. Route comparison after the correction

### Route A: continue finite-field Wang support exclusion, but seek reusable mixed-rank structure

Value: A full exclusion of length-20 A-supports under Wang occupation would prove \(R_{\mathbb F_2}(T)\ge21\). This would be a real finite-field advance beyond Wang's rank-20 lower bound. The route has durable assets: complete LUT, correct key decoding, no-rank-1 proof, pure rank-1 and exact-\(k=18\) closures, adjacent/matching cover, 16 matching strata certificates, and valid ruling-line transport.

Weakness: The support problem is still only an A-side necessary condition. Even a complete A-support exclusion gives \(R_{\mathbb F_2}\ge21\), not characteristic-zero rank 23. Matching has 22 open strata and rep2 is open.

Best next work: avoid indiscriminate longer runs. Use row-orbit recurrence and actual-set stabilizers to generate compact families: add entire stabilizer orbits of rows hit by several rep2 supports, test whether they eliminate model families or produce small reusable contradictions, and convert only successful finite families into proof-producing CNFs. For matching, select cases by structural similarity to closed strata and by row-orbit interactions rather than survivor count alone.

### Route B: two-sided support search followed by B/C coupling

Value: Searching for a fully Wang-admissible A-support is useful because either outcome informs the lower-bound route. If a support satisfying every A-side Wang row is found, it becomes a concrete fixed-A target for solving the \(B,C\) Brent equations. A full decomposition over \(\mathbb F_2\) would be an exact upper-bound breakthrough in that field. Even failure of B/C coupling for several structurally distinct supports may reveal constraints involving all three slots that A-only occupation misses.

Weakness: The five analysis supports are not close evidence of such an object; each still violates many rows. A fixed-A B/C solve is only meaningful after the A-support is verified against all rows.

Best next work: build a proof-safe or at least exact full-LUT support search with stabilizer-row promotion, not a raw CP-SAT run with a few cuts. If a zero-violation support appears, immediately export it with complete LUT verification and ask related analysis or review to run fixed-A B/C solving, while also checking Wang-style support restrictions in B and C.

### Route C: restricted-core rank-19 construction or exclusion

Value: The E11 codimension-one core has a verified rank-21 decomposition from cn122 and lower bound 19. A rank-19 E11-core decomposition would lift to a full \(\mathbb F_2\) rank-\(\le22\) algorithm by adding the removed rank-3 slice. Conversely, proving the E11 core has rank at least 20 would raise the full finite-field lower bound to 21 through the rank-1 restriction route. This is smaller than the full tensor and directly tied to both upper and lower directions.

Weakness: The earlier Boolean core encoder is simple and likely weak; lazy A-support searches for rank 19 returned UNKNOWN, not verified feasibility or infeasibility. Rank-21 core pools and near-miss scans did not yield two-term repair.

Best next work: revive the core route with a more semantic representation: start from known rank-21 E11 core decompositions, search for two-term deletion/merge or rank-19 supports satisfying the induced core occupation constraints, then run fixed-A B/C core solves only after exact support verification. This route has high information value because it can produce either a rank-22 upper bound over F2 or a clean finite-field obstruction.

### Route D: direct rank-22 / rank-23 structural search over full tensors

Value: It is closest to the original upper-bound goal and to characteristic-zero relevance if performed over integer/rational domains. Rank-23 families, flip graphs, BILR/cyclic schemes, and tangent directions may expose rank-drop mechanisms not visible in Wang occupation.

Weakness: Direct Brent equations and Challenge 4 are enormous; negative solver time alone is not mathematical evidence. The current related analysis BILR/Z4 line is interesting but still highly restricted and undergoing convention repairs.

Best next work: do not replace the finite-field route with a blind rank-22 search. Use direct rank-22 work when it is anchored by a structurally promising source: a verified core support, a near-rank-drop family, or a reproducible rank-23 deformation with exact constraints.

## 4. Recommended next research action

The immediate next work should stay in Explore long enough to turn the corrected evidence into a sharper construction/exclusion interface, then hand to Execute. The most valuable executable target is not a long monolithic solve but a compact rep2 row-orbit promotion experiment:

1. From `rep2_common_violation_orbits.json`, select recurrent row orbits hit by at least four of the five analysis supports, prioritizing dimension 6/7 rows with lower bounds 14/15 and residual-after-prefix 4/5.
2. Add whole setwise-stabilizer row orbits, not isolated raw rows, to the rank-aware rep2 model with exact \(k\)-layer control and the valid ruling-line clauses.
3. Compare whether these orbit-promoted formulas quickly eliminate the five known support families or generate a smaller recurring contradictory family.
4. If a formula becomes UNSAT, regenerate it with row provenance and DRAT replay; if it returns a full zero-violation support, export it for fixed-A B/C solving.

Parallel but secondary: prepare a restricted-core E11 rank-19 support/B-C coupling interface, because this is the cleanest upper-bound bridge to a rank-\(\le22\) algorithm over \(\mathbb F_2\). Do not spend another ARTIFACT treating raw violation diversity or survivor count as evidence of impossibility.

## 5. Mathematical Correction

related analysis should be told not to use related analysis record's statements that iterative separation cannot converge for rep2, that it would need an approximate number of rounds, that rep2 may be Wang-feasible because of raw disjointness, or that witness separation has a proven structural ceiling. The valid analysis facts remain: idx31 closed with DRAT verification; idx20 and several other strata resisted the tested runs; rank-aware rep2 staged CP-SAT ended UNKNOWN; rep2 remains open.
