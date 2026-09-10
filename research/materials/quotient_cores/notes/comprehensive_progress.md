# correction notice for this analysis note

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

The route-level interpretation in this analysis note has been corrected by [corrected_route_assessment.md](corrected_route_assessment.md). In particular, raw zero intersection between rep2 violation sets is expected because each violated batch was inserted before the next model was solved; it does not show nonconvergence, does not support any extrapolated round count, and does not imply Wang-feasibility. The failed bounded matching runs also do not prove a structural ceiling. The durable analysis facts remain: idx31 closed with DRAT replay, matching progress is 16/38, the rank-aware rep2 formula ended UNKNOWN, and rep2 remains open.

# Comprehensive Progress and Strategy Update

## Major Finding 1: RREF Verification Recovers 15/38 Matching Closures

[verify_lut_rref_and_rerun_strata.py](../code/verify_lut_rref_and_rerun_strata.py) verified:
- All 8,283,458 LUT keys have RREF bases (0 violations)
- `make_pivot_dict`/`in_span_piv` matches `span_of` perfectly (100K samples, 0 mismatches)
- The analysis "span bug" was only in analysis's own key decoder, NOT in analysis infrastructure
- **All 15 matching strata closures from earlier analysis are definitively valid**

Evidence: [results.json](../results/lut_verify_and_strata/results.json)

## Major Finding 2: Rep2 Violation Sets Have Zero Overlap

Rank-aware CP-SAT models (prefix {1,2}, target 18, max 15 rank-1 candidates):
- Rounds 0-4 found feasible mixed-rank supports (r1=12-15, hr=3-6)
- Each violated 843-1562 Wang rows
- **Pairwise Jaccard similarity = 0.000 for ALL model pairs**
- Universal violations (rows violated by ALL models) = 0

This means:
1. Each CP-SAT model exploits a completely different "loophole"
2. No single Wang row universally blocks rep2
3. Iterative separation would need ~8000+ rounds (at ~1000 violations/round)
4. Rep2 might be Wang-feasible (admissible A-support exists but no decomposition)

Evidence: [result.json](../results/rep2_rankaware/result.json)

## Major Finding 3: Witness Separation Has Structural Ceiling

Batch results for open matching strata:
- idx05 (275 survivors, target 16): MAX_ROUNDS after 30 rounds
- idx09 (275 survivors, target 16): MAX_ROUNDS after 30 rounds
- idx20 (265 survivors, target 15): timed out at round 6+
- idx02 (282 survivors, target 17): MAX_ROUNDS after 30 rounds  
- idx30 (342 survivors, target 14): MAX_ROUNDS after 30 rounds

These are all LARGER than the closed strata (which had ≤265 survivors and were closed
in 4-5 rounds). The approach doesn't scale.

## Current Matching State: 16/38 closed (idx31 newly closed this ARTIFACT)

| k | Total | Closed | Open |
|---|-------|--------|------|
| 7 | 6 | 6 | 0 |
| 6 | 10 | 6 | 4 (idx26,27,29,30) |
| 5 | 10 | 4 | 6 (idx16-21) |
| 4 | 7 | 0 | 7 (idx05-11) |
| 3 | 3 | 0 | 3 (idx02-04) |
| 2 | 1 | 0 | 1 (idx01) |
| 1 | 1 | 0 | 1 (idx00) |

## Rep2 State

- analysis zero-survivor claim: WITHDRAWN (wrong key decoding)
- analysis [1,2,3] closure: VALID (DRAT verified)
- Ruling-line transport: 95 valid clauses, doesn't help at pair level (analysis)
- Rank-aware staged CP-SAT: feasible models with 843-1562 violations each round
- Violation zero-overlap: iterative separation fundamentally too slow
- Rep2 remains OPEN

## Strategic Assessment

### For matching strata (23 open):
The witness-separation iterative approach works only for strata with ≤265 survivors.
Remaining strata need:
1. **Much longer CaDiCaL runs**: idx20/idx31 (twins of closed strata) might close with
   individual runs of 1000+s per solve, 50+ rounds
2. **Direct SAT with enhanced encoding**: pre-encode residual-2 rows as at-most counters,
   then use witness separation only for residual-3+
3. **LP/ILP formulation**: ortools or SCIP with all constraints
4. **Different proof technique**: for k≤4 strata with 450+ survivors

### For rep2:
Wang occupation alone may not exclude adjacent-pair supports. Options:
1. **Find a Wang-admissible rep2 support**: if one exists, test Brent B/C completion →
   could give rank-20 over F2 (breakthrough!)
2. **Brent-coupled exclusion**: encode both Wang occupation AND Brent equations
3. **Accept Wang ceiling**: prove matching strata closure = R_F2 ≥ 21 only for
   no-adjacent-pair decompositions
4. **Structural obstruction beyond occupation**: use degeneration, isotropy, or
   other algebraic arguments
