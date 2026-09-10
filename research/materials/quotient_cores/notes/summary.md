# Complete Research Summary

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Main Result: Cancellation Degeneration with Constant Gauge-Invariant Diagnostic

The gauge-fixed continuation paths from rank-23 decompositions of T_{3,3,3}
exhibit cancellation degeneration where the gauge-invariant rank-drop diagnostic
E(t) = σ_min · ||w̃_k|| / |λ_k| stays constant at ~1.0-1.2. This means:

1. The path NEVER genuinely approaches a rank-22 configuration
2. The decreasing σ_min is exactly compensated by diverging factor norms
3. The amplitude A(t) = Σ||u_i||·||v_i||·||w_i|| / ||T|| grows as ~t²
4. The tangential product ||Δp||·||Δw|| ≈ 2-3 stays O(1) (nonzero limit contribution)

**This is evidence consistent with, but not proving, rank(T_{3,3,3}) = 23.**

## Cancellation Scan Results

- serendipitous_8d34: 7/10 liftable directions cancel at t=20 (cos > 0.99)
- cn122: 9/10 liftable directions cancel at t=20
- Different directions cause different term pairs to merge projectively
- Diverse cancelling pairs: (10,17), (10,15), (7,14), (2,4), (10,12), etc.

## E11 Core (8×9×9, nnz=24) Search Results

| Method | Parameters | Result |
|--------|-----------|--------|
| flip-cpd (analysis) | rank-19 target, 2001 r20 attempts | Best rank 21 |
| Span search (analysis) | 19.8M replacements from 21-term | Deficiency 1 |
| Kissat SAT | 1800s timeout | No result |
| CaDiCaL SAT | 900s timeout (r19 and r20) | No result |
| Random span | 500K trials | Fundamentally wrong (p~2^{-496}) |
| CryptoMiniSat | 1200s timeout | Running (task s4_t28_tool1) |

## E12+E21 Core (8×9×9, nnz=27) Search Results

| Method | Parameters | Result |
|--------|-----------|--------|
| flip-cpd | rank-19 target, 3000 r20 attempts | Best rank 21 |

Both cores resist shortening below rank 21 via flip-cpd.

## review-Informed Priority Directions

1. **E11 rank-19 enhanced SAT** (highest rank-22 UB priority)
   - CryptoMiniSat with native XOR/Gaussian (running)
   - Cube-and-conquer preprocessing
   - Wang occupation constraints
   - Build XOR-native encoding for CryptoMiniSat

2. **H₂/H₃ restriction cores for lower bound** (highest rank-23 LB priority)
   - If R_{F₂}(any core) ≥ 22, then R_{F₂}(T) = 23
   - Need Wang-style certificate or SAT-based exclusion

3. **Full F₂ rank-22 envelope** (definitive F₂ determination)
   - 9-dim slice space L_A ⊆ F₂^81
   - Need 22 of 261,121 rank-one 9×9 matrices to span L_A
   - Branch-and-bound with orbit reduction

4. **Positive control test** (methodology validation)
   - Apply same continuation to a tensor where rank drop IS known
   - Validates whether E(t) diagnostic is informative

## Background Tasks

- s4_t28_tool1: CryptoMiniSat on E11 rank-19, ~1200s timeout, still running

## Key New Files This ARTIFACT

- Scripts: puiseux_analysis.py, projective_cancellation.py, cancellation_scan.py, e11_rank19_algebraic.py
- Data: puiseux_analysis.json, cancellation_analysis.json, cancellation_scan_serendipitous.json, cancellation_scan_cn122.json, e11_rank19_span_search.json
- Notes: cancellation_degeneration.md, corrected_cancellation.md
- review: independent-verification-record,verifier}1_integration.md
