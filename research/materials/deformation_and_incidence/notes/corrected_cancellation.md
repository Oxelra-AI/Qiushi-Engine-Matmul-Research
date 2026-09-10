# CORRECTED: Cancellation Degeneration and Gauge-Invariant Analysis

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Summary

The analysis continuation path from serendipitous_8d34 exhibits **cancellation degeneration**
with a **constant gauge-invariant rank-drop measure E(t) ≈ 1.0**. The decreasing
column-normalized pairing singular values σ_min(t) are exactly compensated by diverging
factor norms, so the path never genuinely approaches a rank-22 configuration.

## Gauge-Invariant Diagnostics (review-verified)

The key quantity is E(t) = σ_min(P) · ||w̃_k|| / |λ_k|, where P is the column-normalized
pairing matrix, w̃_k = w_k · ||u_k⊗v_k|| is the absorbed third factor, and λ_k is the
null vector component. Along the path:

| t    | σ_min     | A(t)    | E(t) | Δp·Δw |
|------|-----------|---------|------|-------|
| 1    | 1.21e-01  | 18.4    | 1.83 | 9.40  |
| 10   | 5.26e-03  | 94.0    | 1.04 | 2.27  |
| 20   | 7.05e-04  | 577     | 1.06 | 2.37  |
| 40   | ~1.2e-04  | ~4000   | 1.14 | ~2.8  |
| 60   | 4.75e-05  | 11660   | 1.19 | 3.27  |

Key observations:
- **E(t) ≈ 1.0-1.2**: Essentially constant. No gauge-invariant progress toward rank 22.
- **A(t)**: Amplitude grows as ~t², confirming divergent decomposition weight.
- **min_prod ≈ 1.4**: No term vanishes; this is NOT a "term deletion" rank drop.
- **Δp·Δw ≈ 2-3**: Product of pairing difference and w-difference stays O(1),
  confirming nonzero tangential contribution in the limit.

## Corrected Interpretation (per review verifier)

The original note overclaimed in several ways:

1. **"Approaches border-rank-22"** is incorrect. The limit has a nonzero tangential
   contribution: ||Δp|| · ||w₁₀-w₁₇|| ≈ O(1). Two terms approaching the same Segre
   point with divergent weights produce a limit object (p, tangent_vector) of length 2,
   not length 1. The total decomposition length stays 23 in any proper compactification.

2. **"Generic"** from 16/20 tested directions is numerically suggestive but not
   algebraically proven genericity. The 4 non-cancelling directions failed due to
   solver divergence, not demonstrated absence of cancellation.

3. **"Closes the continuation route"** should be: "closes the naive arclength
   continuation along unobstructed residual tangent directions for two specific
   families." Other continuation strategies (multi-parameter, constrained rank-defect,
   pseudo-arclength with singular handling) remain untested.

4. The rank-defect condition in the pairing matrix has expected codimension 59
   (= (81-22)×(23-22)) in the parameter space, not codimension 1. Random 1-d paths
   should not be expected to hit it.

## Correct Scientific Statement

> Along gauge-fixed arclength continuations from two independently verified rank-23
> decompositions of T_{3,3,3}, the gauge-invariant rank-drop diagnostic E(t) remains
> constant at O(1), while the amplitude A(t) diverges. This means these specific
> paths parametrize non-compact ends of the rank-23 decomposition fiber F₂₃(T) where
> two terms projectively coalesce, not genuine approach to rank-22 decompositions.
> The observation is consistent with but does not prove rank(T_{3,3,3}) = 23.

## E11 Core SAT/Search Results

Three parallel approaches to the E11 rank-19 problem all failed:

1. **Kissat (1800s)**: Timeout, no solution/UNSAT
2. **CaDiCaL (900s each)**: Timeout for both rank-19 and rank-20
3. **Random span (500K trials)**: Fundamentally wrong approach — the probability
   that 19 random F₂^72 vectors contain a fixed 9-dim subspace is ~2⁻⁴⁹⁶

The naive Tseitin SAT encoding is insufficient for this instance within
reasonable time bounds. Enhanced encodings (XOR-native solver, cube-and-conquer,
occupation constraints, symmetry breaking) are needed.

## Remaining Research Directions (review-informed priority order)

1. **E11 rank-19 with enhanced SAT/search** (highest priority for rank-22 upper bound)
   - CryptoMiniSat with native XOR handling
   - Cube-and-conquer preprocessing
   - Wang occupation constraints integrated into the encoding
   - Structured algebraic search targeting the 8-dim A-span

2. **Rank-2 and rank-3 restriction cores** (highest priority for lower bound)
   - Test whether H₂ (mask 10: E12+E21) or H₃ (mask 84: E13+E22+E31) has F₂-rank ≥ 22
   - If so: R_{F₂}(T) = 23
   - Already constructed by research_record; need flip-cpd and SAT runs

3. **Full F₂ rank-22 envelope determination**
   - Reformulate as: does the 9-dim slice space lie in the span of 22 rank-one 9×9 matrices?
   - 261,121 candidate rank-one matrices over F₂
   - Exact covering problem amenable to branch-and-bound with orbit reduction

4. **Modular seed + Hensel lifting** (conditional on finding F₂ seed)

5. **Positive control test**: Apply the same continuation analysis to a tensor where
   rank-drop IS known to exist, to validate the diagnostic methodology.

## Key Files

- [puiseux_analysis.py](../../quotient_cores/code/puiseux_analysis.py) — power-law and Laurent fits
- [projective_cancellation.py](../code/projective_cancellation.py) — projective normalization
- [cancellation_scan.py](../code/cancellation_scan.py) — multi-direction scan
- [puiseux_analysis.json](../../exact_baselines/results/fmm_r23_schemes/puiseux_analysis.json)
- [cancellation_analysis.json](../../exact_baselines/results/fmm_r23_schemes/cancellation_analysis.json)
- [cancellation_scan_serendipitous.json](../../exact_baselines/results/fmm_r23_schemes/cancellation_scan_serendipitous.json)
- [cancellation_scan_cn122.json](../../exact_baselines/results/cn122_r23_reproduce/cancellation_scan_cn122.json)
- `independent-verification-record`
- `independent-verification-record`
