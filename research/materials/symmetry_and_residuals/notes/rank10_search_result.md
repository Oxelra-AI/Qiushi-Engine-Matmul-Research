# Constructive search for rank-≤10 residual in (10,4) cyclic family

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Setup

For the BILR 4-plane exterior configuration (rigid up to PGL₃), the residual cubic
depends on internal SL₃ frames within the 4 planes. BILR's residual has Waring rank 11
(Koszul rank 722, Pfaffian Φ=-80000). We search for frames where the Strassen
commutator rank([H_X, H_Y]) ≤ 2, which would give Waring rank ≤ 10 and a 22-term
cyclic scheme.

## Objective

Sum of squared 4×4 Pfaffians of Ω_a = K [6S_{X_a}, 6S_{Y_a}] over 5 test direction
pairs, including the analysis integer certificate pair.

## Results

| Search type              | Restarts | Best f          | Best rank | BILR ratio |
|--------------------------|----------|-----------------|-----------|------------|
| BILR baseline            | —        | 2.751 × 10¹³    | 4         | 1.0        |
| Random survey (1000 pts) | —        | 7.714 × 10²¹    | —         | ~10⁸       |
| Powell from 20 best rand | 20       | 4.299 × 10¹¹    | 4-8       | 0.016      |
| Fresh Powell restarts    | 30       | 4.299 × 10¹¹    | 4-8       | 0.016      |
| Local search (σ=0.1)     | 30       | 2.046 × 10¹¹    | 8         | 0.0074     |
| Single-dir pair search   | 30       | 1.316 × 10⁷     | 8         | ~10⁻⁴      |

**All optimized frames have numerical commutator rank 4 or 8, never ≤ 2.**

The optimizer reduces the objective by reducing the overall scale of the commutator
(smaller entries → smaller Pfaffians), NOT by reducing the rank. The identity frame
(BILR) has rank 4; optimized frames typically have rank 8.

## Interpretation

The BILR exterior 4-plane configuration does not contain any internal SL₃ frame where
the residual cubic has Waring rank ≤ 10. The commutator rank is robustly ≥ 4 across
the entire family:

- 50 optimization runs: rank 4 or 8 at all minima
- 1000 random frames: no rank ≤ 2
- analysis modular scans (F₃₁): 300 random + elementary/diagonal slices, all rank ≥ 4

This evidence is consistent with (10,4) being excluded for the BILR exterior
decomposition of the Cartan form. However:

1. This does NOT exclude other exterior decompositions of ω ∈ Λ³(sl₃)
2. The (7,5), (4,6), (1,7) nontraceless branches remain open
3. The search is numerical/heuristic, not a proof

## Remaining gap

The exact exclusion of (10,4) requires either:
- Prove the BILR exterior decomposition is unique up to PGL₃ (fiber analysis)
- Then the numerical evidence here plus the F₃₁ modular scan gives strong evidence
- Or: exact algebraic elimination over the 16-effective-parameter family

## Extended search with normalized objective (critical diagnostic)

A 300-restart search using **normalized Pfaffians** (Pf²/‖Ω‖⁴, scale-invariant) was run.
Every trial quickly found apparent "rank 2" with normalized objective ~10⁻³⁴. However:

- Raw Pfaffian sums at these points: 10⁵⁰ to 10¹⁰⁷
- Frame parameter norms: enormous (causing overflow warnings)
- SVD fails at these extreme scales (LinAlgError: SVD did not converge)

**Interpretation: border-rank degeneration, not genuine rank 22.**

At frame parameters ‖θ‖ ≫ 1, the SL₃ matrices grow, Ω entries reach ~10¹⁵⁺, and the
4×4 Pfaffians involve cancellations below float64 precision (~15 digits). The SVD reports
"rank 2" because the residual singular values are lost to rounding error. In exact
arithmetic the rank would remain ≥ 4.

This is entirely consistent with the known border rank ≤ 20: the 22-dimensional family
approaches the boundary of rank-one-generated spaces in the closure, but never reaches
it at a finite point. The normalized objective's apparent zero is a mirage created by
numerical cancellation at extreme scales, not a genuine rank-22 decomposition.

**The correct evidence is the raw (unnormalized) search:**
- At moderate frame norms (‖θ‖ ≤ 5), minimum raw objective is 2.05×10¹¹
- Commutator rank is robustly 4 or 8 at all well-conditioned frames
- No finite rank-≤10 frame was found in this numerical search; this is not an exclusion of finite frames

## Summary

The numerical search did not find an ordinary rank-≤10 residual in the sampled, well-conditioned part of the BILR exterior frame family. The commutator rank was robustly ≥ 4 in those sampled finite frames, dropping below 4 only through noncompact scale degeneration. This is useful evidence about where not to search, but it is not a finite-family exclusion and not a proof for any complete cyclic rank-22 stratum.

## Files

- Scripts: [rank10_residual_search.py](../code/rank10_residual_search.py), `extended_search.py`
- Data: [quick_search.json](../results/rank10_search/quick_search.json)
- Background task output: `workspace/tasks/s55_t11_tool1/stdout.log`
