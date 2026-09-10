# 13+9 completion chart — construction, calibration, and structural analysis

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

**analysis supersession.** The analysis F₂ "reduction slot" interpretation and cokernel-fraction interpretation are not valid evidence for rank ≥ 23. In the 13+9 chart, the 13×9 matrix C is free column-by-column, so one pivot column may be used in any subset of the nine derived columns; cross-slice intersection or damage counts for D=I single corrections do not impose a slot budget. The real finite-field object is the canonical span problem: find rank-one 9×9 matrices whose span contains the nine-dimensional UV-slice space L. The generic cokernel fraction near rank-22 points is also not an obstruction; dimension 179/729 already predicts about 0.50 for a random target direction, so the measured ≈0.41 should be retired. See [canonical_span_oracle_and_ledger.md](../../quotient_cores/notes/canonical_span_oracle_and_ledger.md) for the corrected interpretation and exact F₂ oracle results.

## Summary

The 13+9 completion chart for T₃₃₃ rank-22 incidence was built, calibrated, and subjected
to three decisive structural tests.  All three provide strong evidence against rank 22,
though none constitutes a proof.

## 1. Chart construction and calibration

The chart parametrizes a 22-term full-UV-rank decomposition T = X_P A^T + X_R B^T by:
- 13 free rank-one UV columns x_i = u_i ⊗ v_i (234 variables)
- C ∈ K^{13×9} (117 variables)
- D ∈ GL_9 (81 variables)
with derived columns X_R = T_flat D − X_P C, each constrained to rank ≤ 1.

**review reduction**: rank[X_P, X_R] = 9 + rank(QX_P) where Q is the 72×81
quotient annihilating L = col(T_flat).  Full UV rank 22 ⟺ rank(QX_P) = 13.
No 22×22 minor atlas is needed.

**Positive controls** (5/5 over F_{65521}):
- Derived columns match original: ✓
- All 9 derived columns rank 1: ✓
- det(D) ≠ 0: ✓
- rank(QX_P) = 13: ✓
- All 729 Brent identities verified: ✓
- Jacobian rank at control: 550 (as expected)
- UV-rank formula: rank_X_full = 9 + rank_QXP ✓ on all controls.

## 2. cn122 deletion patterns

23/23 deletions from cn122 are self-valid (chart works for the truncated tensor).
0/23 deletions produce valid chart solutions against T₃₃₃.

Derived column rank patterns (number of rank-2 columns per deletion):
- **Best**: drop=20 (1 rank-2 column), drop=21 (1 rank-2 column)
- **Worst**: drop=12 (8 rank-2 columns)
- **Typical**: 2-4 rank-2 columns

The single failing column in drops 20, 21 is the most structurally tantalizing: 8/9 of the
rank-shortening subproblems are already solved.  But the remaining one cannot be repaired
without breaking the others, consistent with the first-order obstruction from analysis.

## 3. Real homotopy continuation (gauge-fixed)

Homotopy T(t) = (1-t)T₀ + t·T₃₃₃ from random rank-22 tensors T₀:
- **All 8 paths diverged immediately** (amplitude > 10^{19} at first ARTIFACT).
- Root cause: T₃₃₃ has a substantial cokernel component.

**Cokernel diagnostic** (20 random rank-22 points, scale 0.3):
- T₃₃₃ cokernel fraction: mean 0.412 ± 0.027, range [0.35, 0.48]
- This means ~41% of T₃₃₃'s norm lies in directions unreachable by any infinitesimal
  change in a rank-22 decomposition.
- The fraction is stable across random rank-22 points.

At a hypothetical rank-22 preimage of T₃₃₃, the Terracini analysis (analysis) forces
Jacobian rank ≤ 526, making the cokernel even larger (≥ 203 dimensions vs 179 generic).

This does not prove rank ≥ 23: the Jacobian varies nonlinearly, and a special point could
have T₃₃₃ in its image.  But the consistency is strong geometric evidence.

## 4. F₂ rank-shortening structure (with D = I)

Each T₃₃₃ W-slice is a rank-3 binary 9×9 matrix (3 ones in block-diagonal form).

**Key findings**:
- Each slice has exactly **28** rank-1 F₂ corrections reducing its rank from 3 to 2.
- **Zero** corrections reduce any slice to rank 1 directly.
- **Zero universal reducers** (no correction helps all 9 slices).
- **Zero pairwise intersection**: the 252 = 28 × 9 reducers partition perfectly by slice.

**Interpretation**: over F₂ with standard W-basis, each rank-1 correction can reduce at most
ONE slice's rank.  For rank-22, we need 2+ effective reductions per slice (rank 3 → 1),
requiring ≥ 18 "reduction slots."  With only 13 corrections (each serving exactly 1 slice),
this appears extremely tight.

**Multi-correction analysis** (extended):
- For each first-ARTIFACT reducer, exactly **6** rank-1 "completion partners" bring the
  rank-2 intermediate to rank ≤ 1.  Total viable ordered pairs per slice: 168.
- Each reducer **damages exactly 4 of 8** other slices (increases their rank 3 → 4).
- **Zero neutral reducers**: every reducer hurts at least 1 other slice (hurts exactly 4).
- These exact integers (28 single, 6 pair, 4 damage, 0 neutral) are stable across all
  9 slices, reflecting the Kronecker symmetry of T₃₃₃'s block structure.

**Formal implications**: to reach rank ≤ 1 from rank 3, each slice needs ≥ 2 "effective"
corrections.  With D = I: (i) the first correction helps 1 slice but damages 4; (ii) the
second must come from the 6 specific completion partners; (iii) every correction applied to
non-target slices either damages (97%) or maintains (3%) their rank.

The D = I restriction limits this analysis.  With D ≠ I (different W-basis), the
slice structure changes and the numbers above do not apply.  However, the D = I analysis
reveals the combinatorial tightness inherent in the Kronecker block structure of T₃₃₃.

## 5. Overall assessment

No rank-22 decomposition was found.  No unconditional rank-23 proof was established.
The evidence from three independent approaches (homotopy, F₂ combinatorics, and the
conditional nontransverse exclusion from earlier analysis) consistently points toward rank ≥ 23,
but each has explicit limitations.

The conditional nontransverse exclusion (all aligned patterns have certified block-rank
sum ≥ 23, conditional on Bläser's R(M_{3,3,2}) ≥ 14) remains the strongest partial result.

## Files

- [completion_chart.py](../code/completion_chart.py): Chart construction and calibration
- [homotopy_v2.py](../../quotient_cores/code/homotopy_v2.py): Gauge-fixed homotopy
- [f2_analysis.py](../../quotient_cores/code/f2_analysis.py): F₂ rank-shortening analysis
- [completion_chart_results.json](../results/completion_chart/completion_chart_results.json): Chart calibration data
- [f2_rank_shortening.json](../../quotient_cores/results/f2_analysis/f2_rank_shortening.json): F₂ analysis data
- [homotopy_gauged.json](../../quotient_cores/results/homotopy_v2/homotopy_gauged.json): Homotopy results
