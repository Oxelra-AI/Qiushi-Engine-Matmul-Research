# Modular search and gauge chart calibration for rank-22 T333

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Key findings

### 1. ALS over F_p is completely ineffective for tensor CP decomposition

Tested ALS (alternating least squares) from random starts over F_65521 for both 
rank-22 and rank-23 decompositions of T333, plus a positive control on a random 
rank-22 tensor. Results:

- **Random rank-22 tensor control**: 0/200 ALS starts found a decomposition.
  Minimum residual reached: 378/729 nonzero entries (~52%).
- **T333 rank 23**: 0/3000 ALS starts found anything. Min residual: 729/729 (no improvement).
- **T333 rank 22**: 0/3000 ALS starts. Min residual: 729/729.
- **ALS homotopy** (tracking from random rank-r tensor to T333): 0/200 paths completed.

Root cause: Over F_p, ALS solves a 22×22 subsystem at each ARTIFACT but has no 
metric to minimize the residual on the remaining 59 rows. Without a norm, ALS
cannot converge. This is fundamentally different from ALS over R (which minimizes
Frobenius norm via least squares).

**Conclusion**: ALS and random-start Newton are NOT viable search methods for 
tensor rank over finite fields. Structured algebraic methods (Gröbner, homotopy
from known solutions, elimination) are required.

Data: [modular_search_results.json](../results/modular_search/modular_search_results.json)
Scripts: [modular_rank22_search.py](../code/modular_rank22_search.py)

### 2. Gauge chart (identity + companion normalization) is calibrated

Built the explicit gauge transformation:
- u_anchor → I_3 (identity matrix as 3×3)
- u_anchor2 → companion form via cyclic vector decomposition
- v_anchor → I_3
- All term scalings: u_i[0]=1, v_i[0]=1

Results on random rank-22 controls:
- **Gauge success rate**: 30/30 (100%) for random rank-22 decompositions
- **Brent Jacobian rank**: 550 (generic, as expected)
- **Combined J+G rank**: 594 = 27×22 (FULL RANK) — confirming isolated solutions
- **Gauge matrix rank**: 67 (need one more condition for 68; adding v_2[1]=0)
- **Projected-kernel rank**: 22 (against their own tensors, not T333)

**Key result**: After gauge fixing, rank-22 decompositions are ISOLATED POINTS
over F_p (0-dimensional variety). The J+G combined system has full rank 594,
meaning Newton's method converges locally from any sufficiently close starting point.

Data: [gauge_chart_calibration.json](../results/gauge_chart/gauge_chart_calibration.json)
Scripts: [gauge_chart_v2.py](../code/gauge_chart_v2.py)

### 3. cn122 has ALL singular 3×3 factor matrices

**Critical structural finding**: All 23 u-factors AND all 23 v-factors of the
cn122 rank-23 decomposition have determinant 0 when viewed as 3×3 matrices.
No single factor is invertible.

However, linear combinations ARE invertible: u_0 + u_1 has det = -2 (mod 65521).
This means the "hitting set" approach is essential: the gauge chart
must use linear-combination anchors, not individual terms.

For the generic rank-22 chart: random decompositions have invertible individual 
factors (30/30 success with first-term anchoring). So the identity chart covers 
the generic layer. The singular-factor layer (like cn122) is a lower-dimensional
stratum requiring separate charts.

### 4. Newton homotopy over F_p: conceptual limitation

The deformation T_t = (1-t)T0 + t*T333 with t ∈ F_p is NOT continuous — modular 
inverse of N gives t values scattered across F_p, not "close" to 0. The algebraic 
homotopy curve might exist but Newton tracking over F_p requires the path to pass 
through the F_p-rational points of the rank-22 variety at each sampled t-value.

A proper homotopy would work over Q_p (p-adic rationals) via Hensel lifting, or
over the algebraic closure F̄_p. Over F_p alone, the homotopy is essentially a 
sequence of independent polynomial system instances.

Scripts: [newton_homotopy.py](../code/newton_homotopy.py) (built but not yet run to completion)

## Route assessment

The gauge chart is calibrated and correct. The barrier is NOT the chart construction
but the SEARCH within the chart: finding a specific point in F_p^{328} where 531
polynomial equations vanish simultaneously.

Effective methods for this would be:
1. **Gröbner basis on subsystems**: Fix most variables, solve small systems
2. **p-adic/Hensel lifting**: Work over Z/p^kZ, lift from mod-p solutions
3. **Structured Newton from cn122 modifications**: Not single-term deletions 
   (which are first-order obstructed) but deeper algebraic modifications
4. **Elimination theory**: Compute resultants on small projected subsystems
5. **Symmetry exploitation**: Use the GL_3^3 × S_3 structure of T333 to 
   constrain the search space

The 328-variable system is too large for direct Gröbner. The most promising
near-term route: use the projected-kernel structure to fix 13 pivot terms and
reduce to a 144-variable system in the 9 remaining terms' UV coordinates.
