# Block Decomposition of E11 Moment Matrix — Decisive Results

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Summary

The group-algebra eigenspace decomposition reduces the 256×256 PSD cone
(32,896 scalar parameters) to 93 small blocks (594 scalar parameters),
making the SDP solvable in **7.4 seconds** (vs 1800s timeout before).

## Block Structure

The 1152-element E11 stabilizer acting on C^{256} gives 93 eigenspaces:

| Block size m | Count | PSD params each | Total |
|:---:|:---:|:---:|:---:|
| 1 | 23 | 1 | 23 |
| 2 | 25 | 3 | 75 |
| 3 | 24 | 6 | 144 |
| 5 | 16 | 15 | 240 |
| 6 | 4 | 21 | 84 |
| 7 | 1 | 28 | 28 |
| **Total** | **93** | | **594** |

Validation: the four analysis witnesses correctly identify as PSD-violating
through the block decomposition (full vs block minimum eigenvalues agree to 1e-5).

## Continuous Feasibility Result

**The continuous Wang+RLT+triangle+PSD system is FEASIBLE.**

| Quantity | Value |
|:---|:---|
| SDP status | optimal_inaccurate (AlmostSolved) |
| Solve time | 7.365 s |
| Full 256×256 min eigenvalue | 1.3e-12 (≈0, cardinality kernel) |
| Negative eigenvalue count | 0 |
| Equality residual | 3.6e-12 |
| Upper-bound violation | 3.6e-11 |

Feasible point mass distribution over 6 point orbits (sizes [6,9,36,72,36,96]):

| Orbit | Mass | Density x_a |
|:---:|:---:|:---:|
| 0 | 0.672 | 0.112 |
| 1 | 0.712 | 0.079 |
| 2 | 2.958 | 0.082 |
| 3 | 5.029 | 0.070 |
| 4 | 2.754 | 0.077 |
| 5 | 6.875 | 0.072 |
| **Total** | **19.0** | |

The PSD constraint forces a spread-out distribution (cf. analysis RLT-only
vertex which concentrated on orbits 4–5). All 92 of 97 pair orbits are nonzero.

The minimum eigenvalue is exactly 0 because M·(-19,1,...,1)^T = 0 identically
for any feasible (x,y) satisfying the pair cardinality equations. The PSD
condition on the quotient is nontrivial but satisfied.

## Integer Count-Vector Feasibility

Testing 30 integer count vectors nearest to the continuous optimum:

- **26 PSD-feasible** (found pair distributions satisfying LP + PSD)
- **3 infeasible** ([0,2,3,5,2,7], [0,2,3,5,3,6], [1,2,3,5,2,6]; all have n_1=2)
- **1 solver error**

The 3 infeasible vectors all have n_1=2 (orbit 1, size 9); they may be
LP-infeasible rather than specifically PSD-infeasible.

## Mathematical Significance

**The combination of Wang occupation, Sherali-Adams pair correlations, triangle
inequalities, and moment-matrix PSD is insufficient to exclude distinct 19-point
E11 supports, even at the integer count-vector level.**

This is a precise negative result: the orbit-averaged second-moment necessary
conditions are consistent. The information content:

1. First-moment occupation (Wang rows) alone has a large integrality gap
   (continuous LP feasible with uniform x = 19/255).
2. Second-moment occupation (pair correlations + PSD) tightens the model but
   still admits continuous AND integer feasible points.
3. The remaining obstruction must come from higher-order combinatorial structure:
   actual graph/color realizability, third+ moments, or specific support geometry.

## What This Changes

1. **analysis's serial PSD cutting-plane loop cannot converge**: the continuous
   system is feasible, so no finite collection of square cuts can prove
   LP infeasibility.

2. **The count-vector sweep from analysis would largely confirm feasibility**:
   most count vectors admit PSD-feasible pair distributions. The few infeasible
   ones (n_1=2 cluster) may be LP-infeasible rather than PSD-infeasible.

3. **The research must move to point-level methods**: the 255-binary-variable
   complete-Wang support search, with accumulated face/overlap cuts and
   the fixed-A/B/C compatibility pipeline.

## Reusable Artifacts

- Block decomposition script: [block_sdp_v2.py](../code/block_sdp_v2.py)
- Integer count test: [integer_count_test.py](../../quotient_cores/code/integer_count_test.py)
- Continuous SDP result: [block_sdp_result.json](../results/block_sdp/block_sdp_result.json)
- Feasible z vector: [feasible_z.npy](../arrays/block_sdp/feasible_z.npy)
- Integer results: [integer_count_psd_results.json](../results/block_sdp/integer_count_psd_results.json)

The block decomposition infrastructure (93 eigenspaces, their projections of
orbit coefficient matrices) can be reused for any future moment-matrix work.
