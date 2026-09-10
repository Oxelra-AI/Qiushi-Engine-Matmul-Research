# Rank-Constrained Occupation Analysis and Calibration

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Summary of findings

### 1. Orbit-level MILP with flattening rank constraint

**Question**: Does the combination of Wang occupation + rank-sum lower bound (Σ rank(a_t) ≥ 27) create infeasibility at the orbit level?

**Answer**: NO for both pivots.

- **Pivot 17 (rank 2)**: orbit MILP feasible with rank sum 57. Solution: Y=[0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,0,0,0,13,0], selecting 6+13=19 points all from rank-3 orbits. 45,247 unique orbit-coeff rows. LP min rank sum = 19 (full: 21), well below threshold 25 (full: 27).

- **Pivot 273 (rank 3)**: orbit MILP feasible with rank sum 40. Solution: Y=[0,1,2,0,4,8,0,3,0,0,0,1], selecting 19 points from mixed-rank orbits. 15,145 unique orbit-coeff rows. LP min rank sum = 19 (full: 22), below threshold 24 (full: 27).

**Conclusion**: The stabilizer-averaged Wang constraints + integer rank-sum lower bound are jointly satisfiable at the orbit-count level for both pivots. No R ≥ 21 proof is available from orbit-level occupation + flattening.

### 2. Point-level MILP preliminary results

- **dim≤2 (line constraints) + rank ≥ 25**: Feasible in 0.3s. Solution has rank sum 43 but 14,317 full-row violations. Line constraints are far too weak.
- **dim≤3 + rank ≥ 25**: HiGHS timed out at 120s (status: Time limit). LP relaxation feasible at rank sum exactly 25.0. Background run at 600s underway.

### 3. n=23 det calibration (DECISIVE)

**Question**: Can the inverse-determination SAT oracle complete random low-rank Wang-admissible n=23 supports (where solutions are known to exist)?

**Answer**: NO. All 5 random low-rank (rank sum 27-30) n=23 enhanced-pass candidates timed out at 180s. CaDiCaL cannot distinguish completable from non-completable A-supports in this regime.

**Implication**: The volume-based generate-and-complete construction search produces no evidential information at either n=22 or n=23. The pipeline correctly rejects candidates by structural criteria (enhanced trace filter catches ~50%), but the SAT completion ARTIFACT cannot resolve the remainder within practical timeouts. This is because:
1. The search space is enormous (~10^38 A-supports modulo GL₃×GL₃)
2. Random samples live at rank sum ~49, while known algorithms sit near 27-30
3. Even low-rank samples are structurally unlike valid decompositions
4. CaDiCaL's performance on B/C completion is dominated by the algebraic structure of tight contractions, not by the existence of a solution

The construction search should be retired in favor of structural approaches: local modification of known exact decompositions, symmetry-constrained search, or algebraic family construction.

### 4. Flattening structural constraints

**A-slot split flattening**: All three slot flattenings of T_{3,3,3} are 27×27 permutation matrices. This gives:
- Σ rank(a_t) ≥ 27, Σ rank(b_t) ≥ 27, Σ rank(c_t) ≥ 27

**Column/row containment (dim Y=1)**: For every nonzero u ∈ F₂³:
- #{t : u ∈ col(a_t)} ≤ Σ rank(a_t) - 18
- #{t : u ∈ row(a_t)} ≤ Σ rank(a_t) - 18

At rank sum 27, no column direction appears in more than 9 terms' column spaces.

**Important caveat**: Column containment is NOT Stab(p)-invariant (it depends on the P component of the group action). Therefore orbit-averaged column containment is not a valid necessary condition for the point-level problem. These constraints must be applied at the point level if used.

### 5. Status of research routes

**Lower bound R ≥ 21**:
- Orbit MILP + rank: CLOSED (feasible for both pivots)
- Point-level MILP + rank (dim≤3): OPEN (600s test running)
- Full Wang + rank + column containment at point level: UNTESTED
- B/C-sensitive family constraints: NOT AVAILABLE (per-support only)

**Upper bound R ≤ 22**:
- Volume search: RETIRED (n=23 calibration negative)
- Structural modification of rank-23: OPEN (needs work)
- E11 rank-19 construction: STALLED (no progress since analysis)

## Key artifacts
- [pivot17_milp_v2.json](../../quotient_cores/results/rank_lp/pivot17_milp_v2.json) - orbit MILP pivot 17
- [pivot273_milp_v2.json](../../quotient_cores/results/rank_lp/pivot273_milp_v2.json) - orbit MILP pivot 273
- [pivot17_point_milp_dim2.json](../../quotient_cores/results/rank_lp/pivot17_point_milp_dim2.json) - point MILP dim≤2
- [det_batch_summary.json](../../quotient_cores/results/pipeline_n23_lowrank_det_calibration/det_batch_summary.json) - n=23 calibration
- [pipeline_rank_control_summary.json](../../quotient_cores/results/pipeline_n23_lowrank_calibration/pipeline_rank_control_summary.json) - n=23 control
- [rank_orbit_milp_v2.py](../../quotient_cores/code/rank_orbit_milp_v2.py) - orbit MILP script
- [point_milp_sparse.py](../../quotient_cores/code/point_milp_sparse.py) - point-level MILP script
