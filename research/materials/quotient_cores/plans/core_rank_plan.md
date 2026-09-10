# E11 Core Rank Determination — Research Plan

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Master Problem

Determine ρ = R_{F₂}(E11 core), where E11 core ∈ F₂^{8×9×9}, nnz=24.

Known: 19 ≤ ρ ≤ 21 (Wang lower bound + cn122/flip-cpd upper bound).

Within the E11 route, either outcome of the rank-19 core decision reaches one branch of the research goal:
- ρ ≤ 19 implies R(T_{333}) ≤ 22 via the verified bridge, giving a rank-22 upper-bound breakthrough.
- ρ ≥ 20 implies R(T_{333}) ≥ 21 via the rank-1 A-factor reduction from any hypothetical rank-20 full decomposition to a 19-term E11 core, provided that reduction proof is independently replayed at proof-object and semantic levels.

These are implications for this E11 surface, not biconditionals for the global tensor. A rank-22 full algorithm might exist outside the E11 route, and other lower-bound mechanisms could bypass E11.

## Strategy: SAT Encoding of Core-Only Brent System at Rank 19

### Encoding Structure

**Variables** (per term t = 1,...,19):
- u_t[s] for s=0..7: core A-factor (8 bits)
- v_t[b] for b=0..8: B-factor (9 bits)
- w_t[c] for c=0..8: C-factor (9 bits)
- Base total: 19 × 26 = 494

**Auxiliary variables**:
- a_{t,s,b} = u_t[s] ∧ v_t[b]: 19 × 8 × 9 = 1,368
- p_{t,s,b,c} = a_{t,s,b} ∧ w_t[c]: 19 per equation × 648 = 12,312
- XOR chain auxiliaries: ~18 per equation × 648 ≈ 11,664
- Estimated total: ~26,000 variables

**Constraints**:
- Tseytin for a_{t,s,b}: 3 clauses each × 1,368 = 4,104
- Tseytin for p_{t,s,b,c}: 3 × 12,312 = 36,936
- XOR encoding: ~57 clauses per equation × 648 = 36,936
- Estimated total: ~78,000 clauses

### Comparison with Challenge-4 (MM-22.cnf)
- Challenge-4: 24,975 vars, 111,780 clauses, 594 base vars (22 terms × 27 vars)
- Core encoding: ~26,000 vars, ~78,000 clauses, 494 base vars (19 terms × 26 vars)
- Core encoding is slightly smaller but structurally richer (block-diagonal)

### Clause layers and symmetry handling

**Certified layer currently implemented** ([e11_core_sat.py](../code/e11_core_sat.py)):
1. Brent equations for the 648 core entries with explicit Tseytin AND variables and XOR chains.
2. Per-slice capacity: each slice has matrix rank 3, so at least three terms have `u_t[s]=1`.
3. Term-permutation sorting by nondecreasing integer value of `u_t`.

**Sound orbit branch layer currently implemented** ([e11_quotient_orbits.py](../code/e11_quotient_orbits.py) plus branch CNFs):
The E11 quotient stabilizer has 8 nonzero point orbits of sizes `[3,3,9,36,36,36,36,96]`. Instead of fixing `u_1` to a globally lexicographic value, branch `i` forbids all earlier orbit members and forces one term to the representative of orbit `i`. The union over the eight branches covers all nonzero E11-core CPDs after the verified quotient action.

**Accelerator layer not yet used for theorem clauses**:
Wang occupation rows, distinct projected `u_t`, corrected independent-verification-record consequences, and other support-level restrictions are valuable for witness hunting and preprocessing, but must remain out of proof-bearing CNFs until each mathematical implication and encoding has been replayed in this investigation.

### Implementation Plan
1. Write CNF generator script with configurable structural cuts
2. Verify encoding correctness against known rank-21 pool (should be SAT at rank 21)
3. Run CaDiCaL on rank-19 encoding
4. If UNSAT: generate DRAT proof, verify with drat-trim
5. If SAT: extract witness, verify with qiushi-matmul verifier
6. If UNKNOWN: add more structural cuts, try Kissat/other solvers

### Positive Controls
Before using an UNSAT result mathematically, validate each trusted configuration against a known satisfiable rank-21 core instance and also test that non-unit structural clauses are satisfied by the known decomposition. Current status:
- Certified layer at rank 21 with known units validates internally and CaDiCaL returns SAT.
- Branch 0 at rank 21 with known units validates internally, the known assignment satisfies all non-unit structural/branch clauses, and CaDiCaL returns SAT.
- Further branch controls should be produced with transformed known decompositions if a branch-specific proof object becomes important.

## Parallel Tracks

### Track A: SAT encoding (primary)
Build and solve the core-only Brent system at rank 19.

### Track B: Semantic search with fixed-A completion
For selected Wang-admissible A-supports:
1. Fix 19 distinct u_t ∈ F₂^8 \ {0}
2. Solve the resulting linear system for v_t, w_t over F₂
3. If feasible: verify core decomposition
Use the corrected quotient action to reduce A-support enumeration.

### Track C: Lift obstruction (contingency only)
The residual rank-≤1 lift condition speaks to whether a found rank-19 core can sit inside a full rank-20 decomposition. It is not needed for either requested breakthrough if the E11 core rank decision is settled, but before that settlement it remains a possible independent route to excluding rank 20. Preserve the recorded 0/6,291,456 calibration as evidence of tightness; do not extend it unless it becomes the most direct way to close the full rank-20 case or a rank-19 core witness is found.

## Files Produced in This ARTIFACT
- [e11_bridge_verify.py](../code/e11_bridge_verify.py) — this investigation bridge verification
- [lift_obstruction_analysis.py](../code/lift_obstruction_analysis.py) — lift condition structure
- [lift_calibration.py](../code/lift_calibration.py) — calibration on rank-21 pool
- [core_brent_analysis.py](../code/core_brent_analysis.py) — Brent equation analysis
- `workspace/data/e11_bridge/` — bridge verification data
- `workspace/data/lift_obstruction/` — lift analysis data
- `workspace/data/lift_calibration/` — calibration results
- `workspace/data/core_sat_analysis/` — Brent structure analysis
- [e11_formulation_and_lift.md](../notes/e11_formulation_and_lift.md) — original (contains error)
- [corrected_formulation.md](../notes/corrected_formulation.md) — corrected master dichotomy

## Dependencies (from earlier research, need independent replay)
- Wang lower bound ρ ≥ 19: from Wang arXiv 2603.07280v6
- Rank-1 A-factor branch proof: DRAT objects in research_record (rank-2 + rank-3 branch)
- Repeated-direction proof: DRAT object from research_record analysis
- These should be independently replayed in this investigation before crediting them
