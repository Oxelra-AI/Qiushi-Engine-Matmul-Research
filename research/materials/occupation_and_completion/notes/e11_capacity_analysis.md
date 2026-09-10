# Complete E11 Core Capacity Analysis

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Research Context
Following analysis's identification of the E11 core-to-full lift (rank r → r+3) and the
flawed orbit catalog, this ARTIFACT builds the globally complete description of admissible
E11 rank-19 A-multisets using the full Wang occupation framework.

## Key Construction

### Core Capacity MIP
For the E11 core at target rank s=19, the constraint system is:
- Variables: x_q for q ∈ F₂⁸\{0} (255 nonzero vectors), x_q ∈ {0,...,19}  
- Equality: Σ x_q = 19
- For each subspace Ψ ⊆ F₂⁸ (417,199 total):
  sum_{q ∈ Ψ\{0}} x_q ≤ s - L_T(span(e₀, lift(Ψ)))
  where L_T is the Wang LUT lower bound for the lifted F₂⁹ subspace

**Meaning**: INFEASIBLE proves R_F₂(E11) ≥ 20, closing the constructive route.
FEASIBLE gives admissible A-multisets for SAT testing.

### Constraint Structure at s=19
- 249/255 vectors have cap=1 (multiplicity ≤ 1, from L=18 lifted subspaces)
- 6 vectors have cap=2 (from L=17 lifted subspaces)
- 438 dim-2 subspaces have cap=1 (triple exclusions)
- Total: 417,199 constraints from all subspaces of F₂⁸

### Greedy Test
A greedy algorithm found 19 independent vectors satisfying all cap=1 constraints
from dim-1 and dim-2. The greedy set {1,2,3,4,8,9,12,13,16,18,20,22,24,27,28,31,32,36,42}
was immediately SAT-UNSAT (0.01s): these A-factors don't admit valid B/C factors.
This was expected (most random A-multisets won't work for a rank-19 CPD).

### T-Level Rank Branches (bg task s6_t51)
- rank-3 branch: INFEASIBLE at s=20 (no all-rank-3 decomposition)
- rank-1 branch: UNKNOWN after 5 iterations  
- rank-2 branch: UNKNOWN after 1 iteration
- T-level lower bound remains 20 (rank-3 branch alone is not sufficient)

## Running Computations
- s7_t17_tool2: Complete E11 core capacity LP + CP-SAT (1800s limit)
  CP-SAT has presolved to 3,395 variables, 394,550 constraints and started search

## Next Steps (depending on MIP result)
1. **If INFEASIBLE**: E11 rank ≥ 20 → constructive route closed → check E12+E21 and H3
2. **If FEASIBLE**: Run capacity-then-SAT pipeline:
   a. Enumerate admissible multisets via CP-SAT solution enumeration
   b. Orbit-reduce under corrected E11 stabilizer (576 elements, 8 orbits)
   c. SAT-test each representative with fixed-U solver
   d. Any SAT → rank-19 E11 CPD → full rank-22 T₃₃₃ decomposition
3. **If UNKNOWN**: Need stronger solver or combined capacity+SAT model

## Files
- Scripts: e11_complete_capacity_solve.py, e11_cap1_structure.py, e11_greedy_sat_test.py, e11_capacity_sat_pipeline.py
- Data: e11_complete_capacity/{cap1_structure.json, greedy_sat.json, greedy_verify.json}
