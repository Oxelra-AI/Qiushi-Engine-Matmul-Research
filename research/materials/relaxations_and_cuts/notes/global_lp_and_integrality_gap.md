# Global LP Integrality Gap and Joint Integer Hull Analysis

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Core Wang Occupation Mapping — Verified Correct

The E11 core Wang table uses the LIFTED subspace mapping: for a core subspace
U ⊆ F_2^8, the LUT lookup is for span(E11, ι(U)) ⊆ F_2^9 (confirmed from
`core_capacity_from_wang_lut.py` line 87-90: `key9_from_key8` prepends the
pivot to the lifted basis). The occupation bound is:

    #{core terms in U} ≤ 19 - L_full(span(E11, ι(U)))

The dim-1 core entries have L ∈ {17, 18} (NOT 19):
- 6 directions with L=17, cap=2 (the capacity-2 directions from analysis)
- 249 directions with L=18, cap=1

This is consistent with the repeated-branch exclusion and confirms the
violation framework is sound.

## Complete Dim-by-L Distribution (Corrected from analysis)

| dim8 | L values (count)                                                  |
|------|-------------------------------------------------------------------|
| 0    | 19(1)                                                             |
| 1    | 17(6), 18(249)                                                    |
| 2    | 15(2), 16(525), 17(9830), 18(438)                                |
| 3    | 14(1098), 15(12801), 16(58428), 17(24828)                        |
| 4    | 11(13), 12(8798), 13(498), 14(50424), 15(117009), 16(24045)     |
| 5    | 9(2733), 11(852), 12(46974), 13(7632), 14(29826), 15(9090), 16(48) |
| 6    | 6(428), 9(4715), 12(5460), 14(192)                               |
| 7    | 3(33), 6(150), 9(72)                                             |
| 8    | 0(1)                                                              |

Total: 417,199 rows.

## Local 4D Joint Integer Hull — No Gap

For 5 pairs of dim-5 violating subspaces sharing dim-4 intersections, built
16-variable LP/IP models on the 4D dual joint subspace (66 Wang constraints +
fiber capacities + sum=19). Result: ALL LP vertices are integral for all tested
objectives. The local polytope is tight — no integer cuts at the 4D level.

## Global LP — ALWAYS Fractional

Full 417,199-constraint LP with 255 continuous variables in [0,1], sum=19:
- 13/13 LP vertices tested are fractional
- Typical: 60-99 fractional variables per vertex
- Only 61-73 active constraints at each vertex
- Maximum fractional part: ~0.5 (genuinely half-integral)
- Violation subspace occupation maximizes to exactly 7.0 (=cap) at fractional vertices

This confirms a SIGNIFICANT integrality gap: the LP relaxation is strictly
larger than the integer hull. The Wang constraints form a polytope that admits
many fractional solutions invisible to integer supports.

## Implications

1. The LP feasibility does NOT settle IP feasibility.
2. Integer cuts exist but are not captured by individual rows or local projections.
3. The cuts must come from GLOBAL interactions among many constraints.
4. Direct MILP solving (binary IP) is the most direct path to either:
   - Finding a Wang-admissible support (IP feasible → upper bound direction)
   - Proving no such support exists (IP infeasible → R_F2(core) ≥ 20)

## Files

- [joint_integer_hull.py](../../quotient_cores/code/joint_integer_hull.py) — local 4D analysis
- [global_lp.py](../code/global_lp.py) — global LP analysis
- [milp_test.py](../../quotient_cores/code/milp_test.py) — MILP feasibility test
- [joint_integer_hull_analysis.json](../../quotient_cores/results/joint_hull/joint_integer_hull_analysis.json)
- [global_lp_analysis.json](../results/joint_hull/global_lp_analysis.json)
- `workspace/data/joint_hull/milp_feasibility_test.json` (pending)
