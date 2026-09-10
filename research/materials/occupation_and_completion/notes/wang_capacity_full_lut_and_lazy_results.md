# Wang occupation constraints as a complete finite geometry problem

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

The goal remains the exact tensor rank of `T_<3,3,3>`.  This ARTIFACT rebuilt the Wang occupation/capacity computation after the analysis halfspace error and after the review correction that core-level infeasibility is not the same as a full `T` lower bound.

## Correct mathematical objects

Let Wang's certificate give a lower bound `L(Phi)` for the restriction of `T_<3,3,3>` by an A-side constraint subspace `Phi <= (F2^9)^*`.  For a rank-`s` exact decomposition over `F2` with projective A-factors `a_t in F2^9 \ {0}`,

```text
#{t : a_t in Phi \ {0}} <= s - L(Phi).
```

Reason: the terms whose A-factor lies in the constraint span disappear under the restricted tensor, so at least `L(Phi)` terms must survive.

Two important corrections are now fixed in the research state:

1. The capacity constraint is a subspace-membership/multiplicity bound, not a halfspace count over `<f,a>=1`.
2. For proving `R_F2(T) >= 21`, the decisive capacity problem is the full `T`-level `s=20` problem on `P(F2^9)`, not only an E11-core `s=19` problem.  E11-core infeasibility at `s=19` would prove `R_F2(core_E11) >= 20` and would rule out rank-20 decompositions using a rank-1 A-factor up to symmetry, but it does not rule out rank-20 decompositions whose A-factors all have matrix rank 2 or 3.

For a pivot `p` (E11, E12+E21, or E13+E22+E31), the codimension-one core quotient has A-space `F2^8`.  A rank-`s` core decomposition with projective A-factors `q_t in F2^8\0` must satisfy

```text
#{t : q_t in Psi\0} <= s - L_T(span(p, lift(Psi)))
```

for every subspace `Psi <= F2^8`.  Core `s=19` infeasibility would show that core rank is at least 20 over `F2`; feasibility would give an admissible A-factor support for a much smaller B/C-only decomposition search.

## Complete Wang subspace LUT

Script: [wang_capacity_lazy.py](../code/wang_capacity_lazy.py).

Command run:

```bash
python scripts/wang_capacity_lazy.py --force-lut --build-only --check-cn122
```

Main output:

- Complete expanded LUT path: `data/wang_f2_lb20/wang_subspace_lut.pkl`
- Metadata: [wang_subspace_lut.meta.json](../../quotient_cores/results/wang_f2_lb20/wang_subspace_lut.meta.json)
- 496 Wang orbit records parsed from `cert_matrix_q02_n333.pb.txt`.
- Expanded under 56,448 A-side actions (`GL(3,2) x GL(3,2)` plus transpose).
- Expanded LUT has 8,283,458 subspaces, exactly the Gaussian-binomial count for all subspaces of `F2^9`:
  - dim 0: 1
  - dim 1: 511
  - dim 2: 43,435
  - dim 3: 788,035
  - dim 4: 3,309,747
  - dim 5: 3,309,747
  - dim 6: 788,035
  - dim 7: 43,435
  - dim 8: 511
  - dim 9: 1
- `coverage_ok = true` and `conflict_count = 0`.
- One-dimensional T-level lower bounds: all 511 nonzero one-dimensional constraints have `LB=19`, split by matrix rank as rank-1:49, rank-2:294, rank-3:168.

Consistency test:

- The full cn122 rank-23 scheme at [scheme-47fa58e6cd.qmm](../../exact_baselines/results/cn122_3x3_r23_repro/scheme-47fa58e6cd.qmm) was checked against all 8,283,458 LUT constraints with `s=23`.
- It has 23 A-factors, 20 distinct, max multiplicity 2, zero violations.  This is the automatic guard that caught previous semantic errors.

## T-level rank-20 lazy capacity solve

Script: `wang_capacity_lazy.py`.

Background task: `s7_t6_tool1`.

Command:

```bash
python scripts/wang_capacity_lazy.py --solve-t 20 --max-iters 80 --solver-time 180 --check-cn122
```

Result file: [t_level_capacity_s20_lazy.json](../results/wang_capacity/t_level_capacity_s20_lazy.json).

Observed state:

- Started with all dim-1 and dim-2 constraints: 511 + 43,435 = 43,946 cuts.
- Iteration 1 candidate: 20 distinct points, 36,954 subset spans, 12,539 violated Wang constraints; added 5,000 cuts.
- Iteration 2: 6,339 violations; added 5,000 cuts.
- Iteration 3: 2,510 violations; added 2,510 cuts.
- Iteration 4: 1,736 violations; added 1,736 cuts.
- Iteration 5: 961 violations; added 961 cuts.
- Iteration 6: CP-SAT returned `UNKNOWN` after 181 s with 59,153 total cuts.

Interpretation: no feasible T-level rank-20 A-factor support has been found, but no infeasibility proof has been obtained.  The run provides strong separation data: surviving candidate supports still violate higher-dimensional Wang constraints, mainly in dimensions 4-7 with lower bounds 12-17.  The exact finite problem remains open.

An enhanced T-level run with all dim<=3 cuts and all violated cuts per iteration was submitted as background task `s7_t12_tool1` writing to `data/wang_capacity_dim3_s20/`; its result was still pending when this note was written.

## Core-level rank-19 lazy capacity tests

Script: [core_capacity_from_wang_lut.py](../code/core_capacity_from_wang_lut.py).

Command run:

```bash
python scripts/core_capacity_from_wang_lut.py --check-cn122 --solve --core all --rank 19 --max-iters 30 --solver-time 60
```

Result files:

- [cn122_core_capacity_checks.json](../../exact_baselines/results/core_capacity/cn122_core_capacity_checks.json)
- [core_capacity_E11_s19.json](../results/core_capacity/core_capacity_E11_s19.json)
- [core_capacity_E12_E21_s19.json](../results/core_capacity/core_capacity_E12_E21_s19.json)
- [core_capacity_E13_E22_E31_s19.json](../results/core_capacity/core_capacity_E13_E22_E31_s19.json)
- [core_capacity_summary.json](../results/core_capacity/core_capacity_summary.json)

cn122 quotient consistency:

- E11 restriction: length 21, 18 distinct A-factors, max multiplicity 2, zero capacity violations.
- E12+E21 restriction: length 23, 19 distinct A-factors, max multiplicity 2, zero violations.
- E13+E22+E31 restriction: length 23, 20 distinct A-factors, max multiplicity 2, zero violations.

Lazy core `s=19` statuses:

- E11: after all dim-1/dim-2 cuts and 7 lazy candidate rounds, final CP-SAT status `UNKNOWN` at 13,900 cuts.  Last solved candidate had support 18, total multiplicity 19, max multiplicity 2, and still 54 violated subset-span constraints.
- E12+E21: final status `UNKNOWN` at 12,672 cuts.  Last solved candidate had 19 distinct points and still 198 violated constraints.
- E13+E22+E31: final status `UNKNOWN` at 12,864 cuts.  Last solved candidate had 19 distinct points and still 298 violated constraints.

Interpretation: the complete Wang occupation table has not yet produced a core rank-19 exclusion, but every candidate encountered so far violates higher-dimensional constraints.  No core-level feasible A support has yet been certified.

## Additional Core Constructions

Exact rank-21 pools were obtained for all three codimension-one cores:

- H3/E13+E22+E31 now has verified rank-21 pools; together with E11 and E12+E21, all three cores have explicit `F2` rank `<=21` schemes.
- This rules out the simple route of proving full rank 23 by showing one of these cores has rank at least 22.
- In sampled rank-21 pools, E11 and H3 have exact two-deletion deficiency-one near misses precisely when the two deleted terms have identical W-factor masks.  Counts: E11 815 such pairs; H3 626 such pairs; E12+E21 sampled schemes have no identical W masks and no deficiency-one two-deletions.
- A repaired exact quotient two-replacement search over all 815 E11 near misses tested 139,365 17-column bases and found no repair by two arbitrary rank-one 8x9 columns.  This is strong local negative evidence, not a global lower bound.

## Research state after these computations

The strongest finite-field lower-bound computation is now the full T-level `s=20` capacity problem.  Its infeasibility would prove `R_F2(T_<3,3,3>) >= 21`.  The three core `s=19` problems remain valuable because infeasibility would rule out rank-19 core decompositions and because any feasible A-support would reduce the rank-19 core search to a small B/C-only problem.  Current lazy solves have not settled either the T-level or core capacity systems.
