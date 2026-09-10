# Iterative Model-Driven Separation and Matching Proof Architecture

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Key Innovation This ARTIFACT

Built `iterative_separation.py`: iterative model-driven separation with
direct encoding (no auxiliary variables for most at-most constraints). This
replaces the failed analysis sequential-counter approach that timed out at
700-row/219K-variable CNFs.

### How It Works

For a fixed nonadjacent matching M of size k:
1. Build base CNF from residual-0 (vertex exclusion) and residual-1 (edge
   exclusion) Wang rows, plus exactly-target cardinality on survivors.
2. Solve with CaDiCaL → if UNSAT, verify with DRAT.
3. Decode SAT model → 20-point support.
4. Scan full Wang LUT for violated rows.
5. If no violations → LUT-admissible support found!
6. Add violated rows as at-most-r constraints using direct encoding
   (C(m,r+1) negated clauses, no auxiliary variables) where C(m,r+1) ≤ 20.
7. Repeat from analysis.

Each round adds ~500-1200 constraints, growing the CNF by ~5K-13K clauses.
Convergence typically takes 3-5 rounds for k=6-7, 4-6 rounds for k=5.

## Matching Strata Status

### Global Cover Structure
Every rank-20 F2 support either:
(A) Contains an adjacent rank-1 pair → rep2 branch (fixed {E11, E12})
(B) Has nonadjacent rank-1 points forming a matching → 38 matching strata (k=1..7)

### k=7: ALL 6 CLOSED (analysis)
- idx32, idx37: direct row violations
- idx33, idx34: clique-cover certificates
- idx35, idx36: graph-CNF + DRAT (strictly verified)
- Unified manifest: [k7_unified_manifest.json](../results/k7_manifest/k7_unified_manifest.json)

### k=6: 4/10 closed by clique covers (analysis), 6 UNRESOLVED → RUNNING
- Running as s31_t21_tool1 (old script, no at-most fix)
- Pilot idx25 CLOSED: 4 rounds, 37K clauses, DRAT verified
- NOTE: strata with 443 survivors may hit BAD_MODEL without at-most fix

### k=5: 0/10 closed by coloring → RUNNING
- Pilot idx12 CLOSED: 5 rounds, 55K clauses, DRAT verified
- Running as s31_t44_tool1 (small, ≤265 survivors) and s31_t45_tool1 (large, 448)
- All use fixed version with at-most-target constraint

### k=4: 0/7 closed → RUNNING as s31_t47_tool1
### k=3: 0/3 closed → RUNNING as s31_t48_tool1

### k=2 and k=1: NOT STARTED
- idx0 (k=1): 462 survivors, 5469 edges, target 19
- idx1 (k=2): 461 survivors, 12731 edges, target 18
- These are very hard: many survivors, high targets, few vertex exclusions

## Adjacent-Pair Branch (rep2)

Base graph for rep2 prefix {E11, E12}:
- 509 candidates (all nonzero masks except 1, 2)
- 0 vertex exclusions (max lb for rows containing both E11,E12 is only 17)
- 11,280 edges
- Target: 18
- This is much harder than matching strata

The max Wang lb for rows containing both E11 and E12 is only 17, so no single
Wang row kills the adjacent-pair prefix. The rep2 closure requires either:
1. Iterative separation with many rounds (potentially thousands)
2. A different proof technique (maybe from related analysis's span oracle or deformation)
3. Finding a LUT-admissible support and checking B/C factors

## Critical Open Questions

1. Will ALL matching strata (k=1..7) close? → Running
2. If yes, can rep2 be closed? → Not yet attempted at scale
3. If both close → R_F2(T) ≥ 21 (under the Wang LUT and multiplicity-free model)
4. Even R_F2 ≥ 21 only applies over F2, not characteristic zero
5. Need k=2 and k=1 which have 461-462 survivors

## Files

- [iterative_separation.py](../code/iterative_separation.py) — Main iterative solver
- [k7_manifest.py](../code/k7_manifest.py) — k=7 manifest builder
- [k7_unified_manifest.json](../results/k7_manifest/k7_unified_manifest.json) — k=7 proof manifest
- [summary.json](../results/separation/idx25_v3/summary.json) — k=6 pilot proof
- [summary.json](../results/separation/k5_idx12_v2/summary.json) — k=5 pilot proof
- `workspace/data/separation/k{6,5,4,3}_*/` — batch results (running)
