#!/usr/bin/env python3
"""Verify the constraint projection: check that known rank-21 pool rows
satisfy all Wang constraints at s=21, and cross-check the 8-bit projection."""
import json, sys, time, numpy as np
from pathlib import Path

sys.path.insert(0, str(Path("scripts")))
from wang_capacity_lazy import rref_basis, unpack_basis
from core_capacity_from_wang_lut import CoreQuotient, load_lut, check_core_solution

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
MASK9 = (1 << 9) - 1

lut, _ = load_lut(LUT_PATH)
core = CoreQuotient(pivot=1)

pool = np.load("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy")
R = pool.shape[1] // 3  # 21

# Check first 5 rows using the existing check_core_solution function
for row_idx in range(5):
    row = pool[row_idx]
    sol = {}
    for t in range(R):
        u = int(row[3*t])
        q = core.project9(u)
        if q != 0:
            sol[q] = sol.get(q, 0) + 1
    
    violations, stats = check_core_solution(sol, 21, core, lut, max_report=5)
    print(f"Row {row_idx}: {len(sol)} distinct dirs, total mult={sum(sol.values())}, "
          f"violations={stats['violation_count']}")

# Now check: for a hypothetical rank-19 with distinct directions,
# does check_core_solution work correctly?
# Use 19 DISTINCT directions from row 0's directions + some extras
row = pool[0]
q_all = []
for t in range(R):
    u = int(row[3*t])
    q = core.project9(u)
    if q != 0:
        q_all.append(q)

distinct_q = sorted(set(q_all))
print(f"\nRow 0 has {len(distinct_q)} distinct nonzero quotient directions")

# Build a 19-point set: take all distinct + pad with unused points
used = set(distinct_q)
extra = [p for p in range(1, 256) if p not in used]
test_support = distinct_q + extra[:19 - len(distinct_q)]
assert len(test_support) == 19

sol19 = {q: 1 for q in test_support}
violations, stats = check_core_solution(sol19, 19, core, lut, max_report=10)
print(f"\nTest 19-point set ({len(distinct_q)} from pool + {19-len(distinct_q)} extra):")
print(f"  Violations: {stats['violation_count']}")
if violations:
    for v in violations[:5]:
        print(f"  dim8={v['dim8']}, lb={v['lb']}, cap={v['cap']}, occ={v['occupancy']}, excess={v['excess']}")

# Now verify our projection matches check_core_solution for a DFS solution
dfs_sol = [1, 2, 3, 4, 5, 8, 9, 16, 17, 26, 27, 32, 36, 64, 65, 108, 109, 128, 146]
sol_dfs = {q: 1 for q in dfs_sol}
violations, stats = check_core_solution(sol_dfs, 19, core, lut, max_report=10)
print(f"\nDFS solution [1,2,3,...,146] (first cap<=3 solution):")
print(f"  Violations: {stats['violation_count']}")
if violations:
    for v in violations[:5]:
        print(f"  dim8={v['dim8']}, lb={v['lb']}, cap={v['cap']}, occ={v['occupancy']}, excess={v['excess']}")
    print(f"  Violations by dim8: {stats.get('violations_by_dim8', {})}")
    print(f"  Violations by lb:   {stats.get('violations_by_lb', {})}")
