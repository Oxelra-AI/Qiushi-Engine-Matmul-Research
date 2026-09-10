#!/usr/bin/env python3
"""Stream DFS solutions (cap<=3) and check each against full Wang table.

Goal: determine the rejection rate of cap 4-8 constraints on cap≤3 survivors.
If rejection rate = 100%, the full Wang table excludes all rank-19 E11 supports.
"""
import json
import pickle
import sys
import time
from collections import defaultdict
from pathlib import Path

SCRIPTS_S04 = Path("scripts")
if str(SCRIPTS_S04) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_S04))

from wang_capacity_lazy import rref_basis, unpack_basis
from core_capacity_from_wang_lut import CoreQuotient, load_lut

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUTDIR = Path("data/ghw_singleton")
OUTDIR.mkdir(parents=True, exist_ok=True)

MASK9 = (1 << 9) - 1
N_COLS = 19


def key_contains_e11(key: int) -> bool:
    d = key & 0xF
    if d == 0:
        return False
    return (key >> (4 + 9 * (d - 1))) & MASK9 == 1


def build_constraint_tables(lut):
    """Build separate constraint tables for cap<=3 and cap 4-8."""
    cap3_table = []  # (cap, point_set)
    cap48_table = []  # (cap, point_set)
    point_to_cap3 = defaultdict(list)
    
    for key9, lb_val in lut.items():
        if not key_contains_e11(key9):
            continue
        
        cap = N_COLS - lb_val
        if cap >= N_COLS or cap < 0:
            continue
        
        dim9 = key9 & 0xF
        basis9 = list(unpack_basis(key9))
        basis8_raw = []
        for b in basis9:
            if b == 1:
                continue
            q = b
            if q & 1:
                q ^= 1
            q8 = 0
            for bit in range(1, 9):
                if (q >> bit) & 1:
                    q8 |= 1 << (bit - 1)
            basis8_raw.append(q8)
        
        if not basis8_raw:
            continue
        basis8 = rref_basis(basis8_raw, n=8)
        d = len(basis8)
        
        pts = set()
        for mask in range(1, 1 << d):
            v = 0
            for i in range(d):
                if (mask >> i) & 1:
                    v ^= basis8[i]
            if 0 < v <= 255:
                pts.add(v)
        
        if not pts:
            continue
        
        entry = (cap, frozenset(pts))
        if cap <= 3:
            idx = len(cap3_table)
            cap3_table.append(entry)
            for p in pts:
                point_to_cap3[p].append(idx)
        elif cap <= 8:
            cap48_table.append(entry)
    
    return cap3_table, cap48_table, dict(point_to_cap3)


def main():
    t0 = time.time()
    
    print("Loading Wang LUT...")
    lut, _ = load_lut(LUT_PATH)
    
    print("Building constraint tables...")
    cap3_table, cap48_table, point_to_cap3 = build_constraint_tables(lut)
    print(f"  Cap≤3: {len(cap3_table)} rows")
    print(f"  Cap 4-8: {len(cap48_table)} rows")
    print(f"  Build time: {time.time()-t0:.1f}s")
    
    # DFS with cap≤3 constraints, inline check against cap 4-8
    print(f"\nStreaming DFS (cap≤3 search, cap 4-8 filter, 120s limit)...")
    
    inside_count = [0] * len(cap3_table)
    total_cap3 = 0
    total_cap48_ok = 0
    total_cap48_fail = 0
    fail_by_cap = defaultdict(int)  # cap -> number of failures at that cap
    first_survivor = None
    
    chosen = []
    
    def check_cap48(support_set):
        """Check a support against cap 4-8 constraints."""
        for cap, pts in cap48_table:
            if len(support_set & pts) > cap:
                return False, cap
        return True, -1
    
    def dfs(min_col, depth):
        nonlocal total_cap3, total_cap48_ok, total_cap48_fail, first_survivor
        
        if time.time() - t0 > 120:
            return True
        
        if depth == N_COLS:
            total_cap3 += 1
            support_set = frozenset(chosen)
            ok, fail_cap = check_cap48(support_set)
            if ok:
                total_cap48_ok += 1
                if first_survivor is None:
                    first_survivor = list(chosen)
                    print(f"  *** SURVIVOR: {first_survivor}")
            else:
                total_cap48_fail += 1
                fail_by_cap[fail_cap] += 1
            
            if total_cap3 % 5000 == 0:
                print(f"  checked {total_cap3}: ok={total_cap48_ok} fail={total_cap48_fail}")
            return False
        
        remaining = N_COLS - depth
        
        for q in range(min_col, 256):
            if 255 - q + 1 < remaining:
                break
            
            violated = False
            updated = []
            for ri in point_to_cap3.get(q, []):
                inside_count[ri] += 1
                updated.append(ri)
                if inside_count[ri] > cap3_table[ri][0]:
                    violated = True
                    break
            
            if not violated:
                chosen.append(q)
                timeout = dfs(q + 1, depth + 1)
                chosen.pop()
                if timeout:
                    for ri in updated:
                        inside_count[ri] -= 1
                    return True
            
            for ri in updated:
                inside_count[ri] -= 1
        
        return False
    
    timeout = dfs(1, 0)
    elapsed = time.time() - t0
    
    print(f"\nResults after {elapsed:.1f}s:")
    print(f"  Cap≤3 solutions generated: {total_cap3}")
    print(f"  Pass cap 4-8: {total_cap48_ok}")
    print(f"  Fail cap 4-8: {total_cap48_fail}")
    print(f"  Rejection rate: {total_cap48_fail/(total_cap3 or 1)*100:.2f}%")
    print(f"  Fail by cap: {dict(sorted(fail_by_cap.items()))}")
    if first_survivor:
        print(f"  First survivor: {first_survivor}")
    
    output = {
        "cap3_solutions": total_cap3,
        "cap48_pass": total_cap48_ok,
        "cap48_fail": total_cap48_fail,
        "rejection_rate": total_cap48_fail / (total_cap3 or 1),
        "fail_by_cap": dict(sorted(fail_by_cap.items())),
        "first_survivor": first_survivor,
        "elapsed_sec": elapsed,
        "timeout": timeout,
    }
    
    outpath = OUTDIR / "cap3_stream_cap48_check.json"
    with open(outpath, "w") as f:
        json.dump(output, f, indent=2, sort_keys=True)
    print(f"Saved to {outpath}")


if __name__ == "__main__":
    main()
