#!/usr/bin/env python3
"""analysis: Check peer's Wang-admissible rank-2 support against:
1. DC-lift constraints (from full tensor graph families)
2. Full lift-bit feasibility (all WANG512 rows)

The peer found support [1,3,9,33,99,128,132,144,148,160,184,189,192,198,209,215,224,249,254]
that passes all 417,197 rank-2 quotient Wang rows. But our DC constraints
derive from the full tensor's graph structure and may reject it.
"""
from __future__ import annotations
import json, struct, time, hashlib
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path('research/research_record')
WANG512 = Path('data/wang_native/full_tensor/full_wang512_cap5_len20_all_dim3.bin')
DC_BIN = ROOT / 'workspace/data/quotient_lift/rank2_dc_lift_rows.bin'
OUTDIR = ROOT / 'workspace/data/quotient_lift'

PIVOT = 17  # rank-2 pivot

# Peer's Wang-admissible support (quotient point indices, 1-based)
PEER_SUPPORT = [1,3,9,33,99,128,132,144,148,160,184,189,192,198,209,215,224,249,254]

def lift0(p, pivot):
    h = (pivot & -pivot).bit_length() - 1
    low = p & ((1 << h) - 1)
    high = (p >> h) << (h + 1)
    return low | high

def check_dc_constraints():
    """Check the support against DC-lift rows."""
    # Build support mask (0-indexed bits: point p -> bit p-1)
    support_mask = 0
    for p in PEER_SUPPORT:
        support_mask |= 1 << (p - 1)
    
    violations = []
    with open(DC_BIN, 'rb') as f:
        magic = f.read(8); assert magic == b'E11WANG1'
        n = struct.unpack('<I', f.read(4))[0]
        for idx in range(n):
            cap = struct.unpack('<B', f.read(1))[0]
            dim = struct.unpack('<B', f.read(1))[0]
            _res = struct.unpack('<H', f.read(2))[0]
            words = list(struct.unpack('<4Q', f.read(32)))
            row_mask = 0
            for w_idx, w in enumerate(words):
                row_mask |= w << (64 * w_idx)
            
            overlap = support_mask & row_mask
            occ = bin(overlap).count('1')
            if occ > cap:
                pts_in = sorted([b+1 for b in range(255) if (overlap >> b) & 1])
                row_pts = sorted([b+1 for b in range(255) if (row_mask >> b) & 1])
                violations.append({
                    'row_idx': idx, 'cap': cap, 'dim': dim,
                    'occupation': occ, 'excess': occ - cap,
                    'points_in_row': row_pts,
                    'points_selected': pts_in,
                })
    
    return n, violations

def check_lift_bit_feasibility():
    """Check full lift-bit feasibility using WANG512 rows."""
    pivot = PIVOT
    lifts = [(p, lift0(p, pivot), lift0(p, pivot) ^ pivot) for p in range(1, 256)]
    
    support_set = set(PEER_SUPPORT)
    support_mask = 0
    for p in PEER_SUPPORT:
        support_mask |= 1 << (p - 1)
    
    # Index support points
    support_list = sorted(PEER_SUPPORT)
    n_pts = len(support_list)
    pt_to_idx = {p: i for i, p in enumerate(support_list)}
    
    # Collect constraints
    quotient_violations = 0
    lift_constraints = []  # (agree0_local, agree1_local, cap) for each non-q row
    
    with open(WANG512, 'rb') as f:
        magic = f.read(8); assert magic == b'WANG512\x01'
        n = struct.unpack('<I', f.read(4))[0]
        for idx in range(n):
            cap = struct.unpack('<B', f.read(1))[0]
            dim = struct.unpack('<B', f.read(1))[0]
            _res = struct.unpack('<H', f.read(2))[0]
            words = list(struct.unpack('<8Q', f.read(64)))
            
            def bit(ws, p): return (ws[p >> 6] >> (p & 63)) & 1
            
            cq = bool(bit(words, pivot))
            
            if cq:
                # Quotient occupation: count support points in pi(W)
                count = 0
                for p, a0, a1 in lifts:
                    if p in support_set:
                        if bit(words, a0) or bit(words, a1):
                            count += 1
                if count + 1 > cap:  # +1 for q itself
                    quotient_violations += 1
                continue
            
            # Non-q row: lift-bit constraint
            ag0_local = 0  # bitmask over support indices where lift0 in W
            ag1_local = 0  # bitmask where lift1 in W
            for p, a0, a1 in lifts:
                if p not in support_set:
                    continue
                idx_p = pt_to_idx[p]
                if bit(words, a0):
                    ag0_local |= 1 << idx_p
                if bit(words, a1):
                    ag1_local |= 1 << idx_p
            
            active = ag0_local | ag1_local
            k = bin(active).count('1')
            if k == 0:
                continue
            
            k0 = bin(ag0_local & active).count('1')
            threshold = k0 - cap
            
            if threshold > n_pts:  # impossible
                pass
            
            if threshold > 0 or k > cap:  # non-trivial constraint
                lift_constraints.append((ag0_local, ag1_local, cap, k))
    
    # Now solve the lift-bit system using CP-SAT
    from ortools.sat.python import cp_model
    
    model = cp_model.CpModel()
    eps = [model.NewBoolVar(f'e{support_list[i]}') for i in range(n_pts)]
    
    n_active = 0
    n_trivial = 0
    
    for ag0_local, ag1_local, cap, k in lift_constraints:
        active = ag0_local | ag1_local
        k0 = bin(ag0_local & active).count('1')
        threshold = k0 - cap
        
        if threshold <= -(k):
            n_trivial += 1
            continue
        
        n_active += 1
        
        # Build: sum of eps[i] for i in agree0 - sum of eps[i] for i in agree1 >= threshold
        pos_vars = []
        neg_vars = []
        tmp = ag0_local
        while tmp:
            b = tmp & (-tmp)
            pos_vars.append(eps[b.bit_length() - 1])
            tmp ^= b
        tmp = ag1_local
        while tmp:
            b = tmp & (-tmp)
            neg_vars.append(eps[b.bit_length() - 1])
            tmp ^= b
        
        model.Add(sum(pos_vars) - sum(neg_vars) >= threshold)
    
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 120
    status = solver.Solve(model)
    
    feasible = status in (cp_model.OPTIMAL, cp_model.FEASIBLE)
    
    result = {
        'feasible': feasible,
        'status': solver.StatusName(status),
        'quotient_violations': quotient_violations,
        'total_lift_constraints': len(lift_constraints),
        'active_constraints': n_active,
        'trivial_constraints': n_trivial,
    }
    
    if feasible:
        sol = {support_list[i]: solver.Value(eps[i]) for i in range(n_pts)}
        result['lift_bits'] = sol
    
    return result

def main():
    t0 = time.time()
    
    print("Checking peer's Wang-admissible rank-2 support:")
    print(f"  Support: {PEER_SUPPORT}")
    print(f"  Size: {len(PEER_SUPPORT)}")
    
    # Check DC constraints
    print("\n1. DC-lift constraints check...")
    n_dc_rows, dc_violations = check_dc_constraints()
    print(f"  Total DC rows: {n_dc_rows}")
    print(f"  Violations: {len(dc_violations)}")
    if dc_violations:
        for v in dc_violations[:10]:
            print(f"    Row {v['row_idx']}: cap={v['cap']}, occ={v['occupation']}, "
                  f"excess={v['excess']}, selected={v['points_selected']}")
    
    # Check lift-bit feasibility
    print("\n2. Full lift-bit feasibility check...")
    lift_result = check_lift_bit_feasibility()
    print(f"  Quotient violations: {lift_result['quotient_violations']}")
    print(f"  Active lift constraints: {lift_result['active_constraints']}")
    print(f"  Feasible: {lift_result['feasible']}")
    print(f"  Status: {lift_result['status']}")
    if lift_result['feasible']:
        print(f"  Lift bits: {lift_result.get('lift_bits', 'N/A')}")
    
    results = {
        'schema': 's0908_peer_support_check_v1',
        'support': PEER_SUPPORT,
        'pivot': PIVOT,
        'dc_check': {
            'total_rows': n_dc_rows,
            'violations': dc_violations,
        },
        'lift_bit_check': lift_result,
        'elapsed_sec': time.time() - t0,
    }
    
    out_path = OUTDIR / 'peer_support_check.json'
    out_path.write_text(json.dumps(results, indent=2, default=str) + '\n')
    print(f"\nSaved to {out_path}")

if __name__ == '__main__':
    main()
