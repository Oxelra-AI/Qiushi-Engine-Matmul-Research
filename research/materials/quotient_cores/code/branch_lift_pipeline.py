#!/usr/bin/env python3
"""analysis: branch-specific quotient-Wang survivor finding + lift-bit feasibility testing.

For a given rank-2 or rank-3 branch, finds a fully Wang-admissible 19-support via
CEGAR within the branch constraints (force/forbid), then immediately tests its 
full all-Wang lift-bit feasibility.

Usage:
  python branch_lift_pipeline.py --pivot rank2 --branch 1 [--timeout 120]
"""
import argparse, json, pickle, hashlib, time, sys
from pathlib import Path
from ortools.sat.python import cp_model

ROOT = Path('research/research_record/workspace')
BRANCH_SPECS = ROOT / 'data/quotient_branches/corrected_branch_specs.json'
LUT_PATH = Path('data/wang_f2_lb20/wang_subspace_lut.pkl')
PIVOT_MAP = {'rank2': 17, 'rank3': 273}

def load_quotient_rows(pivot_name):
    """Load all quotient Wang rows from native binary."""
    # Use the peer's all-n19 binary
    bin_path = Path(f'data/wang_native/quotient_binaries/{pivot_name}_all_n19.bin')
    if not bin_path.exists():
        # Fall back to local cap5
        bin_path = ROOT / f'data/quotient_dfs/{pivot_name}_cap5_n19.bin'
    import struct
    data = bin_path.read_bytes()
    rows = []
    off = 0
    while off + 6 <= len(data):
        mask = int.from_bytes(data[off:off+4], 'little')
        cap = int.from_bytes(data[off+4:off+6], 'little')
        rows.append((mask, cap))
        off += 6
    return rows, str(bin_path)

def cegar_branch_support(rows, branch_spec, timeout=120, initial_cap=3):
    """CEGAR loop to find a fully Wang-admissible support in a specific branch."""
    force = set(branch_spec['force'])
    forbid = set(branch_spec['forbid'])
    target = 19
    
    # Sort by cap for CEGAR ordering
    active_rows = [(m, c) for m, c in rows if c <= initial_cap]
    remaining_rows = [(m, c) for m, c in rows if c > initial_cap]
    
    for round_num in range(20):
        model = cp_model.CpModel()
        x = {p: model.NewBoolVar(f'x{p}') for p in range(1, 256)}
        
        # Force/forbid
        for p in force:
            model.Add(x[p] == 1)
        for p in forbid:
            model.Add(x[p] == 0)
        
        # Sum = target
        model.Add(sum(x[p] for p in range(1, 256)) == target)
        
        # Active rows
        for mask, cap in active_rows:
            pts = [p for p in range(1, 256) if mask & (1 << p)]
            if pts:
                model.Add(sum(x[p] for p in pts) <= cap)
        
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = timeout
        solver.parameters.random_seed = round_num * 17 + 42
        
        status = solver.Solve(model)
        status_name = {0:'UNKNOWN', 1:'MODEL_INVALID', 2:'FEASIBLE', 3:'INFEASIBLE', 4:'OPTIMAL'}
        sn = status_name.get(status, str(status))
        
        if sn in ('INFEASIBLE',):
            return None, {'status': 'INFEASIBLE', 'rounds': round_num + 1,
                         'active_rows': len(active_rows)}
        if sn in ('UNKNOWN',):
            return None, {'status': 'UNKNOWN', 'rounds': round_num + 1,
                         'active_rows': len(active_rows)}
        
        supp = sorted(p for p in range(1, 256) if solver.Value(x[p]) == 1)
        supp_mask = sum(1 << p for p in supp)
        
        # Check against ALL rows
        violations = []
        for mask, cap in remaining_rows:
            occ = bin(supp_mask & mask).count('1')
            if occ > cap:
                violations.append((mask, cap))
        
        if not violations:
            return supp, {'status': 'ADMISSIBLE', 'rounds': round_num + 1,
                         'active_rows': len(active_rows), 'violations': 0}
        
        active_rows.extend(violations)
        remaining_rows = [(m, c) for m, c in remaining_rows if (m, c) not in set(violations)]
        print(f"  round {round_num}: supp_size={len(supp)}, violations={len(violations)}, "
              f"active={len(active_rows)}", flush=True)
    
    return None, {'status': 'MAX_ROUNDS', 'rounds': 20, 'active_rows': len(active_rows)}

def build_section(pivot):
    """Build the high-pivot-bit section s: quotient -> full."""
    N = 9
    high_bit = pivot.bit_length() - 1
    section = {}
    for p in range(1, 1 << N):
        if p & (1 << high_bit):
            continue
        bits = []
        for b in range(N):
            if b == high_bit:
                continue
            if p & (1 << b):
                bits.append(b)
        full = 0
        for b in bits:
            full |= (1 << b)
        section[p] = full
    return section

def test_lift_feasibility(support, pivot, pivot_name):
    """Test full all-Wang lift-bit feasibility for the support."""
    lut = pickle.loads(LUT_PATH.read_bytes())
    section = build_section(pivot)
    
    N = 9
    total = (1 << N) - 1  # 511
    support_set = set(support)
    
    # Build lift-bit constraints from all Wang rows
    constraints = []
    for basis_tuple, lb in lut.items():
        cap = (1 << N) - lb  # cap for n=20 decomposition: 20 - lb is the generic cap
        # Wait, need to check semantics. For a length-20 decomposition,
        # |S ∩ W| ≤ 20 - lb(W) where lb is the lower bound from the Wang row.
        # The LUT stores (basis, lb) where lb = L(W).
        cap20 = 20 - lb
        if cap20 < 0 or cap20 >= 20:
            continue
        
        # Build subspace W from basis
        basis = list(basis_tuple)
        dim = len(basis)
        W = set()
        for mask in range(1 << dim):
            v = 0
            for i in range(dim):
                if mask & (1 << i):
                    v ^= basis[i]
            if v != 0:
                W.add(v)
        
        # Check if pivot q is in W
        if pivot in W:
            # q-containing row: occupation constraint on quotient points is standard
            # Already captured by quotient Wang rows
            continue
        
        # q-avoiding row: lift-bit constraint
        # For each quotient point p in support, s(p) or s(p)+q is the full point
        # Constraint: sum_{p: s(p) in W} (1-eps_p) + sum_{p: s(p)+q in W} eps_p <= cap20
        # Equivalently: sum_{p: s(p) in W} + sum_{p in support} eps_p * (1_{s(p)+q in W} - 1_{s(p) in W}) <= cap20
        
        eps0_active = []  # points where s(p) ∈ W  (contributes when eps=0, i.e. y0)
        eps1_active = []  # points where s(p)+q ∈ W (contributes when eps=1, i.e. y1)
        
        for p in support:
            sp = section.get(p)
            if sp is None:
                continue
            spq = sp ^ pivot
            if sp in W:
                eps0_active.append(p)
            if spq in W:
                eps1_active.append(p)
        
        total_active = len(set(eps0_active) | set(eps1_active))
        if total_active == 0:
            continue
        
        # The base contribution (eps=0 for all) = len(eps0_active)
        # Each eps_p=1 adds (1 if s(p)+q in W else 0) - (1 if s(p) in W else 0)
        base = len(eps0_active)
        
        # Deduplicate by (frozenset(eps0), frozenset(eps1), cap)
        key = (frozenset(eps0_active), frozenset(eps1_active), cap20)
        constraints.append((eps0_active, eps1_active, cap20, base))
    
    # Deduplicate
    seen = set()
    unique = []
    for e0, e1, cap, base in constraints:
        k = (frozenset(e0), frozenset(e1), cap)
        if k not in seen:
            seen.add(k)
            # Check if tautological: max possible LHS = |e0 ∪ e1| (all selected)
            # Actually, these are support-specific: all points in support are selected
            # LHS = |{p in e0: eps_p=0}| + |{p in e1: eps_p=1}|
            # We need to check over all 2^|support| assignments
            unique.append((list(set(e0)), list(set(e1)), cap))
    
    # Use exact DFS over lift assignments
    n = len(support)
    idx_map = {p: i for i, p in enumerate(support)}
    
    # Convert constraints to index-based
    idx_constraints = []
    for e0, e1, cap in unique:
        e0_idx = [idx_map[p] for p in e0 if p in idx_map]
        e1_idx = [idx_map[p] for p in e1 if p in idx_map]
        if not e0_idx and not e1_idx:
            continue
        # Tautological check: max LHS when all eps=0 is len(e0_idx), all eps=1 is len(e1_idx)
        # Actual max LHS = for each point, max contribution
        max_lhs = 0
        for i in range(n):
            c0 = 1 if i in set(e0_idx) else 0
            c1 = 1 if i in set(e1_idx) else 0
            max_lhs += max(c0, c1)
        if max_lhs <= cap:
            continue
        idx_constraints.append((e0_idx, e1_idx, cap))
    
    # Quick CP-SAT check first
    model = cp_model.CpModel()
    eps = [model.NewBoolVar(f'e{i}') for i in range(n)]
    
    for e0_idx, e1_idx, cap in idx_constraints:
        terms = []
        for i in e0_idx:
            terms.append(1 - eps[i])  # contributes when eps=0
        for i in e1_idx:
            terms.append(eps[i])       # contributes when eps=1
        # Actually need to express this properly
        # sum_{i in e0} (1 - eps_i) + sum_{i in e1} eps_i <= cap
        # = |e0| + sum_{i in e1} eps_i - sum_{i in e0} eps_i <= cap
        # = sum_{i in e1\e0} eps_i - sum_{i in e0\e1} eps_i <= cap - |e0|
        e0_set = set(e0_idx)
        e1_set = set(e1_idx)
        both = e0_set & e1_set
        only0 = e0_set - e1_set
        only1 = e1_set - e0_set
        # LHS = |both| + sum_{only0} (1-eps) + sum_{only1} eps
        # = |both| + |only0| - sum_{only0} eps + sum_{only1} eps
        # <= cap
        # => sum_{only1} eps - sum_{only0} eps <= cap - |both| - |only0|
        rhs = cap - len(both) - len(only0)
        expr = sum(eps[i] for i in only1) - sum(eps[i] for i in only0)
        model.Add(expr <= rhs)
    
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 60
    status = solver.Solve(model)
    status_name = {0:'UNKNOWN', 1:'MODEL_INVALID', 2:'FEASIBLE', 3:'INFEASIBLE', 4:'OPTIMAL'}
    
    feasible = status_name.get(status, str(status)) in ('FEASIBLE', 'OPTIMAL')
    
    return {
        'support': support,
        'pivot': pivot,
        'pivot_name': pivot_name,
        'unique_constraints': len(idx_constraints),
        'total_scanned': len(constraints),
        'cpsat_status': status_name.get(status, str(status)),
        'feasible': feasible,
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pivot', required=True, choices=['rank2', 'rank3'])
    ap.add_argument('--branch', type=int, required=True)
    ap.add_argument('--timeout', type=int, default=120)
    args = ap.parse_args()
    
    pivot = PIVOT_MAP[args.pivot]
    specs = json.loads(BRANCH_SPECS.read_text())
    branch_list = specs['pivots'][args.pivot]['branches']
    
    br_spec = None
    for b in branch_list:
        if b['branch'] == args.branch:
            br_spec = b
            break
    if br_spec is None:
        print(f"Branch {args.branch} not found for {args.pivot}", file=sys.stderr)
        sys.exit(1)
    
    print(f"=== {args.pivot} branch {args.branch} ===", flush=True)
    print(f"  force={br_spec['force']}, forbid_count={len(br_spec['forbid'])}", flush=True)
    
    t0 = time.time()
    
    # analysis: Find Wang-admissible support
    print("analysis: CEGAR for Wang-admissible support...", flush=True)
    rows, rows_path = load_quotient_rows(args.pivot)
    supp, cegar_info = cegar_branch_support(rows, br_spec, timeout=args.timeout)
    
    if supp is None:
        out = {
            'pivot_name': args.pivot, 'branch': args.branch,
            'cegar_result': cegar_info, 'survivor_found': False,
            'elapsed_sec': time.time() - t0,
        }
        out_path = ROOT / f'data/quotient_lift/branch_lift/{args.pivot}_branch{args.branch}_pipeline.json'
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
        print(json.dumps(out, indent=2, sort_keys=True), flush=True)
        print(f'saved {out_path}', flush=True)
        return
    
    print(f"  Found support: {supp}", flush=True)
    
    # analysis: Test lift-bit feasibility
    print("analysis: Testing all-Wang lift-bit feasibility...", flush=True)
    lift_result = test_lift_feasibility(supp, pivot, args.pivot)
    
    out = {
        'pivot_name': args.pivot, 'branch': args.branch,
        'cegar_result': cegar_info, 'survivor_found': True,
        'support': supp,
        'lift_result': lift_result,
        'elapsed_sec': time.time() - t0,
    }
    
    out_path = ROOT / f'data/quotient_lift/branch_lift/{args.pivot}_branch{args.branch}_pipeline.json'
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps(out, indent=2, sort_keys=True), flush=True)
    print(f'saved {out_path}', flush=True)

if __name__ == '__main__':
    main()
