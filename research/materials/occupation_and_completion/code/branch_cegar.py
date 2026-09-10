#!/usr/bin/env python3
"""analysis: branch-specific quotient-Wang CEGAR for rank-2 and rank-3.

Finds a fully Wang-admissible 19-support within a specific branch (force/forbid).
Uses all rows from the peer binary for verification, with incremental CEGAR.

Usage:
  python branch_cegar.py --pivot rank2 --branch 1 [--timeout 120]
"""
import argparse, json, struct, time, sys
from pathlib import Path
from ortools.sat.python import cp_model

ROOT = Path('research/research_record/workspace')
BRANCH_SPECS = ROOT / 'data/quotient_branches/corrected_branch_specs.json'

def load_rows(pivot_name):
    """Load all quotient Wang rows from peer binary (6-byte records)."""
    p = Path(f'data/wang_native/quotient_binaries/{pivot_name}_all_n19.bin')
    data = p.read_bytes()
    rows = []
    for off in range(0, len(data) - 5, 6):
        mask = int.from_bytes(data[off:off+4], 'little')
        cap  = int.from_bytes(data[off+4:off+6], 'little')
        rows.append((mask, cap))
    return rows, str(p)

def cegar(rows, force, forbid, target=19, timeout=120, max_rounds=30):
    """CEGAR: find fully admissible support or prove infeasibility at current rows."""
    # Split by initial cap
    active = [(m, c) for m, c in rows if c <= 3]
    pool   = [(m, c) for m, c in rows if c > 3]
    pool_set = set(pool)
    
    for rnd in range(max_rounds):
        model = cp_model.CpModel()
        x = {p: model.NewBoolVar(f'x{p}') for p in range(1, 256)}
        for p in force: model.Add(x[p] == 1)
        for p in forbid: model.Add(x[p] == 0)
        model.Add(sum(x[p] for p in range(1, 256)) == target)
        
        for mask, cap in active:
            pts = [p for p in range(1, 256) if mask & (1 << p)]
            if pts:
                model.Add(sum(x[p] for p in pts) <= cap)
        
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = timeout
        solver.parameters.random_seed = rnd * 31 + 7
        status = solver.Solve(model)
        sname = {0:'UNKNOWN',1:'MODEL_INVALID',2:'FEASIBLE',3:'INFEASIBLE',4:'OPTIMAL'}.get(status, str(status))
        
        if sname == 'INFEASIBLE':
            return None, {'status':'INFEASIBLE','rounds':rnd+1,'active_rows':len(active)}
        if sname == 'UNKNOWN':
            return None, {'status':'UNKNOWN','rounds':rnd+1,'active_rows':len(active)}
        
        supp = sorted(p for p in range(1,256) if solver.Value(x[p]))
        smask = sum(1<<p for p in supp)
        
        viols = [(m,c) for m,c in pool_set if bin(smask & m).count('1') > c]
        if not viols:
            return supp, {'status':'ADMISSIBLE','rounds':rnd+1,'active_rows':len(active),'violations':0}
        
        active.extend(viols)
        pool_set -= set(viols)
        print(f"  round {rnd}: violations={len(viols)}, active={len(active)}", flush=True)
    
    return None, {'status':'MAX_ROUNDS','rounds':max_rounds,'active_rows':len(active)}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pivot', required=True, choices=['rank2','rank3'])
    ap.add_argument('--branch', type=int, required=True)
    ap.add_argument('--timeout', type=int, default=120)
    args = ap.parse_args()
    
    specs = json.loads(BRANCH_SPECS.read_text())
    bl = specs['pivots'][args.pivot]['branches']
    br = next((b for b in bl if b['branch'] == args.branch), None)
    if br is None:
        print(f"Branch {args.branch} not found", file=sys.stderr); sys.exit(1)
    
    print(f"=== {args.pivot} branch {args.branch} ===", flush=True)
    print(f"  force={br['force']}, forbid_count={len(br['forbid'])}", flush=True)
    
    t0 = time.time()
    rows, rpath = load_rows(args.pivot)
    print(f"  loaded {len(rows)} rows from {rpath}", flush=True)
    
    supp, info = cegar(rows, set(br['force']), set(br['forbid']), timeout=args.timeout)
    elapsed = time.time() - t0
    
    out = {
        'pivot_name': args.pivot, 'branch': args.branch,
        'force': br['force'], 'forbid': br['forbid'],
        'rows_path': rpath, 'rows_count': len(rows),
        'cegar': info,
        'support': supp,
        'elapsed_sec': elapsed,
    }
    
    odir = ROOT / 'data/quotient_lift/branch_lift'
    odir.mkdir(parents=True, exist_ok=True)
    opath = odir / f'{args.pivot}_branch{args.branch}_cegar.json'
    opath.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps(out, indent=2, sort_keys=True), flush=True)
    print(f'saved {opath}', flush=True)

if __name__ == '__main__':
    main()
