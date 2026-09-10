#!/usr/bin/env python3
"""analysis: CEGAR with cap<=5 initial rows and longer timeout for stubborn branches."""
import argparse, json, struct, time, sys
from pathlib import Path
from ortools.sat.python import cp_model

ROOT = Path('research/research_record/workspace')
BRANCH_SPECS = ROOT / 'data/quotient_branches/corrected_branch_specs.json'

def load_e11wang1(path):
    data = Path(path).read_bytes()
    assert data[:8] == b'E11WANG1', f"Bad magic: {data[:8]}"
    count = struct.unpack('<I', data[8:12])[0]
    assert len(data) == 12 + count * 36
    rows = []
    for i in range(count):
        off = 12 + i * 36
        cap = data[off]
        w0, w1, w2, w3 = struct.unpack('<QQQQ', data[off+4:off+36])
        mask = w0 | (w1 << 64) | (w2 << 128) | (w3 << 192)
        rows.append((mask, cap))
    return rows

def cegar(rows, force, forbid, target=19, timeout=300, initial_cap=5, max_rounds=40):
    active = [(m, c) for m, c in rows if c <= initial_cap]
    pool   = set((m, c) for m, c in rows if c > initial_cap)
    
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
        solver.parameters.random_seed = rnd * 41 + 13
        # Try different search strategies
        if rnd % 3 == 1:
            solver.parameters.search_branching = 1  # FIXED_SEARCH
        elif rnd % 3 == 2:
            solver.parameters.search_branching = 5  # PORTFOLIO_SEARCH
        
        status = solver.Solve(model)
        sname = {0:'UNKNOWN',1:'MODEL_INVALID',2:'FEASIBLE',3:'INFEASIBLE',4:'OPTIMAL'}.get(status, str(status))
        print(f"  round {rnd}: status={sname}, active={len(active)}", flush=True)
        
        if sname == 'INFEASIBLE':
            return None, {'status':'INFEASIBLE','rounds':rnd+1,'active_rows':len(active)}
        if sname == 'UNKNOWN':
            # Try one more round with what we have before giving up
            if rnd >= 2 and pool:
                # Add all remaining rows and try once more
                continue
            return None, {'status':'UNKNOWN','rounds':rnd+1,'active_rows':len(active)}
        
        supp = sorted(p for p in range(1,256) if solver.Value(x[p]))
        smask = sum(1<<p for p in supp)
        
        viols = [(m,c) for m,c in pool if bin(smask & m).count('1') > c]
        if not viols:
            return supp, {'status':'ADMISSIBLE','rounds':rnd+1,'active_rows':len(active),'violations':0}
        
        active.extend(viols)
        pool -= set(viols)
        print(f"  round {rnd}: found support, violations={len(viols)}", flush=True)
    
    return None, {'status':'MAX_ROUNDS','rounds':max_rounds,'active_rows':len(active)}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pivot', required=True, choices=['rank2','rank3'])
    ap.add_argument('--branch', type=int, required=True)
    ap.add_argument('--timeout', type=int, default=300)
    ap.add_argument('--initial-cap', type=int, default=5)
    args = ap.parse_args()
    
    specs = json.loads(BRANCH_SPECS.read_text())
    bl = specs['pivots'][args.pivot]['branches']
    br = next((b for b in bl if b['branch'] == args.branch), None)
    if br is None:
        print(f"Branch {args.branch} not found", file=sys.stderr); sys.exit(1)
    
    print(f"=== {args.pivot} branch {args.branch} (cap<={args.initial_cap}, timeout={args.timeout}s) ===", flush=True)
    print(f"  force={br['force']}, forbid_count={len(br['forbid'])}", flush=True)
    
    t0 = time.time()
    rpath = f"data/wang_native/quotient_binaries/{args.pivot}_all_n19.bin"
    rows = load_e11wang1(rpath)
    print(f"  loaded {len(rows)} rows from {rpath}", flush=True)
    
    supp, info = cegar(rows, set(br['force']), set(br['forbid']),
                       timeout=args.timeout, initial_cap=args.initial_cap)
    elapsed = time.time() - t0
    
    out = {
        'pivot_name': args.pivot, 'branch': args.branch,
        'force': br['force'], 'forbid': br['forbid'],
        'rows_count': len(rows), 'initial_cap': args.initial_cap,
        'cegar': info, 'support': supp, 'elapsed_sec': elapsed,
        'format': 'E11WANG1_corrected',
    }
    
    opath = ROOT / f'data/quotient_lift/branch_lift/{args.pivot}_branch{args.branch}_cegar_cap{args.initial_cap}_t{args.timeout}.json'
    opath.parent.mkdir(parents=True, exist_ok=True)
    opath.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps(out, indent=2, sort_keys=True), flush=True)
    print(f'saved {opath}', flush=True)

if __name__ == '__main__':
    main()
