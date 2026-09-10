#!/usr/bin/env python3
"""analysis: branch-specific quotient-support CEGAR on a supplied E11WANG1 row table.

This is a proof-support and row-selection instrument.  Unlike the analysis
script, the row table is an argument, so locally tightened quotient tables can
be tested without changing the trusted native all-row files.  The row table may
contain ordinary Wang rows and compiled upper-bound rows that are valid under
the branch semantics used here.  A returned INFEASIBLE status from CP-SAT is a
solver result for the currently active rows, not by itself a replayable proof.
A returned ADMISSIBLE support is checked against the supplied complete row
table.  Violated rows are logged for focused propagation experiments.
"""
from __future__ import annotations
import argparse, hashlib, json, struct, time, sys
from collections import Counter
from pathlib import Path
from ortools.sat.python import cp_model

ROOT = Path('research/research_record')
SPECS = ROOT / 'workspace/data/quotient_branches/corrected_branch_specs.json'
MAGIC = b'E11WANG1'
REC = '<BBHQQQQ'
RECSZ = struct.calcsize(REC)

def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda: f.read(1 << 20), b''):
            h.update(c)
    return h.hexdigest()

def load_rows(path: Path):
    data = path.read_bytes()
    if data[:8] != MAGIC:
        raise ValueError(f'{path}: bad magic {data[:8]!r}')
    n = struct.unpack('<I', data[8:12])[0]
    if len(data) != 12 + n * RECSZ:
        raise ValueError(f'{path}: size mismatch {len(data)} vs {12+n*RECSZ}')
    rows = []
    hist = Counter(); dimhist = Counter()
    for idx in range(n):
        off = 12 + idx * RECSZ
        cap, dim, pad, w0, w1, w2, w3 = struct.unpack_from(REC, data, off)
        mask = int(w0) | (int(w1) << 64) | (int(w2) << 128) | (int(w3) << 192)
        rows.append({'idx': idx, 'cap': int(cap), 'dim': int(dim), 'mask': mask, 'popcount': mask.bit_count()})
        hist[int(cap)] += 1; dimhist[int(dim)] += 1
    return rows, {'path': str(path), 'sha256': sha(path), 'count': n, 'cap_hist': {str(k): int(v) for k,v in sorted(hist.items())}, 'dim_hist': {str(k): int(v) for k,v in sorted(dimhist.items())}}

def pts(mask: int):
    return [p for p in range(1, 256) if (mask >> p) & 1]

def solve_round(rows, active, force, forbid, target: int, time_limit: float, seed: int, workers: int):
    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f'x_{p}') for p in range(1, 256)}
    for p in force:
        model.Add(x[p] == 1)
    for p in forbid:
        model.Add(x[p] == 0)
    model.Add(sum(x[p] for p in range(1, 256)) == target)
    for idx in sorted(active):
        r = rows[idx]
        if r['cap'] < target:
            ps = pts(r['mask'])
            if ps:
                model.Add(sum(x[p] for p in ps) <= r['cap'])
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.num_search_workers = int(workers)
    solver.parameters.random_seed = int(seed)
    # Keep result reproducible enough for mining; this is not a proof certificate.
    t0 = time.time(); st = solver.Solve(model); elapsed = time.time() - t0
    rec = {
        'status': solver.StatusName(st),
        'solve_elapsed_sec': elapsed,
        'wall_time': solver.WallTime(),
        'conflicts': solver.NumConflicts(),
        'branches': solver.NumBranches(),
        'active_rows': len(active),
    }
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        rec['support'] = sorted(p for p in range(1, 256) if solver.Value(x[p]))
    return rec

def check_support(supp, rows):
    sm = 0
    for p in supp:
        sm |= 1 << p
    viol = []
    for r in rows:
        if r['cap'] <= 0 or r['cap'] >= len(supp):
            continue
        occ = (sm & r['mask']).bit_count()
        if occ > r['cap']:
            viol.append({'idx': r['idx'], 'cap': r['cap'], 'dim': r['dim'], 'occ': occ, 'excess': occ-r['cap'], 'popcount': r['popcount']})
    viol.sort(key=lambda v: (-v['excess'], v['cap'], -v['occ'], v['dim'], v['idx']))
    return viol

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pivot', required=True, choices=['rank2','rank3'])
    ap.add_argument('--branch', type=int, required=True)
    ap.add_argument('--rows', type=Path, required=True)
    ap.add_argument('--initial-cap', type=int, default=3)
    ap.add_argument('--target', type=int, default=19)
    ap.add_argument('--rounds', type=int, default=8)
    ap.add_argument('--time-per-round', type=float, default=120.0)
    ap.add_argument('--total-time', type=float, default=600.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--seed', type=int, default=27000)
    ap.add_argument('--label', required=True)
    ap.add_argument('--outdir', type=Path, default=ROOT/'workspace/data/quotient_lift/tightening')
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    specs = json.loads(SPECS.read_text())['pivots'][args.pivot]['branches']
    br = next((b for b in specs if int(b['branch']) == args.branch), None)
    if br is None:
        print(f'no branch {args.branch}', file=sys.stderr); sys.exit(2)
    rows, rowmeta = load_rows(args.rows)
    active = {r['idx'] for r in rows if 0 < r['cap'] <= args.initial_cap and r['cap'] < args.target}
    force = set(map(int, br['force'])); forbid = set(map(int, br['forbid']))
    t0 = time.time(); rounds = []
    print(f'{args.pivot} branch {args.branch}: rows={len(rows)} initial_active={len(active)} force={sorted(force)} forbid_count={len(forbid)} table_sha={rowmeta["sha256"]}', flush=True)
    for rnd in range(args.rounds):
        if time.time() - t0 >= args.total_time:
            break
        tl = min(args.time_per_round, args.total_time - (time.time() - t0))
        print(f'round {rnd}: active={len(active)} tl={tl:.1f}', flush=True)
        rec = solve_round(rows, active, force, forbid, args.target, tl, args.seed + 101*rnd, args.workers)
        if 'support' not in rec:
            rounds.append(rec)
            print(f'  {rec["status"]} no support', flush=True)
            break
        viol = check_support(rec['support'], rows)
        rec['violation_count'] = len(viol)
        rec['violation_cap_hist'] = {str(k): int(v) for k,v in sorted(Counter(vv['cap'] for vv in viol).items())}
        rec['violation_dim_hist'] = {str(k): int(v) for k,v in sorted(Counter(vv['dim'] for vv in viol).items())}
        rec['violation_excess_hist'] = {str(k): int(v) for k,v in sorted(Counter(vv['excess'] for vv in viol).items())}
        rec['violation_rows'] = [int(vv['idx']) for vv in viol]
        rec['violation_head'] = viol[:80]
        print(f'  {rec["status"]} qviol={len(viol)} cap_hist={rec["violation_cap_hist"]} supp={rec["support"]}', flush=True)
        rounds.append(rec)
        if not viol:
            rec['fully_admissible_for_supplied_rows'] = True
            break
        new = 0
        for vv in viol:
            if vv['idx'] not in active:
                active.add(vv['idx']); new += 1
        rec['new_rows_added'] = new
        if new == 0:
            break
    vc = Counter()
    for rr in rounds:
        for idx in rr.get('violation_rows', []):
            vc[int(idx)] += 1
    top = []
    for idx, cnt in vc.most_common(300):
        r = rows[idx]
        top.append({'idx': idx, 'count': cnt, 'cap': r['cap'], 'dim': r['dim'], 'popcount': r['popcount']})
    out = {
        'schema': 's0908_branch_cegar_custom_v1',
        'meaning': 'CEGAR over one corrected quotient-support row table and one corrected orbit branch. INFEASIBLE is a CP-SAT result for active rows; ADMISSIBLE means no violation of the supplied row table; UNKNOWN and timeouts are not exclusions.',
        'pivot': args.pivot,
        'branch': args.branch,
        'branch_force': sorted(force),
        'branch_forbid': sorted(forbid),
        'target': args.target,
        'initial_cap': args.initial_cap,
        'rows_meta': rowmeta,
        'rounds': rounds,
        'final_active_rows': len(active),
        'unique_violated_rows': len(vc),
        'top_violated_rows': top,
        'final_status': rounds[-1]['status'] if rounds else 'NO_ROUNDS',
        'found_fully_admissible': any(r.get('fully_admissible_for_supplied_rows') for r in rounds),
        'elapsed_sec': time.time() - t0,
    }
    op = args.outdir / f'{args.label}_{args.pivot}_branch{args.branch}_cegar.json'
    op.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print('saved', op, flush=True)
    print(json.dumps({'out': str(op), 'final_status': out['final_status'], 'rounds': len(rounds), 'found_fully_admissible': out['found_fully_admissible'], 'unique_violated_rows': out['unique_violated_rows'], 'final_active_rows': out['final_active_rows'], 'elapsed_sec': out['elapsed_sec']}, indent=2, sort_keys=True), flush=True)

if __name__ == '__main__':
    main()
