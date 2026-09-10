#!/usr/bin/env python3
"""analysis: CP-SAT assumption-core extraction plus DRAT replay for dim-2 raises.

This targets the quotient occupation subproblems for original-Wang-LUT dim-2
orbits.  The mathematical problem for a two-dimensional A-subspace W with old
node lower bound L=18 is the existence of nonnegative integer counts on the
2^7-1 quotient points with total L satisfying every induced Wang row
    sum_{q in row} x_q <= cap(row).
If this integer system is infeasible, quotienting a length-20 decomposition by
W would leave at most 18 terms, contradicting the node lower bound raised to 19.

OR-Tools CP-SAT can quickly prove the full system infeasible but its proof is
not independently checkable here.  We therefore ask CP-SAT only for an
assumption core: a subset of row constraints that CP-SAT says is infeasible.
We then encode that row subset as a plain occurrence-slot CNF and require
CaDiCaL+drat-trim to prove UNSAT.  The DRAT replay, not the CP-SAT core claim,
is the reusable proof object for the row subsystem.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

from ortools.sat.python import cp_model  # type: ignore
from pysat.card import CardEnc, EncType  # type: ignore
from pysat.formula import CNF  # type: ignore

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
import dim2_replay_compat_graph as dg  # type: ignore

DEFAULT_OUT = Path('data/dim2_assumption_core')


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def run_cmd(args: List[str], timeout: int) -> Dict:
    t0 = time.time()
    try:
        p = subprocess.run(args, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
        return {
            'args': args,
            'returncode': p.returncode,
            'stdout_tail': p.stdout[-6000:],
            'stderr_tail': p.stderr[-6000:],
            'elapsed_sec': time.time() - t0,
            'timeout': False,
        }
    except subprocess.TimeoutExpired as e:
        return {
            'args': args,
            'returncode': None,
            'stdout_tail': (e.stdout or '')[-6000:] if isinstance(e.stdout, str) else '',
            'stderr_tail': (e.stderr or '')[-6000:] if isinstance(e.stderr, str) else '',
            'elapsed_sec': time.time() - t0,
            'timeout': True,
        }


def solve_rows_with_assumptions(rows: Sequence[Tuple[int, int]], k: int, L: int, sec: float, workers: int) -> Dict:
    """Return CP-SAT status and a row-index core if the assumption API provides one."""
    npts = (1 << k) - 1
    model = cp_model.CpModel()
    xs = [model.NewIntVar(0, L, f'x_{i+1}') for i in range(npts)]
    model.Add(sum(xs) == L)
    assumps = []
    lit_to_row: Dict[int, int] = {}
    kept_rows = []
    for ridx, (mask, cap) in enumerate(rows):
        if cap >= L or mask == 0:
            continue
        pts = [i for i in range(npts) if (mask >> i) & 1]
        if not pts and cap >= 0:
            continue
        a = model.NewBoolVar(f'a_{ridx}')
        if cap < 0:
            model.Add(0 <= -1).OnlyEnforceIf(a)
        else:
            model.Add(sum(xs[i] for i in pts) <= int(cap)).OnlyEnforceIf(a)
        assumps.append(a)
        # The CpSolver returns integer literals; Index() is stable for positive literal.
        lit_to_row[a.Index()] = ridx
        kept_rows.append(ridx)
    # AddAssumptions exists in recent OR-Tools.  Fall back to AddAssumption loop if needed.
    if hasattr(model, 'AddAssumptions'):
        model.AddAssumptions(assumps)
    else:
        for a in assumps:
            model.AddAssumption(a)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(sec)
    solver.parameters.num_search_workers = int(workers)
    solver.parameters.random_seed = 9034
    t0 = time.time()
    st = solver.Solve(model)
    elapsed = time.time() - t0
    status = solver.StatusName(st)
    out = {
        'status': status,
        'elapsed_sec': elapsed,
        'branches': int(solver.NumBranches()),
        'conflicts': int(solver.NumConflicts()),
        'assumption_count': len(assumps),
        'feasible': None,
        'core_row_indices': [],
    }
    if st in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        out['feasible'] = True
        sol = [int(solver.Value(x)) for x in xs]
        out['nonzero_solution'] = [(i+1, v) for i, v in enumerate(sol) if v]
    elif st == cp_model.INFEASIBLE:
        out['feasible'] = False
        core_lits = list(solver.SufficientAssumptionsForInfeasibility())
        # returned literals may be signed; assumptions are positive BoolVars here.
        core_rows = []
        missing = []
        for lit in core_lits:
            key = abs(int(lit))
            if key in lit_to_row:
                core_rows.append(lit_to_row[key])
            elif int(lit) in lit_to_row:
                core_rows.append(lit_to_row[int(lit)])
            else:
                missing.append(int(lit))
        out['core_literal_count'] = len(core_lits)
        out['core_row_indices'] = sorted(set(core_rows))
        out['core_decode_missing_literals'] = missing[:20]
        out['core_decode_missing_count'] = len(missing)
    return out


def solve_plain_rows(rows: Sequence[Tuple[int, int]], k: int, L: int, sec: float, workers: int) -> Dict:
    npts = (1 << k) - 1
    model = cp_model.CpModel()
    xs = [model.NewIntVar(0, L, f'x_{i+1}') for i in range(npts)]
    model.Add(sum(xs) == L)
    for mask, cap in rows:
        pts = [i for i in range(npts) if (mask >> i) & 1]
        if cap < 0:
            model.Add(0 <= -1)
        elif pts and cap < L:
            model.Add(sum(xs[i] for i in pts) <= int(cap))
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(sec)
    solver.parameters.num_search_workers = int(workers)
    solver.parameters.random_seed = 1934
    t0 = time.time(); st = solver.Solve(model); elapsed = time.time() - t0
    out = {'status': solver.StatusName(st), 'elapsed_sec': elapsed, 'branches': int(solver.NumBranches()), 'conflicts': int(solver.NumConflicts())}
    if st in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        out['feasible'] = True
        sol = [int(solver.Value(x)) for x in xs]
        out['nonzero_solution'] = [(i+1, v) for i, v in enumerate(sol) if v]
    elif st == cp_model.INFEASIBLE:
        out['feasible'] = False
    else:
        out['feasible'] = None
    return out


def var_id(slot: int, point: int, npts: int) -> int:
    return slot * npts + point + 1


def encode_occurrence_cnf(rows: Sequence[Tuple[int, int]], k: int, L: int, path: Path) -> Dict:
    npts = (1 << k) - 1
    cnf = CNF()
    top = L * npts
    stats = {'slot_exactly_one_clauses': 0, 'row_constraints_encoded': 0, 'unit_forbidden_literals': 0}
    for s in range(L):
        lits = [var_id(s, p, npts) for p in range(npts)]
        cnf.append(lits); stats['slot_exactly_one_clauses'] += 1
        enc = CardEnc.atmost(lits=lits, bound=1, top_id=top, encoding=EncType.seqcounter)
        cnf.extend(enc.clauses); stats['slot_exactly_one_clauses'] += len(enc.clauses); top = enc.nv
    for mask, cap in rows:
        if cap >= L or mask == 0:
            continue
        lits = []
        for s in range(L):
            base = s * npts + 1
            for p in range(npts):
                if (mask >> p) & 1:
                    lits.append(base + p)
        if cap < 0:
            cnf.append([])
            stats['row_constraints_encoded'] += 1
        elif cap == 0:
            for lit in lits:
                cnf.append([-lit])
            stats['unit_forbidden_literals'] += len(lits)
            stats['row_constraints_encoded'] += 1
        elif cap < len(lits):
            enc = CardEnc.atmost(lits=lits, bound=int(cap), top_id=top, encoding=EncType.seqcounter)
            cnf.extend(enc.clauses); top = enc.nv
            stats['row_constraints_encoded'] += 1
    path.parent.mkdir(parents=True, exist_ok=True)
    cnf.to_file(str(path))
    stats.update({'vars': cnf.nv, 'clauses': len(cnf.clauses), 'npts': npts, 'slots': L, 'path': str(path)})
    return stats


def row_hash(rows: Sequence[Tuple[int,int]]) -> str:
    s = ';'.join(f'{int(m)}:{int(c)}' for m,c in rows)
    return hashlib.sha256(s.encode()).hexdigest()


def process_index(idx: int, outdir: Path, cp_sec: float, workers: int, shrink: bool, cnf: bool, cadical_timeout: int, drat_timeout: int) -> Dict:
    lut, cache = dg.load_lut_cache()
    raw_lbs = dg.orbit_lbs_from_cache(cache, {})
    profile = json.loads(dg.PROFILE.read_text())
    rec_by_idx = {int(r['index']): r for r in profile['dimension_2_orbits']}
    prec = rec_by_idx[idx]
    W = [int(x) for x in prec['constraint_values']]
    L = int(prec['rank_lower_bound'])
    k = 9 - len(dg.rref_basis(W, 9))
    rows, meta = dg.node_rows(W, lut, cache, raw_lbs, L)
    t0 = time.time()
    acore = solve_rows_with_assumptions(rows, k, L, cp_sec, workers)
    core_indices = list(acore.get('core_row_indices', []))
    core_rows = [rows[i] for i in core_indices]
    shrink_records = []
    if shrink and acore.get('feasible') is False and core_rows:
        # Greedy deletion shrink.  This is only to reduce the later CNF; DRAT proves final core.
        changed = True
        while changed:
            changed = False
            i = 0
            while i < len(core_rows):
                trial = core_rows[:i] + core_rows[i+1:]
                sol = solve_plain_rows(trial, k, L, min(cp_sec, 10.0), workers)
                if sol.get('feasible') is False:
                    removed = core_rows[i]
                    core_rows = trial
                    shrink_records.append({'removed_index': i, 'removed_row': {'mask': removed[0], 'cap': removed[1]}, 'remaining': len(core_rows), 'solve': sol})
                    changed = True
                else:
                    i += 1
            # Avoid pathological long shrinking; the first pass often suffices.
            if len(shrink_records) > 1000:
                break
    plain_core = None
    if core_rows:
        plain_core = solve_plain_rows(core_rows, k, L, cp_sec, workers)
    idxdir = outdir / f'orbit{idx}'
    idxdir.mkdir(parents=True, exist_ok=True)
    core_path = idxdir / f'orbit{idx}_assumption_core.json'
    out = {
        'schema': 's0908_dim2_assumption_core_v1',
        'meaning': 'CP-SAT assumption core for an original-LUT dim-2 occupation raise, followed when requested by independent occurrence-CNF DRAT replay.',
        'index': idx,
        'basis': W,
        'rank_pattern': [dg.rank3(x) for x in dg.nonzero_span(W)],
        'old_lb': L,
        'attempted_raise_to': L + 1,
        'quotient_dim': k,
        'full_row_count': len(rows),
        'full_row_meta': meta,
        'full_row_sha256': row_hash(rows),
        'assumption_solve': acore,
        'selected_core_row_count': len(core_rows),
        'selected_core_row_sha256': row_hash(core_rows),
        'selected_core_rows': [{'mask': int(m), 'cap': int(c), 'popcount': int(m).bit_count()} for m,c in core_rows],
        'plain_core_solve': plain_core,
        'shrink_records_head': shrink_records[:50],
        'shrink_removed_count': len(shrink_records),
        'elapsed_before_cnf_sec': time.time() - t0,
    }
    if cnf and plain_core and plain_core.get('feasible') is False:
        cnf_path = idxdir / f'orbit{idx}_assumption_core.cnf'
        drat_path = idxdir / f'orbit{idx}_assumption_core.drat'
        log_path = idxdir / f'orbit{idx}_proof_logs.json'
        cnf_meta = encode_occurrence_cnf(core_rows, k, L, cnf_path)
        cnf_meta['sha256'] = sha256(cnf_path)
        cad = run_cmd(['cadical', str(cnf_path), str(drat_path)], cadical_timeout)
        dr = None
        verified = False
        if cad['returncode'] == 20 and drat_path.exists():
            dr = run_cmd(['drat-trim', str(cnf_path), str(drat_path)], drat_timeout)
            verified = (dr['returncode'] == 0 and 's VERIFIED' in dr['stdout_tail'])
        log_path.write_text(json.dumps({'cadical': cad, 'drat_trim': dr}, indent=2, sort_keys=True) + '\n')
        out.update({
            'cnf_meta': cnf_meta,
            'cnf_path': str(cnf_path),
            'cnf_sha256': cnf_meta['sha256'],
            'drat_path': str(drat_path),
            'drat_sha256': sha256(drat_path) if drat_path.exists() else None,
            'cadical_returncode': cad['returncode'],
            'drat_returncode': None if dr is None else dr['returncode'],
            'drat_verified': verified,
            'proof_log_path': str(log_path),
        })
    out['elapsed_sec'] = time.time() - t0
    core_path.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    out['core_path'] = str(core_path)
    out['core_sha256'] = sha256(core_path)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--indices', default='484,485,486,487,488,489,490,491')
    ap.add_argument('--outdir', type=Path, default=DEFAULT_OUT)
    ap.add_argument('--cp-sec', type=float, default=60.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--shrink', action='store_true')
    ap.add_argument('--cnf', action='store_true')
    ap.add_argument('--cadical-timeout', type=int, default=300)
    ap.add_argument('--drat-timeout', type=int, default=300)
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    records = []
    for idx in [int(x) for x in args.indices.split(',') if x.strip()]:
        rec = process_index(idx, args.outdir, args.cp_sec, args.workers, args.shrink, args.cnf, args.cadical_timeout, args.drat_timeout)
        records.append({k: v for k, v in rec.items() if k not in ('selected_core_rows','full_row_meta','shrink_records_head')})
        print('orbit', idx, 'core_rows', rec['selected_core_row_count'], 'plain', None if rec['plain_core_solve'] is None else rec['plain_core_solve'].get('status'), 'drat', rec.get('drat_verified'), 'elapsed', rec['elapsed_sec'], flush=True)
    manifest = {
        'schema': 's0908_dim2_assumption_core_manifest_v1',
        'meaning': 'Per-orbit assumption-core and optional DRAT results for the eight dim-2 exclusions 484--491 now needed by the shortened saturated lower-bound route.',
        'records': records,
        'summary': {
            'total': len(records),
            'assumption_infeasible': [r['index'] for r in records if r['assumption_solve'].get('feasible') is False],
            'plain_core_infeasible': [r['index'] for r in records if r.get('plain_core_solve',{}).get('feasible') is False],
            'drat_verified': [r['index'] for r in records if r.get('drat_verified') is True],
        },
    }
    mpath = args.outdir / 'dim2_assumption_core_manifest.json'
    mpath.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status':'ok','manifest':str(mpath),'summary':manifest['summary']}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
