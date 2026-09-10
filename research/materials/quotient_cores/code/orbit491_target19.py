#!/usr/bin/env python3
"""Long target-19 ladder sanity check for dim-2 orbit 491.

The theorem only needs target-18 infeasibility (raise LB from 18 to 19), but
feasibility at target 19 is a useful edge check for the independently rebuilt
node-local row system.  The 120s analysis all-orbit run left orbit 491 UNKNOWN.
"""
from __future__ import annotations
import json, pickle, sys, time
from pathlib import Path

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from dim2_independent_semantics import (LUT_PATH, CACHE_PATH, rref_ind, independent_rows, solve_cp, canonical_rows_digest)

OUT = Path("data/dim2_independent/orbit491_target19_long.json")


def main():
    with LUT_PATH.open('rb') as f:
        data = pickle.load(f)
    lut = data['lut'] if isinstance(data, dict) and 'lut' in data else data
    with CACHE_PATH.open('rb') as f:
        cache = pickle.load(f)
    orb = next(o for o in cache['orbits'] if int(o['cert_index']) == 491)
    W = rref_ind([int(x) for x in orb['basis']], 9)
    target = 19
    t0 = time.time()
    rows, meta = independent_rows(W, lut, target)
    sol = solve_cp(9-len(W), target, rows, timeout=1800.0, workers=16)
    rec = {
        'schema': 'orbit491_target19_long_v1',
        'cert_index': 491,
        'target': target,
        'W_basis': [int(x) for x in orb['basis']],
        'W_rref': list(W),
        'rows': len(rows),
        'row_digest': canonical_rows_digest(rows),
        'row_meta': meta,
        'solve': sol,
        'elapsed_total_sec': time.time() - t0,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(rec, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'out': str(OUT),
        'status': sol.get('status'),
        'feasible': sol.get('feasible'),
        'elapsed_sec': sol.get('elapsed_sec'),
        'nonzero_count': sol.get('nonzero_count'),
        'max_multiplicity': sol.get('max_multiplicity'),
        'violations_check': sol.get('violations_check'),
    }, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
