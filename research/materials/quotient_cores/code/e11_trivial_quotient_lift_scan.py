#!/usr/bin/env python3
"""Scan orbit-representative prefix spans using trivial quotient CPDs.

For each 4D E11 A-prefix span whose quotient tensor has q nonzero entries with
q <= 15, use the coordinate q-term quotient CPD and run the exact general
coset-lift SAT with residual budget 19-q.  A SAT model verifies to E11 rank 19.
UNSAT only excludes that coordinate quotient scheme for that prefix orbit.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np

SCRIPTS = Path('scripts')
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

import e11_quotient_lift_general_sat as glift  # noqa: E402


def coordinate_scheme(Q: np.ndarray) -> np.ndarray:
    terms = []
    for a, b, c in np.argwhere(Q.astype(np.uint8) & 1):
        terms.extend([1 << int(a), 1 << int(b), 1 << int(c)])
    return np.array(terms, dtype=np.uint16)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--invariants', type=Path, default=Path('data/prefix_span_orbits/prefix_span_orbit_invariants.json'))
    ap.add_argument('--qnnz', type=int, default=15, help='test representatives with this quotient coordinate count; use -1 for all <=15')
    ap.add_argument('--max-reps', type=int, default=0)
    ap.add_argument('--timeout-per-rep', type=int, default=60)
    ap.add_argument('--threads', type=int, default=8)
    ap.add_argument('--out', type=Path, default=Path('data/trivial_quotient_lift_scan/q15_scan.json'))
    ap.add_argument('--keep-cnf', action='store_true')
    args = ap.parse_args()
    t0 = time.time()
    data = json.loads(args.invariants.read_text())
    # The head may be truncated in JSON only if top too small; use directly_testable head from file.
    reps = data['directly_testable_by_trivial_quotient_rank_le15_head']
    # If top did not include all directly testable reps, low_qnnz head with top large should be regenerated.
    if args.qnnz >= 0:
        reps = [r for r in reps if int(r['quotient_nnz']) == args.qnnz]
    else:
        reps = [r for r in reps if int(r['quotient_nnz']) <= 15]
    if args.max_reps > 0:
        reps = reps[:args.max_reps]
    core = glift.build_e11_core()
    records = []
    first_witness = None
    for pos, r in enumerate(reps):
        prefix = [int(x) for x in r['basis']]
        ann = glift.annihilator_basis(prefix, 8)
        Q = glift.quotient_core(core, ann)
        scheme = coordinate_scheme(Q)
        qrank = len(scheme) // 3
        if qrank != int(r['quotient_nnz']):
            raise RuntimeError(f'qrank mismatch for orbit {r["orbit_id"]}: {qrank} vs {r["quotient_nnz"]}')
        rank_res = 19 - qrank
        if rank_res < 0:
            continue
        meta, Rcoords, lifts, b_masks, c_masks, M_rows = glift.scheme_to_residual(core, prefix, scheme)
        rec = {
            'orbit_id': int(r['orbit_id']),
            'prefix_basis': prefix,
            'Wang_L': int(r['Wang_L']),
            'Wang_cap_at_rank19': int(r['Wang_cap_at_rank19']),
            'orbit_size': int(r['orbit_size']),
            'quotient_nnz_coordinate_rank': qrank,
            'residual_rank_budget': rank_res,
            'quotient_flattening_ranks': r['flattening_ranks'],
            **meta,
        }
        enc = glift.GeneralLiftSAT(Rcoords, M_rows, rank_res=rank_res)
        args.out.parent.mkdir(parents=True, exist_ok=True)
        cnf_path = args.out.parent / f'orbit{r["orbit_id"]}_q{qrank}_res{rank_res}.xor.cnf'
        enc.F.write_native(cnf_path, [
            'trivial quotient coordinate scheme general lift scan',
            f'orbit_id={r["orbit_id"]}',
            f'prefix={prefix}',
            f'qrank={qrank}',
            f'rank_res={rank_res}',
        ])
        solve = glift.solve_native(cnf_path, 'cryptominisat5', args.timeout_per_rep, args.threads)
        model = solve.pop('model', None)
        rec.update({
            'vars': enc.F.next - 1,
            'cnf_clauses': len(enc.F.cnf),
            'native_xor_clauses': len(enc.F.xors),
            'cnf_sha256': glift.sha256_file(cnf_path),
            'cnf_path': str(cnf_path) if args.keep_cnf else None,
            'solve': solve,
        })
        if solve.get('status') == 'SAT' and model:
            C, res_u4, res_v, res_w = enc.decode(model)
            e11_dec = glift.lift_to_full_e11(core, prefix, lifts, b_masks, c_masks, C, res_u4, res_v, res_w)
            rec['decoded_general_lift'] = {
                'correction_matrix_rows_k_cols_j': C.astype(int).tolist(),
                'residual_u_masks_in_V_coords': res_u4,
                'residual_v_masks': res_v,
                'residual_w_masks': res_w,
                'model_lit_count': len(model),
            }
            rec['e11_decomposition'] = e11_dec
            if e11_dec['e11_verified']:
                rec['t333_decomposition'] = glift.lift_e11_to_t333(e11_dec)
                first_witness = rec
        if not args.keep_cnf and cnf_path.exists() and solve.get('status') != 'SAT':
            cnf_path.unlink()
            rec['cnf_path'] = None
        records.append(rec)
        print(f"{pos+1}/{len(reps)} orbit {r['orbit_id']} q={qrank} res={rank_res}: {solve.get('status')} {solve.get('elapsed_sec'):.2f}s")
        if first_witness is not None:
            break
    counts = {}
    for r in records:
        st = r.get('solve', {}).get('status', 'UNKNOWN')
        counts[st] = counts.get(st, 0) + 1
    result = {
        'purpose': 'exact general coset lift scan for coordinate quotient schemes on low-qnnz 4D prefix-span orbits',
        'field': 'F2',
        'qnnz_filter': args.qnnz,
        'representatives_tested': len(records),
        'status_counts': counts,
        'witness_found': first_witness is not None,
        'first_witness': first_witness,
        'records': records,
        'meaning': 'SAT gives verified E11 rank <=19 and full T333 rank <=22 over F2. UNSAT excludes only the coordinate quotient CPD for that prefix orbit; UNKNOWN is no conclusion.',
        'elapsed_sec': time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True, default=int) + '\n')
    print(json.dumps({k: result[k] for k in ['representatives_tested','status_counts','witness_found','elapsed_sec']}, indent=2, sort_keys=True))
    print('wrote', args.out)


if __name__ == '__main__':
    main()
