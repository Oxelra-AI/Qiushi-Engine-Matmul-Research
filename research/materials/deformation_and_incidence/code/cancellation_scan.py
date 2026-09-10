#!/usr/bin/env python3
"""Quick cancellation scan: test multiple continuation directions for cancellation.

For each liftable direction from the serendipitous scan, do a short continuation
(to t=20), check whether a projective pair-merging pattern emerges.

This tests whether cancellation degeneration is generic for the serendipitous family,
or specific to the ranked:0 direction.
"""
import json, sys, os
import numpy as np
from pathlib import Path
from scipy.optimize import least_squares

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from formal_lift_pairing import (
    parse_qmm, terms_to_vec, tensor_value, build_jacobian, build_rescalings,
    build_stabilizer_pullback, matrix_rank_svd, projective_pairing_stats,
    eval_truncated_path, formal_lift, bilinear_Q
)

def setup_local(scheme):
    Sobj = parse_qmm(scheme)
    r = Sobj['rank']; x0 = terms_to_vec(Sobj['terms']); target = tensor_value(x0, r)
    J0 = build_jacobian(x0, r)
    U, S, Vt = np.linalg.svd(J0, full_matrices=True)
    jrank = int(np.sum(S > 1e-10)); kernel = Vt[jrank:].T; left_null = U[:, jrank:]
    R = build_rescalings(x0, r); G = build_stabilizer_pullback(x0, r)
    sym = np.hstack([R, G])
    Usym, Ssym, _ = np.linalg.svd(sym, full_matrices=False)
    srank = int(np.sum(Ssym > 1e-10)); sym_basis = Usym[:, :srank]
    sym_in_kernel = kernel.T @ sym
    Uc, Sc, _ = np.linalg.svd(sym_in_kernel, full_matrices=True)
    qrank = int(np.sum(Sc > 1e-10)); residual_dirs = kernel @ Uc[:, qrank:]
    return Sobj, r, x0, target, J0, U, S, Vt, jrank, kernel, left_null, sym_basis, residual_dirs

def load_scan(scan_json):
    return json.loads(Path(scan_json).read_text())

def check_cancellation(x, r):
    """Check if any pair of terms has near-identical projective uv direction."""
    uv_cols = []
    for k in range(r):
        u = x[27*k:27*k+9]
        v = x[27*k+9:27*k+18]
        uv = np.outer(u, v).ravel()
        n = np.linalg.norm(uv)
        uv_cols.append(uv / max(n, 1e-15))
    
    # Find the closest pair
    best_cos = -1
    best_pair = None
    for i in range(r):
        for j in range(i+1, r):
            cos = abs(np.dot(uv_cols[i], uv_cols[j]))
            if cos > best_cos:
                best_cos = cos
                best_pair = (i, j)
    
    return best_cos, best_pair

def main():
    scheme = sys.argv[1]
    scan_json = sys.argv[2]
    json_out = sys.argv[3]
    
    Sobj, r, x0, target, J0, U, S, Vt, jrank, kernel, left_null, sym_basis, residual_dirs = setup_local(scheme)
    scan = load_scan(scan_json)
    
    liftable = scan.get('liftable_sorted_by_pairing_motion', [])
    print(f'Found {len(liftable)} liftable directions')
    
    t_values = [5.0, 10.0, 20.0]
    results = []
    
    for rank_idx in range(min(10, len(liftable))):
        rec = liftable[rank_idx]
        coords = np.array(rec['residual_coordinates'], dtype=float)
        x1 = residual_dirs @ coords
        x1 = x1 / np.linalg.norm(x1)
        
        # Quick formal lift
        coeffs, lift_info = formal_lift(x0, x1, J0, U, S, Vt, jrank, residual_dirs, kernel, left_null, r, 8)
        
        if not lift_info['status'].startswith('lifted'):
            results.append({'rank_idx': rank_idx, 'source_index': rec.get('index'), 'status': 'no_lift'})
            continue
        
        # Build continuation system
        nvar = len(x0)
        def fun(x, t):
            F = tensor_value(x, r) - target
            gauge = sym_basis.T @ (x - x0)
            arc = np.array([np.dot(x - x0, x1) - t])
            return np.concatenate([F, gauge, 10.0 * arc])
        
        def jac(x, t):
            J = build_jacobian(x, r)
            return np.vstack([J, sym_basis.T, 10.0 * x1.reshape(1, nvar)])
        
        point_results = []
        x_prev = x0.copy()
        success = True
        
        for t in t_values:
            x_init = eval_truncated_path(coeffs, t)
            if point_results and point_results[-1]['brent_res'] < 1e-8:
                x_init = x_prev + (t - point_results[-1]['t']) * x1
            
            res = least_squares(lambda x: fun(x, t), x_init, jac=lambda x: jac(x, t),
                               method='trf', x_scale='jac', ftol=1e-13, xtol=1e-13, gtol=1e-13,
                               max_nfev=300, verbose=0)
            x = res.x
            x_prev = x.copy()
            
            brent_res = float(np.linalg.norm(tensor_value(x, r) - target))
            best_cos, best_pair = check_cancellation(x, r)
            
            # Pairing singular values
            pair_stats = {}
            for p in ['uv', 'uw', 'vw']:
                ps = projective_pairing_stats(x, r, p)
                pair_stats[p] = float(ps['min_singular_col_normalized'])
            
            point_results.append({
                't': float(t),
                'brent_res': brent_res,
                'success': bool(res.success),
                'best_cos': float(best_cos),
                'best_pair': list(best_pair) if best_pair else None,
                'pairing_mins': pair_stats,
                'min_pairing': float(min(pair_stats.values())),
            })
            
            if brent_res > 1e-7:
                success = False
                break
        
        result = {
            'rank_idx': rank_idx,
            'source_index': rec.get('index'),
            'lift_status': lift_info['status'],
            'pairing_derivative': rec.get('most_negative_pairing_derivative'),
            'success': success,
            'points': point_results
        }
        
        if point_results:
            last = point_results[-1]
            result['final_min_pairing'] = last['min_pairing']
            result['final_best_cos'] = last['best_cos']
            result['final_best_pair'] = last['best_pair']
        
        results.append(result)
        
        if point_results:
            last = point_results[-1]
            print(f'  ranked:{rank_idx} (idx={rec.get("index")}): t={last["t"]:.0f} '
                  f'brent={last["brent_res"]:.2e} min_pair={last["min_pairing"]:.6f} '
                  f'cos={last["best_cos"]:.8f} pair={last["best_pair"]}')
    
    # Summary
    print('\n=== Summary ===')
    cancellation_count = 0
    for r_item in results:
        if r_item.get('final_best_cos', 0) > 0.99:
            cancellation_count += 1
    print(f'{cancellation_count}/{len(results)} directions show cancellation at t=20')
    
    out = {'scheme': scheme, 'scan_json': scan_json, 'results': results,
           'cancellation_fraction': cancellation_count / max(len(results), 1)}
    Path(json_out).write_text(json.dumps(out, indent=2) + '\n')
    print(f'Wrote {json_out}')

if __name__ == '__main__':
    main()
