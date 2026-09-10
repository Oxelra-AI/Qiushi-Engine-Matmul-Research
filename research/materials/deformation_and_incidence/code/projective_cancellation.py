#!/usr/bin/env python3
"""Projective uv-column normalization and w-absorption analysis.

Implements the prescription:
1. For each term k, normalize the uv column by a nonvanishing coordinate
2. Absorb the scale into the w factor: w̃_k = w_k * (scale)
3. Study the limits of both normalized uv directions and absorbed w factors
4. If terms 10 and 17 converge to the same projective uv direction,
   the near-dependence is a cancellation degeneration: the limit
   is a border-rank phenomenon, not a finite-parameter rank reduction.
"""
import json, sys
import numpy as np
from pathlib import Path

def load_continuation(path):
    d = json.loads(Path(path).read_text())
    pts = d['continuation_results']
    ts = np.array([p['t'] for p in pts])
    xs = np.array([p['x'] for p in pts if 'x' in p])
    return d, ts, xs

def projective_normalization_analysis(ts, xs, r=23):
    """For each term, normalize its u⊗v by one coordinate and absorb into w."""
    n_pts = len(ts)
    
    # Focus on terms 10 and 17 (the near-dependent pair)
    target_terms = [10, 17]
    
    # For each term, compute the outer product u_k ⊗ v_k (81-dimensional)
    uv_directions = {}  # term -> list of normalized uv columns per t
    w_absorbed = {}     # term -> list of absorbed w vectors per t
    
    for k in target_terms:
        uv_directions[k] = []
        w_absorbed[k] = []
    
    for i in range(n_pts):
        for k in target_terms:
            u = xs[i, 27*k:27*k+9]
            v = xs[i, 27*k+9:27*k+18]
            w = xs[i, 27*k+18:27*k+27]
            
            uv = np.outer(u, v).ravel()  # 81-dimensional
            
            # Find the coordinate with largest absolute value for normalization
            pivot_idx = np.argmax(np.abs(uv))
            pivot_val = uv[pivot_idx]
            
            if abs(pivot_val) > 1e-15:
                uv_normalized = uv / pivot_val  # normalize so pivot coordinate = 1
                w_abs = w * pivot_val  # absorb the scale
            else:
                uv_normalized = uv
                w_abs = w
            
            uv_directions[k].append(uv_normalized)
            w_absorbed[k].append(w_abs)
    
    uv_directions = {k: np.array(v) for k, v in uv_directions.items()}
    w_absorbed = {k: np.array(v) for k, v in w_absorbed.items()}
    
    return uv_directions, w_absorbed

def analyze_convergence(ts, uv_dirs, w_abs, target_terms=[10, 17]):
    """Check if the two terms converge in the projective uv direction."""
    n_pts = len(ts)
    
    results = {}
    
    # 1. Relative change in uv direction (should stabilize if converging)
    for k in target_terms:
        diffs = []
        for i in range(1, n_pts):
            diff = np.linalg.norm(uv_dirs[k][i] - uv_dirs[k][i-1])
            diffs.append(float(diff))
        results[f'uv_direction_change_term_{k}'] = diffs
    
    # 2. Distance between the two uv directions (should → 0 for cancellation)
    angular_dists = []
    for i in range(n_pts):
        d1 = uv_dirs[target_terms[0]][i]
        d2 = uv_dirs[target_terms[1]][i]
        # Relative distance normalized by norms
        n1 = np.linalg.norm(d1)
        n2 = np.linalg.norm(d2)
        if n1 > 1e-15 and n2 > 1e-15:
            # Try both orientations (sign ambiguity)
            dist_plus = np.linalg.norm(d1/n1 - d2/n2)
            dist_minus = np.linalg.norm(d1/n1 + d2/n2)
            angular_dist = min(dist_plus, dist_minus)
            sign_match = 'same' if dist_plus < dist_minus else 'opposite'
        else:
            angular_dist = float('inf')
            sign_match = 'unknown'
        angular_dists.append({
            't': float(ts[i]),
            'angular_distance': float(angular_dist),
            'sign_alignment': sign_match,
            'raw_distance': float(np.linalg.norm(d1 - d2)),
            'norm_10': float(n1),
            'norm_17': float(n2)
        })
    results['angular_distance_evolution'] = angular_dists
    
    # 3. W-factor analysis: absorbed w vectors
    w_analysis = {}
    for k in target_terms:
        w_norms = [float(np.linalg.norm(w_abs[k][i])) for i in range(n_pts)]
        w_analysis[f'w_absorbed_norms_term_{k}'] = list(zip([float(t) for t in ts], w_norms))
    
    # 4. Check the difference w_10 - w_17 (or w_10 + w_17 depending on sign)
    w_sum_norms = []
    w_diff_norms = []
    for i in range(n_pts):
        w10 = w_abs[target_terms[0]][i]
        w17 = w_abs[target_terms[1]][i]
        w_sum_norms.append(float(np.linalg.norm(w10 + w17)))
        w_diff_norms.append(float(np.linalg.norm(w10 - w17)))
    w_analysis['w_sum_norms'] = list(zip([float(t) for t in ts], w_sum_norms))
    w_analysis['w_diff_norms'] = list(zip([float(t) for t in ts], w_diff_norms))
    results['w_analysis'] = w_analysis
    
    # 5. Laurent fit of the projective uv direction in s=1/t
    mask = ts >= 5
    ss = 1.0 / ts[mask]
    for k in target_terms:
        uv_fit = uv_dirs[k][mask]
        A = np.column_stack([np.ones_like(ss), ss, ss**2])
        limits = np.zeros(81)
        residuals = np.zeros(81)
        for j in range(81):
            coef, _, _, _ = np.linalg.lstsq(A, uv_fit[:, j], rcond=None)
            limits[j] = coef[0]
            pred = A @ coef
            residuals[j] = np.sqrt(np.mean((uv_fit[:, j] - pred)**2))
        results[f'uv_limit_term_{k}'] = {
            'limit_norm': float(np.linalg.norm(limits)),
            'residual_rms': float(np.sqrt(np.mean(residuals**2))),
            'max_residual': float(np.max(residuals)),
            'limit_vector': limits.tolist()
        }
    
    # 6. Compare the two limit uv directions
    lim_10 = np.array(results[f'uv_limit_term_{target_terms[0]}']['limit_vector'])
    lim_17 = np.array(results[f'uv_limit_term_{target_terms[1]}']['limit_vector'])
    n10 = np.linalg.norm(lim_10)
    n17 = np.linalg.norm(lim_17)
    if n10 > 1e-10 and n17 > 1e-10:
        cos_plus = float(np.dot(lim_10, lim_17) / (n10 * n17))
        dist_proj = min(np.linalg.norm(lim_10/n10 - lim_17/n17),
                       np.linalg.norm(lim_10/n10 + lim_17/n17))
    else:
        cos_plus = float('nan')
        dist_proj = float('nan')
    
    results['limit_comparison'] = {
        'cosine_similarity': cos_plus,
        'projective_distance': float(dist_proj),
        'norm_10': float(n10),
        'norm_17': float(n17),
    }
    
    # 7. Laurent fit for w_absorbed 
    for k in target_terms:
        w_fit = w_abs[k][mask]
        A = np.column_stack([np.ones_like(ss), ss, ss**2])
        w_limits = np.zeros(9)
        w_lin = np.zeros(9)
        w_residuals = np.zeros(9)
        for j in range(9):
            coef, _, _, _ = np.linalg.lstsq(A, w_fit[:, j], rcond=None)
            w_limits[j] = coef[0]
            w_lin[j] = coef[1]
            pred = A @ coef
            w_residuals[j] = np.sqrt(np.mean((w_fit[:, j] - pred)**2))
        results[f'w_absorbed_limit_term_{k}'] = {
            'limit_vector': w_limits.tolist(),
            'linear_term': w_lin.tolist(),
            'limit_norm': float(np.linalg.norm(w_limits)),
            'linear_norm': float(np.linalg.norm(w_lin)),
            'residual_rms': float(np.sqrt(np.mean(w_residuals**2))),
            'max_residual': float(np.max(w_residuals)),
        }
    
    # 8. Decisive test: fit absorbed w to a Laurent expansion in s=1/t
    # If w_absorbed ~ C_0 + C_1/t + ... with C_0 divergent, it's cancellation
    # Better: fit x(t) directly for the raw u,v,w of terms 10,17
    for k in target_terms:
        raw_u = xs_global[mask, 27*k:27*k+9]  
        raw_v = xs_global[mask, 27*k+9:27*k+18]
        raw_w = xs_global[mask, 27*k+18:27*k+27]
        
        # Fit u(s) = u_{-1}/s + u_0 + u_1*s + ...  (Laurent with possible pole)
        # First check: does a polynomial in 1/t fit better than polynomial in t?
        inv_ts = 1.0 / ts[mask]
        
        # Test: fit u_j(t) = a_0 + a_1*t + a_2*t^2
        # vs u_j(t) = b_0 + b_1*t  (linear in t → divergent)
        A_lin = np.column_stack([np.ones_like(ts[mask]), ts[mask]])
        u_growth_rates = []
        for j in range(9):
            coef_lin, _, _, _ = np.linalg.lstsq(A_lin, raw_u[:, j], rcond=None)
            u_growth_rates.append(float(coef_lin[1]))  # slope in t
        v_growth_rates = []
        for j in range(9):
            coef_lin, _, _, _ = np.linalg.lstsq(A_lin, raw_v[:, j], rcond=None)
            v_growth_rates.append(float(coef_lin[1]))
        w_growth_rates = []
        for j in range(9):
            coef_lin, _, _, _ = np.linalg.lstsq(A_lin, raw_w[:, j], rcond=None)
            w_growth_rates.append(float(coef_lin[1]))
        
        results[f'raw_growth_rates_term_{k}'] = {
            'u_linear_slopes': u_growth_rates,
            'v_linear_slopes': v_growth_rates,
            'w_linear_slopes': w_growth_rates,
            'u_max_slope': float(np.max(np.abs(u_growth_rates))),
            'v_max_slope': float(np.max(np.abs(v_growth_rates))),
            'w_max_slope': float(np.max(np.abs(w_growth_rates))),
        }
    
    return results

# Global variable for raw xs access in the convergence analysis
xs_global = None

def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('continuation_json')
    ap.add_argument('--json-out', required=True)
    args = ap.parse_args()
    
    global xs_global
    d, ts, xs = load_continuation(args.continuation_json)
    xs_global = xs
    
    uv_dirs, w_abs = projective_normalization_analysis(ts, xs)
    results = analyze_convergence(ts, uv_dirs, w_abs)
    
    # Print key findings
    print("=== Projective UV Direction Convergence ===")
    for ad in results['angular_distance_evolution']:
        if ad['t'] in [1, 5, 10, 20, 30, 45, 60]:
            print(f"  t={ad['t']:5.0f}: angular_dist={ad['angular_distance']:.8f}  sign={ad['sign_alignment']}")
    
    print(f"\n=== Limit Comparison ===")
    lc = results['limit_comparison']
    print(f"  Cosine similarity: {lc['cosine_similarity']:.10f}")
    print(f"  Projective distance: {lc['projective_distance']:.10f}")
    
    print(f"\n=== W-Absorbed Limit Norms ===")
    for k in [10, 17]:
        wl = results[f'w_absorbed_limit_term_{k}']
        print(f"  Term {k}: limit_norm={wl['limit_norm']:.4f}, linear_norm={wl['linear_norm']:.4f}, residual={wl['residual_rms']:.6f}")
    
    print(f"\n=== Raw Growth Rates (linear slopes in t) ===")
    for k in [10, 17]:
        rg = results[f'raw_growth_rates_term_{k}']
        print(f"  Term {k}: max |u_slope|={rg['u_max_slope']:.6f}, "
              f"max |v_slope|={rg['v_max_slope']:.6f}, "
              f"max |w_slope|={rg['w_max_slope']:.6f}")
    
    # Check: w_sum vs w_diff norms
    wa = results['w_analysis']
    print(f"\n=== W-Absorbed Sum/Diff Norms (last 5 points) ===")
    for (t1, sn), (t2, dn) in zip(wa['w_sum_norms'][-5:], wa['w_diff_norms'][-5:]):
        print(f"  t={t1:5.0f}: |w10+w17|={sn:.4f}, |w10-w17|={dn:.4f}")
    
    # Determine cancellation degeneration verdict
    ad_last = results['angular_distance_evolution'][-1]
    ad_mid = results['angular_distance_evolution'][len(results['angular_distance_evolution'])//2]
    
    is_converging = ad_last['angular_distance'] < ad_mid['angular_distance'] * 0.5
    limit_cos = abs(lc['cosine_similarity'])
    
    if limit_cos > 0.999 and is_converging:
        verdict = "CANCELLATION DEGENERATION CONFIRMED: terms 10 and 17 converge to the same projective uv direction as t→∞. The boundary is at infinity; σ_min→0 reflects a border-rank phenomenon, not a finite-parameter rank reduction. The absorbed w-factors diverge to compensate."
    elif limit_cos > 0.99:
        verdict = "STRONG EVIDENCE of cancellation degeneration: uv directions nearly identical in the limit."
    elif is_converging:
        verdict = "Convergence observed but limit projective distance still measurable."
    else:
        verdict = "No clear cancellation degeneration detected."
    
    results['cancellation_verdict'] = verdict
    print(f"\n=== VERDICT: {verdict} ===")
    
    Path(args.json_out).write_text(json.dumps(results, indent=2) + '\n')
    print(f"\nWrote {args.json_out}")

if __name__ == '__main__':
    main()
