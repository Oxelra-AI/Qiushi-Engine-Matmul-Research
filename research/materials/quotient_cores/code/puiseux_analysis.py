#!/usr/bin/env python3
"""Laurent/Puiseux analysis of the serendipitous_8d34 continuation path.

Key question: does the path hit the pairing-defect boundary at finite t*,
or only at t→∞?

Strategy:
1. Fit σ_min(t) to power-law models: σ ~ C/t^α  (infinite boundary)
                                       σ ~ C*(t*-t)^β  (finite boundary)
2. Analyze individual factor entries u_i(t), v_i(t), w_i(t) in projective coordinates
3. Check if column norms of factors diverge (cancellation degeneration) or converge
4. Fit the 1/t Laurent expansion and check for finite-limit behavior

Output: JSON with fits, residuals, and diagnostic plots.
"""
import json, sys
import numpy as np
from pathlib import Path
from scipy.optimize import curve_fit, minimize_scalar, minimize

def load_continuation(path):
    d = json.loads(Path(path).read_text())
    pts = d['continuation_results']
    ts = np.array([p['t'] for p in pts])
    sigmas = np.array([p['solve']['min_projective_pairing_singular'] for p in pts])
    step_norms = np.array([p['solve']['step_norm_from_base'] for p in pts])
    brent_res = np.array([p['solve']['brent_residual_norm'] for p in pts])
    
    # Extract full solution vectors
    xs = []
    for p in pts:
        if 'x' in p:
            xs.append(np.array(p['x']))
    xs = np.array(xs)
    
    return d, ts, sigmas, step_norms, brent_res, xs

def fit_power_law_decay(ts, sigmas, t_min=5):
    """Fit σ_min(t) ~ C * t^(-α) for large t."""
    mask = ts >= t_min
    t_fit = ts[mask]
    s_fit = sigmas[mask]
    
    # log-log fit
    logt = np.log(t_fit)
    logs = np.log(s_fit)
    # Linear regression: log(σ) = log(C) - α*log(t)
    A = np.column_stack([np.ones_like(logt), logt])
    coef, res, _, _ = np.linalg.lstsq(A, logs, rcond=None)
    logC, neg_alpha = coef
    C = np.exp(logC)
    alpha = -neg_alpha
    
    # Compute R² and residuals
    s_pred = C * t_fit**(-alpha)
    ss_res = np.sum((s_fit - s_pred)**2)
    ss_tot = np.sum((s_fit - np.mean(s_fit))**2)
    R2 = 1 - ss_res/ss_tot
    
    return {'C': float(C), 'alpha': float(alpha), 'R2': float(R2),
            'residual_rms': float(np.sqrt(ss_res/len(s_fit))),
            'prediction_at_100': float(C * 100**(-alpha)),
            'prediction_at_1000': float(C * 1000**(-alpha)),
            'interpretation': 'σ_min ~ C*t^(-α): boundary at infinity' if alpha > 0 else 'non-decaying'}

def fit_finite_boundary(ts, sigmas, t_min=5):
    """Fit σ_min(t) ~ C*(t*-t)^β for some finite t*."""
    mask = ts >= t_min
    t_fit = ts[mask]
    s_fit = sigmas[mask]
    t_max = float(t_fit[-1])
    
    best_result = None
    best_ss = np.inf
    
    # Try various candidate t* values
    for t_star_cand in np.linspace(t_max*1.01, t_max*20, 200):
        try:
            # log(σ) = log(C) + β*log(t*-t)
            dt = t_star_cand - t_fit
            if np.any(dt <= 0):
                continue
            logdt = np.log(dt)
            logs = np.log(s_fit)
            A = np.column_stack([np.ones_like(logdt), logdt])
            coef, _, _, _ = np.linalg.lstsq(A, logs, rcond=None)
            logC, beta = coef
            C_val = np.exp(logC)
            s_pred = C_val * dt**beta
            ss = np.sum((s_fit - s_pred)**2)
            if ss < best_ss:
                best_ss = ss
                ss_tot = np.sum((s_fit - np.mean(s_fit))**2)
                best_result = {
                    't_star': float(t_star_cand),
                    'C': float(C_val),
                    'beta': float(beta),
                    'R2': float(1 - ss/ss_tot),
                    'residual_rms': float(np.sqrt(ss/len(s_fit)))
                }
        except Exception:
            pass
    
    if best_result:
        best_result['interpretation'] = f'σ_min ~ C*(t*-t)^β: boundary at t*={best_result["t_star"]:.2f}' if best_result['R2'] > 0.99 else 'poor fit to finite boundary model'
    return best_result

def fit_step_norm(ts, step_norms, t_min=5):
    """Fit step_norm(t) to understand path geometry."""
    mask = ts >= t_min
    t_fit = ts[mask]
    n_fit = step_norms[mask]
    
    # Linear fit: norm ~ a*t + b
    A = np.column_stack([t_fit, np.ones_like(t_fit)])
    coef_lin, res_lin, _, _ = np.linalg.lstsq(A, n_fit, rcond=None)
    a, b = coef_lin
    ss_res_lin = np.sum((n_fit - (a*t_fit + b))**2)
    ss_tot = np.sum((n_fit - np.mean(n_fit))**2)
    
    # Power-law fit: norm ~ C*t^α
    logt = np.log(t_fit)
    logn = np.log(n_fit)
    A2 = np.column_stack([np.ones_like(logt), logt])
    coef_pow, _, _, _ = np.linalg.lstsq(A2, logn, rcond=None)
    C_pow = np.exp(coef_pow[0])
    alpha_pow = coef_pow[1]
    
    return {
        'linear': {'a': float(a), 'b': float(b), 'R2': float(1 - ss_res_lin/ss_tot)},
        'power_law': {'C': float(C_pow), 'alpha': float(alpha_pow)},
        'interpretation': 'ARTIFACT norm grows roughly linearly in t' if abs(alpha_pow - 1) < 0.3 else f'ARTIFACT norm grows as t^{alpha_pow:.2f}'
    }

def analyze_factor_growth(ts, xs, r=23):
    """Analyze whether individual factor entries grow, and whether column norms diverge."""
    n_pts = len(ts)
    n_var = xs.shape[1]
    
    # Parse factors: x = [u0(9), v0(9), w0(9), u1(9), v1(9), w1(9), ...]
    # For rank r, term k: u_k = x[27k:27k+9], v_k = x[27k+9:27k+18], w_k = x[27k+18:27k+27]
    
    u_norms = np.zeros((n_pts, r))
    v_norms = np.zeros((n_pts, r))
    w_norms = np.zeros((n_pts, r))
    
    for i in range(n_pts):
        for k in range(r):
            u = xs[i, 27*k:27*k+9]
            v = xs[i, 27*k+9:27*k+18]
            w = xs[i, 27*k+18:27*k+27]
            u_norms[i, k] = np.linalg.norm(u)
            v_norms[i, k] = np.linalg.norm(v)
            w_norms[i, k] = np.linalg.norm(w)
    
    # Identify terms whose norms grow fastest
    growth_rates = []
    for k in range(r):
        for label, norms in [('u', u_norms[:, k]), ('v', v_norms[:, k]), ('w', w_norms[:, k])]:
            if ts[-1] > 0 and norms[-1] > 1e-10:
                ratio = norms[-1] / max(norms[0], 1e-10)
                growth_rates.append({
                    'term': k, 'factor': label,
                    'norm_first': float(norms[0]),
                    'norm_last': float(norms[-1]),
                    'growth_ratio': float(ratio)
                })
    
    growth_rates.sort(key=lambda x: -x['growth_ratio'])
    
    # Check for cancellation degeneration: if some terms grow while others shrink
    max_u_norm = np.max(u_norms, axis=1)
    max_v_norm = np.max(v_norms, axis=1)
    max_w_norm = np.max(w_norms, axis=1)
    
    # Compute product norms (the actual contribution of each term)
    product_norms = u_norms * v_norms * w_norms
    max_product = np.max(product_norms, axis=1)
    
    # Build uv pairing matrix at each t and find the near-dependent columns
    near_dep_info = []
    for i in range(n_pts):
        # uv pairing: 23 columns of length 81 (outer product u_k ⊗ v_k)
        uv_cols = []
        for k in range(r):
            u = xs[i, 27*k:27*k+9]
            v = xs[i, 27*k+9:27*k+18]
            uv_cols.append(np.outer(u, v).ravel())
        P = np.column_stack(uv_cols)
        # Column-normalize
        col_norms = np.linalg.norm(P, axis=0)
        col_norms[col_norms < 1e-15] = 1.0
        P_norm = P / col_norms
        U_svd, S_svd, Vt_svd = np.linalg.svd(P_norm, full_matrices=False)
        # Near-null vector
        null_vec = Vt_svd[-1]
        # Which columns contribute most to near-dependence?
        sorted_idx = np.argsort(-np.abs(null_vec))
        near_dep_info.append({
            't': float(ts[i]),
            'sigma_min': float(S_svd[-1]),
            'null_vector_top5': [(int(sorted_idx[j]), float(null_vec[sorted_idx[j]])) for j in range(5)],
            'null_vector_sparsity': float(np.sum(np.abs(null_vec) > 0.1)),
            'max_col_norm_uv': float(np.max(col_norms)),
            'min_col_norm_uv': float(np.min(col_norms)),
            'col_norm_ratio': float(np.max(col_norms) / max(np.min(col_norms), 1e-15))
        })
    
    return {
        'top_growing_factors': growth_rates[:10],
        'top_shrinking_factors': sorted(growth_rates, key=lambda x: x['growth_ratio'])[:10],
        'max_product_norm': [float(x) for x in max_product],
        'near_dependence_evolution': near_dep_info,
        'max_factor_growth_overall': float(growth_rates[0]['growth_ratio']) if growth_rates else 0.0,
    }

def laurent_expansion_in_s(ts, xs, r=23):
    """
    Set s = 1/t and study x(s) as s → 0.
    If the path has a finite limit x* = lim_{s→0} x(s), the boundary is at infinity.
    If the path diverges in specific components, identify the leading terms.
    """
    # Use only large-t points for the Laurent analysis
    mask = ts >= 5.0
    ts_fit = ts[mask]
    xs_fit = xs[mask]
    ss = 1.0 / ts_fit
    
    n_pts = len(ss)
    n_var = xs_fit.shape[1]
    
    # For each coordinate, fit x_i(s) = a0 + a1*s + a2*s^2 using least squares
    # If a0 is well-determined and the residual is small, the coordinate has a finite limit
    limits = np.zeros(n_var)
    linear_terms = np.zeros(n_var)
    residual_norms = np.zeros(n_var)
    
    A = np.column_stack([np.ones_like(ss), ss, ss**2])
    for j in range(n_var):
        coef, res, _, _ = np.linalg.lstsq(A, xs_fit[:, j], rcond=None)
        limits[j] = coef[0]
        linear_terms[j] = coef[1]
        pred = A @ coef
        residual_norms[j] = np.sqrt(np.mean((xs_fit[:, j] - pred)**2))
    
    # Check how well the extrapolation to s=0 works
    # Use the second-to-last points to predict the last
    if n_pts >= 4:
        A_train = np.column_stack([np.ones(n_pts-1), ss[:-1], ss[:-1]**2])
        A_test = np.array([1.0, ss[-1], ss[-1]**2])
        pred_last = np.zeros(n_var)
        for j in range(n_var):
            coef, _, _, _ = np.linalg.lstsq(A_train, xs_fit[:-1, j], rcond=None)
            pred_last[j] = A_test @ coef
        cross_val_error = np.linalg.norm(xs_fit[-1] - pred_last) / np.linalg.norm(xs_fit[-1])
    else:
        cross_val_error = float('nan')
    
    # Identify variables with large residuals (bad Laurent fit → possible divergence)
    bad_fit_mask = residual_norms > 0.01
    
    # For the limiting point (s→0), reconstruct the tensor and check pairing
    x_limit = limits.copy()
    # Compute the Brent tensor residual at the limiting point
    # (We'll do this externally with the full machinery)
    
    # Organize by terms
    term_analysis = []
    for k in range(r):
        u_lim = limits[27*k:27*k+9]
        v_lim = limits[27*k+9:27*k+18]
        w_lim = limits[27*k+18:27*k+27]
        u_res = residual_norms[27*k:27*k+9]
        v_res = residual_norms[27*k+9:27*k+18]
        w_res = residual_norms[27*k+18:27*k+27]
        term_analysis.append({
            'term': k,
            'u_limit_norm': float(np.linalg.norm(u_lim)),
            'v_limit_norm': float(np.linalg.norm(v_lim)),
            'w_limit_norm': float(np.linalg.norm(w_lim)),
            'u_residual_max': float(np.max(u_res)),
            'v_residual_max': float(np.max(v_res)),
            'w_residual_max': float(np.max(w_res)),
            'product_limit_norm': float(np.linalg.norm(u_lim) * np.linalg.norm(v_lim) * np.linalg.norm(w_lim)),
            'max_residual': float(max(np.max(u_res), np.max(v_res), np.max(w_res))),
        })
    
    # Sort by which terms have worst fit (possible divergent behavior)
    term_analysis.sort(key=lambda x: -x['max_residual'])
    
    # Check pairing at the limit
    uv_cols = []
    for k in range(r):
        u = limits[27*k:27*k+9]
        v = limits[27*k+9:27*k+18]
        uv_cols.append(np.outer(u, v).ravel())
    P_lim = np.column_stack(uv_cols)
    col_norms_lim = np.linalg.norm(P_lim, axis=0)
    col_norms_lim[col_norms_lim < 1e-15] = 1.0
    P_norm_lim = P_lim / col_norms_lim
    _, S_lim, _ = np.linalg.svd(P_norm_lim, full_matrices=False)
    
    return {
        'n_fit_points': int(n_pts),
        's_range': [float(ss[-1]), float(ss[0])],
        'x_limit_norm': float(np.linalg.norm(limits)),
        'overall_residual_rms': float(np.sqrt(np.mean(residual_norms**2))),
        'max_coordinate_residual': float(np.max(residual_norms)),
        'n_bad_fit_coordinates': int(np.sum(bad_fit_mask)),
        'cross_validation_relative_error': float(cross_val_error),
        'limit_pairing_uv_singular_values': [float(x) for x in S_lim],
        'limit_pairing_uv_sigma_min': float(S_lim[-1]),
        'limit_pairing_uv_sigma_second_min': float(S_lim[-2]) if len(S_lim) > 1 else None,
        'term_analysis_worst_fit': term_analysis[:5],
        'x_limit': limits.tolist(),
    }


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('continuation_json')
    ap.add_argument('--json-out', required=True)
    args = ap.parse_args()
    
    d, ts, sigmas, step_norms, brent_res, xs = load_continuation(args.continuation_json)
    
    results = {}
    
    # 1. Power-law decay fit (boundary at infinity model)
    results['power_law_decay'] = fit_power_law_decay(ts, sigmas, t_min=5)
    print(f"Power-law fit: σ ~ {results['power_law_decay']['C']:.6f} * t^(-{results['power_law_decay']['alpha']:.4f}), R²={results['power_law_decay']['R2']:.8f}")
    
    # 2. Finite boundary fit
    results['finite_boundary'] = fit_finite_boundary(ts, sigmas, t_min=5)
    if results['finite_boundary']:
        fb = results['finite_boundary']
        print(f"Finite boundary fit: σ ~ {fb['C']:.6f} * (t*-t)^{fb['beta']:.4f}, t*={fb['t_star']:.2f}, R²={fb['R2']:.8f}")
    
    # 3. ARTIFACT norm analysis
    results['step_norm'] = fit_step_norm(ts, step_norms, t_min=5)
    print(f"ARTIFACT norm: {results['step_norm']['interpretation']}")
    
    # 4. Factor growth analysis
    results['factor_growth'] = analyze_factor_growth(ts, xs)
    print(f"Max factor growth ratio: {results['factor_growth']['max_factor_growth_overall']:.4f}")
    
    # 5. Laurent expansion in s=1/t
    results['laurent'] = laurent_expansion_in_s(ts, xs)
    print(f"Laurent: limit point norm={results['laurent']['x_limit_norm']:.4f}, "
          f"residual RMS={results['laurent']['overall_residual_rms']:.6f}, "
          f"limit uv σ_min={results['laurent']['limit_pairing_uv_sigma_min']:.8f}")
    
    # 6. Compare model fits
    pl_r2 = results['power_law_decay']['R2']
    fb_r2 = results['finite_boundary']['R2'] if results['finite_boundary'] else -1
    
    if pl_r2 > 0.999 and pl_r2 > fb_r2:
        verdict = 'STRONG EVIDENCE: boundary at infinity (power-law decay σ ~ t^(-α))'
    elif fb_r2 > 0.999 and fb_r2 > pl_r2:
        verdict = f'STRONG EVIDENCE: finite boundary at t*≈{results["finite_boundary"]["t_star"]:.1f}'
    elif pl_r2 > fb_r2:
        verdict = 'MODERATE EVIDENCE: boundary at infinity (power-law preferred but not decisive)'
    else:
        verdict = 'INCONCLUSIVE: neither model clearly dominant'
    
    results['verdict'] = verdict
    results['model_comparison'] = {
        'power_law_R2': pl_r2,
        'finite_boundary_R2': fb_r2,
        'preferred': 'power_law' if pl_r2 > fb_r2 else 'finite_boundary'
    }
    
    print(f"\n=== VERDICT: {verdict} ===")
    
    # Print near-dependence evolution
    print("\nNear-dependence evolution:")
    for nd in results['factor_growth']['near_dependence_evolution'][-6:]:
        print(f"  t={nd['t']:6.1f}: σ_min={nd['sigma_min']:.6e}, "
              f"null top=({nd['null_vector_top5'][0][0]},{nd['null_vector_top5'][0][1]:.3f}), "
              f"sparsity={nd['null_vector_sparsity']:.0f}")
    
    Path(args.json_out).write_text(json.dumps(results, indent=2) + '\n')
    print(f"\nWrote {args.json_out}")

if __name__ == '__main__':
    main()
