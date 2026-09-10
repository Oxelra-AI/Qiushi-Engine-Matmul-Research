#!/usr/bin/env python3
"""
Coupled dual-basis system for E11 core decompositions over F_2.

Mathematical foundation:
  For a saturated rank-9 contraction λ with M_λ = Λ⊗I_3 invertible and |I_λ| = 9,
  the active B/C factors satisfy C_λ^T M_λ^{-1} B_λ = I_9.
  The diagonal gives: tr(M_λ^{-1} X_t) = 1 for each t ∈ I_λ, where X_t = b_t c_t^T.

  Convention (analysis corrected):
    tr(M^{-1} X) = Σ_{r,s} (M^{-1})_{rs} X_{sr} = c^T M^{-1} b  for X = bc^T.

  Multi-contraction coupling: combining trace conditions from ≥8 saturated rank-9
  contractions can detect supports with no valid B/C assignment (even relaxed).

This script:
  1. Builds the E11 core tensor and contraction structure
  2. For a given support, identifies all tight contractions
  3. Constructs the combined tensor-identity + trace linear system over GF(2)
  4. Checks GF(2) consistency (inconsistency = no valid relaxed X_t assignment)
  5. Analyzes the contraction overlap / coupling hypergraph
  6. Finds minimal inconsistent subsets (by greedy or exhaustive search)

Usage:
  python coupled_dual_basis_system.py [--support INDICES] [--control]
"""

import numpy as np
import json
import os
import sys
import itertools
from pathlib import Path

# ---------- GF(2) arithmetic ----------

def gf2_rref(A):
    """Row-reduce A over GF(2). Returns (rref_matrix, rank, pivot_cols)."""
    A = A.copy() % 2
    m, n = A.shape
    pivots = []
    row = 0
    for col in range(n):
        # find pivot
        found = -1
        for r in range(row, m):
            if A[r, col]:
                found = r
                break
        if found < 0:
            continue
        # swap
        A[[row, found]] = A[[found, row]]
        # eliminate
        for r in range(m):
            if r != row and A[r, col]:
                A[r] ^= A[row]
        pivots.append(col)
        row += 1
    return A, row, pivots


def gf2_rank(A):
    _, r, _ = gf2_rref(np.array(A, dtype=np.uint8))
    return r


def gf2_consistent(A, b):
    """Check if Ax = b is consistent over GF(2)."""
    A = np.array(A, dtype=np.uint8) % 2
    b = np.array(b, dtype=np.uint8).reshape(-1, 1) % 2
    Ab = np.hstack([A, b])
    _, rank_Ab, _ = gf2_rref(Ab)
    _, rank_A, _ = gf2_rref(A)
    return rank_A == rank_Ab, rank_A, rank_Ab


# ---------- E11 core tensor ----------

def build_e11_core():
    """Build the E11 quotient core tensor T_core ∈ F_2^{8×9×9}.
    
    Slices: 8 basis matrices of L = {Λ ∈ M_3(F_2) : Λ_11 = 0}.
    Each slice S_j = (Λ_j ⊗ I_3), occupying a specific 3×3 block.
    """
    T = np.zeros((8, 9, 9), dtype=np.uint8)
    # The 8 matrix units E_{ij} with (i,j) ≠ (0,0), indexed 0-7
    # A-matrix positions (i,j):
    a_positions = [(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
    # Corresponding B⊗C block positions (j,i) — transposed!
    # analysis verified: L(q) = Q^T ⊗ I_3, so A-entry (i,j) gives
    # I_3 at block (j,i) in the 9×9 B×C matrix.
    
    for idx, (ai, aj) in enumerate(a_positions):
        # Block position in B⊗C is (aj, ai) = transpose of A-position
        bi, bj = aj, ai
        for k in range(3):
            T[idx, 3*bi + k, 3*bj + k] = 1
    
    return T, a_positions


def lambda_to_mat(lam_int):
    """Convert 8-bit lambda to 3×3 matrix with Λ_11 = 0."""
    positions = [(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
    M = np.zeros((3,3), dtype=np.uint8)
    for bit_idx, (i,j) in enumerate(positions):
        if lam_int & (1 << bit_idx):
            M[i,j] = 1
    return M


def mat_rank_gf2(M):
    """Rank of matrix over GF(2)."""
    return gf2_rank(M)


def mat_inv_gf2(M):
    """Inverse of invertible matrix over GF(2)."""
    n = M.shape[0]
    A = np.hstack([M.copy() % 2, np.eye(n, dtype=np.uint8)])
    rref, r, _ = gf2_rref(A)
    assert r == n, f"Matrix not invertible (rank {r} vs {n})"
    return rref[:, n:] % 2


def contraction_matrix(lam_int):
    """Build M_λ = Λ^T ⊗ I_3 (9×9 over F_2).
    
    analysis verified: L(q) = Q^T ⊗ I_3 in row-major conventions.
    The block at position (j,i) in the 9×9 matrix carries Λ_{ij}·I_3.
    """
    Lambda = lambda_to_mat(lam_int)
    return np.kron(Lambda.T, np.eye(3, dtype=np.uint8)) % 2


# ---------- Support analysis ----------

def support_active_sets(support, n_bits=8):
    """For each nonzero λ ∈ F_2^8, compute I_λ = {t : <λ, a_t> = 1}."""
    active = {}
    for lam in range(1, 1 << n_bits):
        I_lam = []
        for t, a in enumerate(support):
            if bin(a & lam).count('1') % 2 == 1:
                I_lam.append(t)
        active[lam] = I_lam
    return active


def find_tight_contractions(support, active_sets=None):
    """Find all tight contractions for given support.
    
    Returns dict: lam -> {active_set, contraction_rank, lambda_rank, is_tight}
    Only returns tight contractions (|I_λ| == contraction_rank).
    """
    if active_sets is None:
        active_sets = support_active_sets(support)
    
    tight = {}
    for lam in range(1, 256):
        I_lam = active_sets[lam]
        Lambda = lambda_to_mat(lam)
        lr = int(mat_rank_gf2(Lambda))
        cr = 3 * lr  # contraction rank
        if len(I_lam) == cr:
            tight[lam] = {
                'active_set': I_lam,
                'lambda_rank': lr,
                'contraction_rank': cr,
            }
    return tight


# ---------- Combined linear system ----------

def build_tensor_identity_system(support, T_core):
    """Build the tensor identity equations: Σ_{t: (a_t)_i=1} X_t = S_i.
    
    Variables: X_t[r,c] for t=0..s-1, r,c=0..8 → total s*81 variables.
    Equations: 8 slices × 81 entries = 648.
    """
    s = len(support)
    n_vars = s * 81
    positions = [(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
    
    rows = []
    rhs = []
    
    for slice_idx in range(8):
        for r in range(9):
            for c in range(9):
                row = np.zeros(n_vars, dtype=np.uint8)
                for t, a in enumerate(support):
                    if a & (1 << slice_idx):
                        var_idx = t * 81 + r * 9 + c
                        row[var_idx] = 1
                rows.append(row)
                rhs.append(T_core[slice_idx, r, c])
    
    return np.array(rows, dtype=np.uint8), np.array(rhs, dtype=np.uint8)


def build_trace_equations(support, tight_rank9, active_sets):
    """Build trace equations: tr(M_λ^{-1} X_t) = 1 for tight rank-9 contractions.
    
    Corrected convention: tr(M^{-1} X) = Σ_{r,s} (M^{-1})_{rs} X_{sr}.
    """
    s = len(support)
    n_vars = s * 81
    
    rows = []
    rhs = []
    contraction_labels = []
    
    for lam, info in tight_rank9.items():
        M = contraction_matrix(lam)
        M_inv = mat_inv_gf2(M)
        
        for t in info['active_set']:
            row = np.zeros(n_vars, dtype=np.uint8)
            # tr(M^{-1} X_t) = Σ_{r,s} (M^{-1})_{rs} * X_t[s,r]
            for r in range(9):
                for ss in range(9):
                    if M_inv[r, ss]:
                        # coefficient of X_t[s, r]
                        var_idx = t * 81 + ss * 9 + r
                        row[var_idx] ^= 1
            rows.append(row)
            rhs.append(1)
            contraction_labels.append((lam, t))
    
    if not rows:
        return np.zeros((0, n_vars), dtype=np.uint8), np.array([], dtype=np.uint8), []
    
    return np.array(rows, dtype=np.uint8), np.array(rhs, dtype=np.uint8), contraction_labels


def analyze_coupling(support, tight_rank9):
    """Analyze the contraction overlap / coupling hypergraph."""
    s = len(support)
    
    # Term participation: for each term, which contractions include it
    term_contractions = {t: [] for t in range(s)}
    for lam, info in tight_rank9.items():
        for t in info['active_set']:
            term_contractions[t].append(lam)
    
    # Pairwise overlaps between tight rank-9 contractions
    lams = sorted(tight_rank9.keys())
    overlap_matrix = {}
    for i, l1 in enumerate(lams):
        for j, l2 in enumerate(lams):
            if i < j:
                s1 = set(tight_rank9[l1]['active_set'])
                s2 = set(tight_rank9[l2]['active_set'])
                overlap_matrix[(l1, l2)] = len(s1 & s2)
    
    return {
        'num_tight_rank9': len(tight_rank9),
        'num_terms': s,
        'term_participation': {t: len(cs) for t, cs in term_contractions.items()},
        'max_participation': max(len(cs) for cs in term_contractions.values()),
        'min_participation': min(len(cs) for cs in term_contractions.values()),
        'avg_participation': sum(len(cs) for cs in term_contractions.values()) / s,
        'pairwise_overlap_hist': {},
        'total_incidences': sum(len(cs) for cs in term_contractions.values()),
    }


def check_combined_system(support, T_core, tight_rank9, active_sets, 
                          include_trace=True, trace_subset=None):
    """Build and check the combined tensor-identity + trace system.
    
    Returns consistency info and ranks.
    """
    s = len(support)
    n_vars = s * 81
    
    # Tensor identity
    A_tensor, b_tensor = build_tensor_identity_system(support, T_core)
    
    if not include_trace:
        consistent, rank_A, rank_Ab = gf2_consistent(A_tensor, b_tensor)
        return {
            'consistent': consistent,
            'rank_A': int(rank_A),
            'rank_Ab': int(rank_Ab),
            'n_equations': len(A_tensor),
            'n_variables': n_vars,
            'trace_equations': 0,
        }
    
    # Trace equations
    if trace_subset is not None:
        tight_sub = {l: tight_rank9[l] for l in trace_subset if l in tight_rank9}
    else:
        tight_sub = tight_rank9
    
    A_trace, b_trace, labels = build_trace_equations(support, tight_sub, active_sets)
    
    if len(A_trace) == 0:
        consistent, rank_A, rank_Ab = gf2_consistent(A_tensor, b_tensor)
        return {
            'consistent': consistent,
            'rank_A': int(rank_A),
            'rank_Ab': int(rank_Ab),
            'n_equations': len(A_tensor),
            'n_variables': n_vars,
            'trace_equations': 0,
        }
    
    # Combined
    A_combined = np.vstack([A_tensor, A_trace])
    b_combined = np.concatenate([b_tensor, b_trace])
    
    consistent, rank_A, rank_Ab = gf2_consistent(A_combined, b_combined)
    
    # Also check tensor-only for reference
    _, rank_tensor, _ = gf2_rref(A_tensor)
    
    return {
        'consistent': bool(consistent),
        'rank_combined': int(rank_A),
        'rank_combined_augmented': int(rank_Ab),
        'rank_tensor_only': int(rank_tensor),
        'n_equations_total': len(A_combined),
        'n_tensor_equations': len(A_tensor),
        'n_trace_equations': len(A_trace),
        'n_variables': n_vars,
        'n_contractions_used': len(tight_sub),
        'trace_rank_gain': int(rank_A) - int(rank_tensor),
    }


def find_min_inconsistent_subset(support, T_core, tight_rank9, active_sets, max_size=10):
    """Find minimal subset of tight rank-9 contractions making system inconsistent.
    
    Uses greedy then exact search.
    """
    lams = sorted(tight_rank9.keys())
    n = len(lams)
    
    # First check: is full system inconsistent?
    full_result = check_combined_system(support, T_core, tight_rank9, active_sets, 
                                        include_trace=True)
    if full_result['consistent']:
        return {'full_consistent': True, 'min_inconsistent': None}
    
    # Binary search / greedy for minimal inconsistent subset
    best_subset = list(lams)
    
    # Try removing one at a time (greedy shrink)
    changed = True
    while changed:
        changed = False
        for i in range(len(best_subset)):
            candidate = best_subset[:i] + best_subset[i+1:]
            result = check_combined_system(support, T_core, tight_rank9, active_sets,
                                          include_trace=True, trace_subset=candidate)
            if not result['consistent']:
                best_subset = candidate
                changed = True
                break
    
    # Now try exact search for smaller subsets
    min_size = len(best_subset)
    found_smaller = False
    
    for size in range(2, min(min_size, max_size + 1)):
        for subset in itertools.combinations(lams, size):
            result = check_combined_system(support, T_core, tight_rank9, active_sets,
                                          include_trace=True, trace_subset=list(subset))
            if not result['consistent']:
                best_subset = list(subset)
                min_size = size
                found_smaller = True
                break
        if found_smaller:
            break
    
    return {
        'full_consistent': False,
        'min_inconsistent_size': min_size,
        'min_inconsistent_contractions': best_subset,
        'total_contractions': n,
    }


# ---------- Positive control: cn122 ----------

def load_cn122_core(scheme_path):
    """Load cn122 rank-23 scheme, reduce mod 2, project to E11 core."""
    # A-matrix positions for the 8-bit encoding
    positions = [(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]  # same as a_positions
    
    terms = []
    with open(scheme_path) as f:
        lines = f.readlines()
    
    current_term = {}
    for line in lines:
        line = line.strip()
        if line.startswith('term '):
            if current_term:
                terms.append(current_term)
            current_term = {'idx': int(line.split()[1])}
        elif line.startswith('u '):
            current_term['u'] = [int(x) % 2 for x in line.split()[1:]]
        elif line.startswith('v '):
            current_term['v'] = [int(x) % 2 for x in line.split()[1:]]
        elif line.startswith('w '):
            current_term['w'] = [int(x) % 2 for x in line.split()[1:]]
    if current_term:
        terms.append(current_term)
    
    # Project A-factors to 8-bit E11 core encoding
    core_terms = []
    for term in terms:
        u = term['u']  # 9-entry A-vector
        # E11 core projection: extract bits corresponding to positions
        a_bits = 0
        for bit_idx, (i,j) in enumerate(positions):
            if u[3*i + j]:
                a_bits |= (1 << bit_idx)
        if a_bits != 0:  # nonzero projection
            core_terms.append({
                'a': a_bits,
                'b': np.array(term['v'], dtype=np.uint8),
                'c': np.array(term['w'], dtype=np.uint8),
            })
    
    return core_terms


# ---------- Main ----------

def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--support', type=str, default=None,
                        help='Comma-separated A-direction integers')
    parser.add_argument('--control', action='store_true',
                        help='Run cn122 positive control')
    parser.add_argument('--l15', action='store_true',
                        help='Run L15 near-miss support')
    parser.add_argument('--min-subset', action='store_true',
                        help='Search for minimal inconsistent subset')
    parser.add_argument('--max-subset-size', type=int, default=10)
    parser.add_argument('--outdir', type=str, 
                        default='data/coupled_dual_basis')
    args = parser.parse_args()
    
    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    
    T_core, positions = build_e11_core()
    
    results = {}
    
    # L15 near-miss
    L15 = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]
    
    if args.l15 or (not args.support and not args.control):
        print("=" * 60)
        print("L15 NEAR-MISS SUPPORT ANALYSIS")
        print("=" * 60)
        
        active = support_active_sets(L15)
        tight = find_tight_contractions(L15, active)
        tight_r9 = {l: v for l, v in tight.items() if v['lambda_rank'] == 3}
        tight_r6 = {l: v for l, v in tight.items() if v['lambda_rank'] == 2}
        tight_r3 = {l: v for l, v in tight.items() if v['lambda_rank'] == 1}
        
        print(f"Support size: {len(L15)}")
        print(f"Tight rank-9 contractions: {len(tight_r9)}")
        print(f"Tight rank-6 contractions: {len(tight_r6)}")
        print(f"Tight rank-3 contractions: {len(tight_r3)}")
        
        # Coupling analysis
        coupling = analyze_coupling(L15, tight_r9)
        print(f"\nCoupling structure:")
        print(f"  Term participation: min={coupling['min_participation']}, "
              f"max={coupling['max_participation']}, avg={coupling['avg_participation']:.1f}")
        print(f"  Total incidences: {coupling['total_incidences']}")
        
        # Tensor-only
        result_tensor = check_combined_system(L15, T_core, tight_r9, active, 
                                              include_trace=False)
        print(f"\nTensor-only system:")
        print(f"  Consistent: {result_tensor['consistent']}")
        print(f"  Rank: {result_tensor['rank_A']}/{result_tensor['n_equations']} eqs, "
              f"{result_tensor['n_variables']} vars")
        
        # Full trace system
        result_full = check_combined_system(L15, T_core, tight_r9, active, 
                                           include_trace=True)
        print(f"\nFull tensor + trace system:")
        print(f"  Consistent: {result_full['consistent']}")
        print(f"  Combined rank: {result_full['rank_combined']}")
        print(f"  Augmented rank: {result_full['rank_combined_augmented']}")
        print(f"  Trace rank gain: {result_full['trace_rank_gain']}")
        print(f"  Equations: {result_full['n_equations_total']} "
              f"({result_full['n_tensor_equations']} tensor + "
              f"{result_full['n_trace_equations']} trace)")
        
        # Individual contraction check
        print(f"\nPer-contraction trace consistency:")
        individual_results = {}
        for lam in sorted(tight_r9.keys()):
            r = check_combined_system(L15, T_core, tight_r9, active,
                                     include_trace=True, trace_subset=[lam])
            individual_results[lam] = r['consistent']
        
        n_individual_fail = sum(1 for v in individual_results.values() if not v)
        print(f"  Individual inconsistent: {n_individual_fail}/{len(tight_r9)}")
        if n_individual_fail > 0:
            print(f"  Failing contractions: {[l for l,v in individual_results.items() if not v]}")
        
        # Minimal inconsistent subset
        if args.min_subset:
            print(f"\nSearching for minimal inconsistent subset (max size {args.max_subset_size})...")
            min_result = find_min_inconsistent_subset(
                L15, T_core, tight_r9, active, max_size=args.max_subset_size)
            print(f"  Min inconsistent size: {min_result.get('min_inconsistent_size', 'N/A')}")
            if min_result.get('min_inconsistent_contractions'):
                print(f"  Contractions: {min_result['min_inconsistent_contractions']}")
            results['l15_min_subset'] = min_result
        
        results['l15'] = {
            'support': L15,
            'tight_rank9_count': len(tight_r9),
            'tight_rank6_count': len(tight_r6),
            'tight_rank3_count': len(tight_r3),
            'tight_rank9_lambdas': sorted(tight_r9.keys()),
            'coupling': coupling,
            'tensor_only': result_tensor,
            'full_trace': result_full,
            'individual_consistent': individual_results,
            'n_individual_fail': n_individual_fail,
        }
    
    # cn122 positive control
    if args.control:
        print("\n" + "=" * 60)
        print("CN122 POSITIVE CONTROL (21-term core)")
        print("=" * 60)
        
        scheme_path = "data/cn122_3x3_r23_repro/scheme.qmm"
        if not os.path.exists(scheme_path):
            print(f"Scheme not found at {scheme_path}")
        else:
            core_terms = load_cn122_core(scheme_path)
            cn_support = [t['a'] for t in core_terms]
            cn_support_unique = sorted(set(cn_support))
            
            print(f"Core terms: {len(core_terms)}, unique A-dirs: {len(cn_support_unique)}")
            
            # For the positive control, use unique A-directions
            # Note: cn122 has 21 core terms with 19 distinct A-directions
            # We test the DISTINCT support (19 points)
            active = support_active_sets(cn_support_unique)
            tight = find_tight_contractions(cn_support_unique, active)
            tight_r9 = {l: v for l, v in tight.items() if v['lambda_rank'] == 3}
            
            print(f"Distinct support size: {len(cn_support_unique)}")
            print(f"Tight rank-9 contractions: {len(tight_r9)}")
            
            # Check consistency (should pass since this comes from an actual decomposition
            # ... of the 21-term core, which has 19 distinct directions)
            # Note: the 19-direction support maps to the core of 21 terms where some
            # directions repeat; the trace system uses the 19-direction support
            result = check_combined_system(cn_support_unique, T_core, tight_r9, active,
                                          include_trace=True)
            print(f"\nFull tensor + trace system:")
            print(f"  Consistent: {result['consistent']}")
            print(f"  Combined rank: {result['rank_combined']}")
            print(f"  Trace rank gain: {result['trace_rank_gain']}")
            
            # Also verify actual factors satisfy trace conditions
            print(f"\nVerifying actual factors against trace conditions...")
            trace_pass = 0
            trace_fail = 0
            for lam, info in tight_r9.items():
                M = contraction_matrix(lam)
                M_inv = mat_inv_gf2(M)
                for t_idx in info['active_set']:
                    a_dir = cn_support_unique[t_idx]
                    # Find a core term with this A-direction
                    for ct in core_terms:
                        if ct['a'] == a_dir:
                            b, c = ct['b'], ct['c']
                            X = np.outer(b, c) % 2
                            # tr(M^{-1} X) = Σ_{r,s} M_inv[r,s] * X[s,r]
                            tr_val = 0
                            for r in range(9):
                                for s in range(9):
                                    tr_val ^= (M_inv[r, s] * X[s, r])
                            if tr_val == 1:
                                trace_pass += 1
                            else:
                                trace_fail += 1
                            break
            print(f"  Trace pass: {trace_pass}, fail: {trace_fail}")
            
            results['cn122_control'] = {
                'support': cn_support_unique,
                'n_core_terms': len(core_terms),
                'n_distinct': len(cn_support_unique),
                'tight_rank9_count': len(tight_r9),
                'full_trace': result,
                'factor_trace_pass': trace_pass,
                'factor_trace_fail': trace_fail,
            }
    
    # Custom support
    if args.support:
        support = [int(x) for x in args.support.split(',')]
        print(f"\nCustom support: {support}")
        active = support_active_sets(support)
        tight = find_tight_contractions(support, active)
        tight_r9 = {l: v for l, v in tight.items() if v['lambda_rank'] == 3}
        
        result = check_combined_system(support, T_core, tight_r9, active,
                                      include_trace=True)
        print(f"Tight rank-9: {len(tight_r9)}")
        print(f"Consistent: {result['consistent']}")
        print(f"Combined rank: {result['rank_combined']}")
        print(f"Trace rank gain: {result['trace_rank_gain']}")
        
        results['custom'] = {
            'support': support,
            'tight_rank9_count': len(tight_r9),
            'full_trace': result,
        }
    
    # Save results
    out_path = outdir / "coupled_dual_basis_analysis.json"
    
    # Convert numpy types for JSON
    def convert(obj):
        if isinstance(obj, (np.integer, np.int64, np.int32)):
            return int(obj)
        if isinstance(obj, (np.floating, np.float64)):
            return float(obj)
        if isinstance(obj, np.ndarray):
            return obj.tolist()
        if isinstance(obj, np.bool_):
            return bool(obj)
        if isinstance(obj, dict):
            return {str(k): convert(v) for k, v in obj.items()}
        if isinstance(obj, list):
            return [convert(v) for v in obj]
        return obj
    
    with open(out_path, 'w') as f:
        json.dump(convert(results), f, indent=2)
    print(f"\nResults saved to {out_path}")
    
    return results


if __name__ == "__main__":
    main()
