#!/usr/bin/env python3
"""Calibrate the lift obstruction tightness using rank-21 core decompositions.

For each rank-21 E11 core CPD from the pool, test ALL 2^21 lift-bit assignments
epsilon_i in {0,1} and check how many satisfy rank(M_0 + Delta) <= 1 where
Delta = sum_{eps_i=1} v_i tensor w_i.

This calibrates how restrictive the lift condition is. If even rank-21 cores
rarely admit rank <= 1, rank-19 cores (fewer terms, fewer possible Delta matrices)
would be even more constrained.
"""
import numpy as np
from pathlib import Path
import json, time

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUTDIR = WS / "data" / "lift_calibration"
OUTDIR.mkdir(parents=True, exist_ok=True)

def vec_from_mask(mask, n):
    return np.array([(int(mask)>>i)&1 for i in range(n)], dtype=np.uint8)

def gf2_rank_batch(matrices):
    """Compute GF(2) rank for a batch of matrices. matrices shape: (batch, m, n)."""
    ranks = np.zeros(len(matrices), dtype=np.int32)
    for idx in range(len(matrices)):
        A = matrices[idx].copy().astype(np.uint8) % 2
        rows, cols = A.shape
        rank = 0
        for col in range(cols):
            pivot = -1
            for row in range(rank, rows):
                if A[row, col] & 1:
                    pivot = row
                    break
            if pivot == -1:
                continue
            if pivot != rank:
                A[rank], A[pivot] = A[pivot].copy(), A[rank].copy()
            for row in range(rows):
                if row != rank and (A[row, col] & 1):
                    A[row] ^= A[rank]
            rank += 1
        ranks[idx] = rank
    return ranks

def build_M0():
    M0 = np.zeros((9,9), dtype=np.uint8)
    M0[:3,:3] = np.eye(3, dtype=np.uint8)
    return M0

def load_pool(pool_path, max_rows=10):
    """Load core CPD rows from pool."""
    pool = np.load(pool_path)
    n_rows = min(len(pool), max_rows)
    results = []
    for idx in range(n_rows):
        row = pool[idx]
        rank = len(row) // 3
        v_list = []
        w_list = []
        for t in range(rank):
            u, v, w = int(row[3*t]), int(row[3*t+1]), int(row[3*t+2])
            v_list.append(vec_from_mask(v, 9))
            w_list.append(vec_from_mask(w, 9))
        results.append({
            'rank': rank,
            'V': np.array(v_list, dtype=np.uint8),  # (rank, 9)
            'W': np.array(w_list, dtype=np.uint8),   # (rank, 9)
        })
    return results

def test_all_lift_assignments(V, W, M0, max_rank_target=1):
    """Test all 2^r lift-bit assignments for rank(M0 + Delta) <= max_rank_target."""
    r = len(V)
    assert r == len(W)
    
    # Precompute v_t tensor w_t for each term
    vw = np.zeros((r, 9, 9), dtype=np.uint8)
    for t in range(r):
        vw[t] = np.outer(V[t], W[t]).astype(np.uint8) % 2
    
    count_le1 = 0
    count_eq0 = 0
    count_eq1 = 0
    rank_dist = {}
    examples_le1 = []
    
    total = 1 << r
    t0 = time.time()
    
    for eps_mask in range(total):
        # Compute Delta = sum_{eps_t=1} v_t tensor w_t
        Delta = np.zeros((9,9), dtype=np.uint8)
        for t in range(r):
            if (eps_mask >> t) & 1:
                Delta ^= vw[t]
        
        # Compute M0 + Delta
        target = (M0 + Delta) % 2
        
        # Compute rank
        rk = int(gf2_rank_batch(target.reshape(1,9,9))[0])
        rank_dist[rk] = rank_dist.get(rk, 0) + 1
        
        if rk <= max_rank_target:
            count_le1 += 1
            if rk == 0:
                count_eq0 += 1
            else:
                count_eq1 += 1
            if len(examples_le1) < 5:
                eps_bits = [int((eps_mask >> t) & 1) for t in range(r)]
                examples_le1.append({
                    'eps_mask': eps_mask,
                    'eps_bits': eps_bits,
                    'rank': rk,
                    'popcount': sum(eps_bits)
                })
        
        if (eps_mask + 1) % (1 << 20) == 0:
            elapsed = time.time() - t0
            print(f"  Checked {eps_mask+1}/{total} ({100*(eps_mask+1)/total:.1f}%) in {elapsed:.1f}s")
    
    elapsed = time.time() - t0
    return {
        'total_assignments': total,
        'count_rank_le_1': count_le1,
        'count_rank_0': count_eq0,
        'count_rank_1': count_eq1,
        'rank_distribution': rank_dist,
        'examples_le1': examples_le1,
        'elapsed_sec': round(elapsed, 2)
    }

def main():
    print("=" * 60)
    print("LIFT OBSTRUCTION CALIBRATION")
    print("=" * 60)
    
    M0 = build_M0()
    
    # Find the pool file
    pool_candidates = [
        "data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy",
    ]
    pool_path = None
    for p in pool_candidates:
        if Path(p).exists():
            pool_path = p
            break
    
    if pool_path is None:
        print("ERROR: Could not find rank-21 pool file")
        return
    
    print(f"\nPool: {pool_path}")
    
    # Load first few rows
    decomps = load_pool(pool_path, max_rows=3)
    
    all_results = []
    for idx, decomp in enumerate(decomps):
        print(f"\n--- Testing decomposition {idx} (rank {decomp['rank']}) ---")
        V, W = decomp['V'], decomp['W']
        print(f"  V shape: {V.shape}, W shape: {W.shape}")
        print(f"  Total assignments: 2^{decomp['rank']} = {1 << decomp['rank']}")
        
        result = test_all_lift_assignments(V, W, M0)
        result['decomp_idx'] = idx
        result['decomp_rank'] = decomp['rank']
        all_results.append(result)
        
        print(f"  Time: {result['elapsed_sec']}s")
        print(f"  Rank distribution of M0+Delta:")
        for rk in sorted(result['rank_distribution'].keys()):
            cnt = result['rank_distribution'][rk]
            pct = 100.0 * cnt / result['total_assignments']
            print(f"    rank {rk}: {cnt} ({pct:.4f}%)")
        print(f"  Rank ≤ 1: {result['count_rank_le_1']} ({100.0*result['count_rank_le_1']/result['total_assignments']:.6f}%)")
        
        if result['examples_le1']:
            print(f"  Example lift assignments with rank ≤ 1:")
            for ex in result['examples_le1'][:3]:
                print(f"    eps_mask={ex['eps_mask']}, popcount={ex['popcount']}, rank={ex['rank']}")
    
    # Save results
    with open(OUTDIR / "lift_calibration_rank21.json", "w") as f:
        json.dump(all_results, f, indent=2)
    print(f"\nSaved: {OUTDIR / 'lift_calibration_rank21.json'}")

if __name__ == "__main__":
    main()
