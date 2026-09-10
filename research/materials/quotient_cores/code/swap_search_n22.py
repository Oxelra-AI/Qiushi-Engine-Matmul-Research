#!/usr/bin/env python3
"""Swap-based hill-climb search for Wang-admissible n=22 A-multisets.

Starting from deletion near-misses of known rank-23 schemes (which have ~19
excess-1 violations among 8.28M Wang rows), iteratively apply single-direction
swaps to reduce violations to zero.

Algorithm per iteration:
  1. Stream binary, compute occupation, identify violated/tight/near-tight rows
  2. For each (remove_position, add_direction) pair, compute:
       fixed  = #{violated rows: A[i] in row AND d not in row}
       created = #{tight rows: d in row AND A[i] not in row}
  3. Apply the best swap (max fixed - created)
  4. If violations == 0: output candidate for trace filter + Brent completion
  
Uses numpy for vectorized occupation computation over 8.28M rows.
"""
from __future__ import annotations
import argparse, json, struct, sys, time, os
from collections import Counter
from pathlib import Path
from typing import List, Tuple, Optional
import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

WORKSPACE = SCRIPT_DIR.parent
DEFAULT_BINARY = WORKSPACE / "data" / "pivot_fixed_n22_binary" / "full_wang512_cap21_len22_all_dim9_allbinding.bin"
DEFAULT_SEEDS = WORKSPACE / "data" / "pivot_fixed_n22" / "rank23_deletion_wang22.json"


def load_wang512_numpy(path: Path) -> Tuple[np.ndarray, np.ndarray, np.ndarray, int]:
    """Load WANG512 binary into numpy arrays.
    
    Returns: (masks_u64[nrows,8], caps[nrows], dims[nrows], nrows)
    masks_u64[r, w] is the w-th uint64 word of row r's 512-bit mask.
    """
    raw = path.read_bytes()
    assert raw[:8] == b"WANG512\x01", f"Bad magic"
    nrows = struct.unpack_from("<I", raw, 8)[0]
    # Each record: cap(u8) dim(u8) reserved(u16) mask[8](u64)
    rec_size = 68
    data = np.frombuffer(raw, dtype=np.uint8, offset=12)
    data = data[:nrows * rec_size].reshape(nrows, rec_size)
    caps = data[:, 0].copy()
    dims = data[:, 1].copy()
    # Extract 8 uint64 words per row (bytes 4..67)
    mask_bytes = data[:, 4:68].copy()  # shape (nrows, 64)
    masks_u64 = mask_bytes.view(np.uint64).reshape(nrows, 8)
    return masks_u64, caps, dims, nrows


def bit_test_vectorized(masks: np.ndarray, d: int) -> np.ndarray:
    """Return boolean array: masks[r] has bit d set."""
    w = d >> 6  # word index
    b = d & 63  # bit index
    return ((masks[:, w] >> np.uint64(b)) & np.uint64(1)).astype(bool)


def compute_occupation(masks: np.ndarray, multiset: List[int]) -> np.ndarray:
    """Compute occupation (with multiplicity) for each row."""
    nrows = masks.shape[0]
    occ = np.zeros(nrows, dtype=np.int32)
    cnt = Counter(multiset)
    for d, mult in cnt.items():
        occ += mult * bit_test_vectorized(masks, d).astype(np.int32)
    return occ


def find_interesting_rows(occ: np.ndarray, caps: np.ndarray, masks: np.ndarray, dims: np.ndarray):
    """Find violated, tight, and near-tight rows."""
    caps_i32 = caps.astype(np.int32)
    diff = occ - caps_i32
    
    violated_idx = np.where(diff > 0)[0]
    tight_idx = np.where(diff == 0)[0]
    near_tight_idx = np.where(diff == -1)[0]
    
    return violated_idx, tight_idx, near_tight_idx


def evaluate_all_swaps(masks: np.ndarray, caps: np.ndarray,
                       multiset: List[int],
                       violated_idx: np.ndarray,
                       tight_idx: np.ndarray,
                       occ: np.ndarray) -> Tuple[int, int, int, int]:
    """Evaluate all (remove_pos, add_dir) swaps.
    
    Returns: (best_remove_pos, best_add_dir, best_violations_after, current_violations)
    """
    r = len(multiset)
    current_violations = len(violated_idx)
    
    if current_violations == 0:
        return -1, -1, 0, 0
    
    # For violated rows: occ > cap, excess = occ - cap
    # A swap (remove A[i], add d) fixes a violated row iff:
    #   A[i] in row AND d not in row AND excess == 1
    # (For excess > 1, need delta <= -excess, impossible with single swap)
    caps_i32 = caps.astype(np.int32)
    excess_v = occ[violated_idx] - caps_i32[violated_idx]
    fixable_v = violated_idx[excess_v == 1]  # only excess-1 rows can be fixed
    unfixable_v = len(violated_idx) - len(fixable_v)
    
    # For tight rows: a swap creates a violation iff d in row AND A[i] not in row
    
    # Precompute membership for each direction in violated/tight rows
    # For fixable violated rows
    n_fix = len(fixable_v)
    n_tight = len(tight_idx)
    
    # Extract mask words for fixable violated and tight rows
    fix_masks = masks[fixable_v]  # shape (n_fix, 8)
    tight_masks = masks[tight_idx]  # shape (n_tight, 8)
    
    best_score = -10**9
    best_i = -1
    best_d = -1
    
    # For each remove position i
    for i in range(r):
        ai = multiset[i]
        # Skip if removing this creates a duplicate that's identical swap
        # (handled later by checking d != ai)
        
        # For fixable violated rows: does A[i] appear?
        ai_in_fix = bit_test_vectorized(fix_masks, ai)  # (n_fix,) bool
        
        # For tight rows: does A[i] appear?
        ai_in_tight = bit_test_vectorized(tight_masks, ai)  # (n_tight,) bool
        
        # For each candidate direction d
        for d in range(1, 512):
            if d == ai:
                continue  # no-op swap
            
            # Fixed: A[i] in row AND d not in row (for fixable rows)
            d_in_fix = bit_test_vectorized(fix_masks, d)  # (n_fix,) bool
            fixed = int(np.sum(ai_in_fix & ~d_in_fix))
            
            # Created: d in row AND A[i] not in row (for tight rows)  
            d_in_tight = bit_test_vectorized(tight_masks, d)  # (n_tight,) bool
            created = int(np.sum(d_in_tight & ~ai_in_tight))
            
            # Also: violated rows with excess > 1 that get worse
            # (d in row AND A[i] not in row for excess-1 rows → still violated, doesn't change count)
            # For excess-1 rows where d in row AND A[i] in row → occ unchanged → still violated
            # For excess-1 rows where d not in row AND A[i] not in row → occ unchanged → still violated
            
            # Worsened: tight rows where we add d and remove A[i]
            # Actually all handled: violations_after = current - fixed + created + unfixable
            # But unfixable stays constant across swaps
            
            score = fixed - created
            if score > best_score:
                best_score = score
                best_i = i
                best_d = d
    
    violations_after = current_violations - best_score  # since unfixable stays
    return best_i, best_d, violations_after, current_violations


def evaluate_swaps_fast(masks: np.ndarray, caps: np.ndarray,
                        multiset: List[int],
                        violated_idx: np.ndarray,
                        tight_idx: np.ndarray,
                        occ: np.ndarray) -> Tuple[int, int, int, int, list]:
    """Fast vectorized swap evaluation using matrix-vector products."""
    r = len(multiset)
    current_violations = len(violated_idx)
    
    if current_violations == 0:
        return -1, -1, 0, 0, []
    
    caps_i32 = caps.astype(np.int32)
    excess_v = occ[violated_idx] - caps_i32[violated_idx]
    fixable_mask = (excess_v == 1)
    fixable_v = violated_idx[fixable_mask]
    n_fix = len(fixable_v)
    n_tight = len(tight_idx)
    unfixable = int(np.sum(~fixable_mask))
    
    if n_fix == 0 and n_tight == 0:
        return -1, -1, current_violations, current_violations, []
    
    fix_masks = masks[fixable_v]  # (n_fix, 8)
    tight_masks = masks[tight_idx]  # (n_tight, 8)
    
    # Precompute membership: fix_has[d, r] = direction d in fixable row r
    fix_has = np.zeros((512, n_fix), dtype=np.float32)
    tight_has = np.zeros((512, n_tight), dtype=np.float32)
    
    for d in range(1, 512):
        w, b = d >> 6, d & 63
        fix_has[d] = ((fix_masks[:, w] >> np.uint64(b)) & np.uint64(1)).astype(np.float32)
        tight_has[d] = ((tight_masks[:, w] >> np.uint64(b)) & np.uint64(1)).astype(np.float32)
    
    # Precompute per-direction sums
    fix_sum = fix_has.sum(axis=1)   # (512,): how many fixable rows contain d
    tight_sum = tight_has.sum(axis=1)  # (512,): how many tight rows contain d
    
    # For each position i, evaluate ALL directions d simultaneously
    best_score = -10**9
    best_i = -1
    best_d = -1
    top_swaps = []
    
    for i in range(r):
        ai = multiset[i]
        # ai's membership vectors
        ai_fix = fix_has[ai]    # (n_fix,)
        ai_tight = tight_has[ai]  # (n_tight,)
        ai_fix_sum = float(ai_fix.sum())
        ai_tight_sum = float(ai_tight.sum())
        
        # For each d:
        # fixed[d] = sum(ai_in_fix AND NOT d_in_fix) = ai_fix @ (1 - fix_has[d])
        #          = ai_fix_sum - ai_fix @ fix_has[d]^T
        # Use matrix-vector: overlap_fix = fix_has @ ai_fix → (512,)
        overlap_fix = fix_has @ ai_fix  # (512,)
        fixed_all = ai_fix_sum - overlap_fix  # (512,)
        
        # created[d] = sum(d_in_tight AND NOT ai_in_tight) 
        #            = tight_sum[d] - tight_has[d] @ ai_tight
        overlap_tight = tight_has @ ai_tight  # (512,)
        created_all = tight_sum - overlap_tight  # (512,)
        
        scores = fixed_all - created_all  # (512,)
        scores[0] = -10**6  # direction 0 invalid
        scores[ai] = -10**6  # no-op swap
        
        best_d_for_i = int(np.argmax(scores))
        score_for_i = float(scores[best_d_for_i])
        
        if score_for_i > best_score:
            best_score = score_for_i
            best_i = i
            best_d = best_d_for_i
        
        # Record top swaps for this position
        top_d = np.argsort(scores)[-3:][::-1]
        for dd in top_d:
            dd = int(dd)
            if scores[dd] > -10**5:
                top_swaps.append({
                    'i': i, 'ai': int(ai), 'd': dd, 
                    'fixed': int(fixed_all[dd]), 'created': int(created_all[dd]),
                    'score': int(scores[dd])
                })
    
    top_swaps.sort(key=lambda x: -x['score'])
    violations_after = int(current_violations - best_score)
    return best_i, best_d, violations_after, current_violations, top_swaps[:20]


def mat33_rank(m: int) -> int:
    """GF(2) rank of 3x3 matrix encoded as 9-bit int."""
    rows = [(m >> (3*i)) & 7 for i in range(3)]
    r = 0
    for c in range(3):
        pivot = None
        for rr in range(r, 3):
            if (rows[rr] >> c) & 1:
                pivot = rr; break
        if pivot is None: continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        for rr in range(3):
            if rr != r and (rows[rr] >> c) & 1:
                rows[rr] ^= rows[r]
        r += 1
    return r


def flattening_check(multiset: List[int]) -> dict:
    """Check Σ rank(a_t) ≥ 27 for the multiset."""
    total = sum(mat33_rank(a) for a in multiset)
    return {'sum_rank_A': total, 'bound': 27, 'satisfies': total >= 27}


def run_swap_search(binary_path: Path, seed_multiset: List[int], 
                    max_iters: int = 50, outdir: Optional[Path] = None,
                    seed_name: str = "seed") -> dict:
    """Run the full swap hill-climb search."""
    t0 = time.time()
    
    print(f"Loading binary {binary_path}...", flush=True)
    masks, caps, dims, nrows = load_wang512_numpy(binary_path)
    print(f"  Loaded {nrows} rows in {time.time()-t0:.1f}s", flush=True)
    
    multiset = list(seed_multiset)
    history = []
    
    for iteration in range(max_iters):
        t1 = time.time()
        
        # Compute occupation
        occ = compute_occupation(masks, multiset)
        violated_idx, tight_idx, near_tight_idx = find_interesting_rows(occ, caps, masks, dims)
        
        n_viol = len(violated_idx)
        n_tight = len(tight_idx)
        n_near = len(near_tight_idx)
        
        # Violation details
        caps_i32 = caps.astype(np.int32)
        if n_viol > 0:
            excess = occ[violated_idx] - caps_i32[violated_idx]
            viol_dims = dims[violated_idx]
            dim_hist = dict(Counter(int(d) for d in viol_dims))
            excess_hist = dict(Counter(int(e) for e in excess))
        else:
            dim_hist = {}
            excess_hist = {}
        
        flat = flattening_check(multiset)
        
        print(f"\nIter {iteration}: violations={n_viol}, tight={n_tight}, near_tight={n_near}, "
              f"flat_sum={flat['sum_rank_A']}", flush=True)
        
        if n_viol > 0:
            print(f"  Violation dims: {dim_hist}, excess: {excess_hist}", flush=True)
        
        if n_viol == 0:
            print(f"*** ZERO VIOLATIONS! Wang-admissible candidate found! ***", flush=True)
            rec = {
                'iteration': iteration,
                'violations': 0,
                'tight': n_tight,
                'multiset': [int(x) for x in multiset],
                'flattening': flat,
                'elapsed_sec': time.time() - t1,
                'status': 'ADMISSIBLE'
            }
            history.append(rec)
            break
        
        # Evaluate all swaps
        t2 = time.time()
        best_i, best_d, viol_after, viol_now, top_swaps = evaluate_swaps_fast(
            masks, caps, multiset, violated_idx, tight_idx, occ)
        eval_time = time.time() - t2
        
        improvement = viol_now - viol_after
        print(f"  Best swap: remove A[{best_i}]={multiset[best_i]}, add {best_d}, "
              f"violations {viol_now} -> {viol_after} (improve {improvement}), "
              f"eval {eval_time:.1f}s", flush=True)
        
        rec = {
            'iteration': iteration,
            'violations': n_viol,
            'tight': n_tight,
            'near_tight': n_near,
            'violation_dim_hist': dim_hist,
            'violation_excess_hist': excess_hist,
            'best_swap': {'remove_pos': best_i, 'remove_dir': int(multiset[best_i]),
                         'add_dir': best_d, 'violations_after': viol_after,
                         'improvement': improvement},
            'top_swaps_head': top_swaps[:5] if top_swaps else [],
            'flattening': flat,
            'multiset': [int(x) for x in multiset],
            'eval_sec': eval_time,
            'elapsed_sec': time.time() - t1,
        }
        history.append(rec)
        
        if improvement <= 0:
            print(f"  No improving swap found. Stuck at {n_viol} violations.", flush=True)
            rec['status'] = 'STUCK'
            break
        
        # Apply swap
        multiset[best_i] = best_d
    
    result = {
        'schema': 'swap_search_v1',
        'seed_name': seed_name,
        'seed_multiset': [int(x) for x in seed_multiset],
        'final_multiset': [int(x) for x in multiset],
        'final_violations': history[-1].get('violations', -1),
        'iterations': len(history),
        'status': history[-1].get('status', 'MAX_ITERS'),
        'total_elapsed_sec': time.time() - t0,
        'history': history,
    }
    
    if outdir:
        outdir.mkdir(parents=True, exist_ok=True)
        out_path = outdir / f"{seed_name}_swap_search.json"
        out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
        print(f"\nSaved: {out_path}")
    
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--binary', type=Path, default=DEFAULT_BINARY)
    ap.add_argument('--seeds', type=Path, default=DEFAULT_SEEDS,
                    help='JSON from rank23_deletion_wang22.py')
    ap.add_argument('--max-seeds', type=int, default=6,
                    help='Max number of seeds to try')
    ap.add_argument('--max-iters', type=int, default=30)
    ap.add_argument('--outdir', type=Path, 
                    default=WORKSPACE / "data" / "swap_search")
    args = ap.parse_args()
    
    # Load seeds
    data = json.load(open(args.seeds))
    seeds = []
    for src in data['results']:
        for bd in src['best_deletions'][:3]:  # top 3 deletions per source
            name = f"{src['name']}_del{bd['deleted_A']}"
            seeds.append((name, bd['candidate_A_multiset'], bd['violation_count']))
    
    # Sort by violation count, take top seeds
    seeds.sort(key=lambda x: x[2])
    seeds = seeds[:args.max_seeds]
    
    print(f"=== Swap Search for n=22 Wang-admissible A-multisets ===")
    print(f"Seeds: {len(seeds)}, max_iters: {args.max_iters}")
    print(f"Binary: {args.binary}")
    
    all_results = []
    for name, multiset, init_viol in seeds:
        print(f"\n{'='*60}")
        print(f"Seed: {name}, initial violations: {init_viol}")
        print(f"Multiset: {multiset}")
        result = run_swap_search(args.binary, multiset, args.max_iters, args.outdir, name)
        all_results.append({
            'seed_name': name,
            'final_violations': result['final_violations'],
            'iterations': result['iterations'],
            'status': result['status'],
            'elapsed_sec': result['total_elapsed_sec'],
        })
    
    summary = {
        'schema': 'swap_search_summary_v1',
        'total_seeds': len(seeds),
        'results': all_results,
        'any_admissible': any(r['final_violations'] == 0 for r in all_results),
    }
    
    summary_path = args.outdir / "swap_search_summary.json"
    args.outdir.mkdir(parents=True, exist_ok=True)
    summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(f"\n{'='*60}")
    print(f"Summary saved: {summary_path}")
    for r in all_results:
        print(f"  {r['seed_name']}: {r['final_violations']} violations, "
              f"{r['iterations']} iters, {r['status']}, {r['elapsed_sec']:.1f}s")


if __name__ == '__main__':
    main()
