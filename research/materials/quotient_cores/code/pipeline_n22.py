#!/usr/bin/env python3
"""High-throughput n=22 candidate generation and completion pipeline.

Strategy: generate many diverse Wang-admissible A-multisets from random seeds,
then test each through trace filter and fixed-A Brent completion.

Random seeds: pick 22 random nonzero directions from [1,511], hill-climb
to zero Wang violations, then test.  This explores much more of the search
space than perturbations of a single rank-23 scheme.
"""
from __future__ import annotations
import argparse, json, os, struct, subprocess, sys, time
from collections import Counter
from pathlib import Path
from typing import List, Tuple, Optional
import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

WORKSPACE = SCRIPT_DIR.parent
DEFAULT_BINARY = WORKSPACE / "data" / "pivot_fixed_n22_binary" / "full_wang512_cap21_len22_all_dim9_allbinding.bin"


def load_wang512_numpy(path: Path):
    raw = path.read_bytes()
    assert raw[:8] == b"WANG512\x01"
    nrows = struct.unpack_from("<I", raw, 8)[0]
    rec_size = 68
    data = np.frombuffer(raw, dtype=np.uint8, offset=12)
    data = data[:nrows * rec_size].reshape(nrows, rec_size)
    caps = data[:, 0].copy()
    dims = data[:, 1].copy()
    mask_bytes = data[:, 4:68].copy()
    masks_u64 = mask_bytes.view(np.uint64).reshape(nrows, 8)
    return masks_u64, caps, dims, nrows


def compute_occupation(masks, multiset):
    nrows = masks.shape[0]
    occ = np.zeros(nrows, dtype=np.int32)
    cnt = Counter(multiset)
    for d, mult in cnt.items():
        w, b = d >> 6, d & 63
        occ += mult * ((masks[:, w] >> np.uint64(b)) & np.uint64(1)).astype(np.int32)
    return occ


def swap_search(masks, caps, multiset, max_iters=50):
    """Hill-climb to zero violations. Returns (final_multiset, violations, iters)."""
    ms = list(multiset)
    for it in range(max_iters):
        occ = compute_occupation(masks, ms)
        caps_i32 = caps.astype(np.int32)
        diff = occ - caps_i32
        violated_idx = np.where(diff > 0)[0]
        n_viol = len(violated_idx)
        if n_viol == 0:
            return ms, 0, it
        
        tight_idx = np.where(diff == 0)[0]
        excess = diff[violated_idx]
        fixable_v = violated_idx[excess == 1]
        n_fix = len(fixable_v)
        n_tight = len(tight_idx)
        
        if n_fix == 0:
            return ms, n_viol, it  # stuck, all excess > 1
        
        fix_masks = masks[fixable_v]
        tight_masks = masks[tight_idx]
        
        fix_has = np.zeros((512, n_fix), dtype=np.float32)
        tight_has = np.zeros((512, n_tight), dtype=np.float32)
        for d in range(1, 512):
            w, b = d >> 6, d & 63
            fix_has[d] = ((fix_masks[:, w] >> np.uint64(b)) & np.uint64(1)).astype(np.float32)
            tight_has[d] = ((tight_masks[:, w] >> np.uint64(b)) & np.uint64(1)).astype(np.float32)
        
        fix_sum_vec = fix_has.sum(axis=1)
        tight_sum_vec = tight_has.sum(axis=1)
        
        best_score = -1e9
        best_i, best_d = -1, -1
        
        for i in range(len(ms)):
            ai = ms[i]
            ai_fix = fix_has[ai]
            ai_tight = tight_has[ai]
            ai_fix_sum = float(ai_fix.sum())
            
            overlap_fix = fix_has @ ai_fix
            fixed_all = ai_fix_sum - overlap_fix
            overlap_tight = tight_has @ ai_tight
            created_all = tight_sum_vec - overlap_tight
            
            scores = fixed_all - created_all
            scores[0] = -1e6
            scores[ai] = -1e6
            
            bd = int(np.argmax(scores))
            if scores[bd] > best_score:
                best_score = scores[bd]
                best_i, best_d = i, bd
        
        if best_score <= 0:
            return ms, n_viol, it  # stuck
        
        ms[best_i] = best_d
    
    # Check final
    occ = compute_occupation(masks, ms)
    n_viol = int(np.sum(occ > caps.astype(np.int32)))
    return ms, n_viol, max_iters


def mat33_rank(m):
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


def trace_filter(multiset):
    """Run trace filter, return True if consistent."""
    cmd = [sys.executable, str(SCRIPT_DIR / 'full_tight_trace_filter.py'),
           '--multiset', ','.join(str(x) for x in multiset),
           '--out', '/dev/null']
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=30,
                             env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
        if proc.returncode == 0:
            data = json.loads(proc.stdout)
            return data.get('full_trace_consistent', False), data
    except:
        pass
    return False, {}


def brent_completion(multiset, outdir, name, timeout=300):
    """Run fixed-A Brent completion. Returns (sat, result_dict)."""
    outdir = Path(outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    cmd = [sys.executable, str(SCRIPT_DIR / 'full_fixed_a_completion.py'),
           '--multiset', ','.join(str(x) for x in multiset),
           '--outdir', str(outdir), '--name', name, '--timeout', str(timeout)]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout+60,
                             env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
        if proc.returncode == 0:
            data = json.loads(proc.stdout)
            return data.get('sat', None), data
    except Exception as e:
        return None, {'error': str(e)}
    return None, {'error': 'subprocess failed'}


def generate_random_seed(rng, r=22):
    """Generate a random 22-element multiset from [1,511]."""
    return sorted(rng.choice(range(1, 512), size=r, replace=False).tolist())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--binary', type=Path, default=DEFAULT_BINARY)
    ap.add_argument('--n-random', type=int, default=20, help='Random seeds to try')
    ap.add_argument('--max-swap-iters', type=int, default=50)
    ap.add_argument('--brent-timeout', type=int, default=600)
    ap.add_argument('--outdir', type=Path, default=WORKSPACE / "data" / "pipeline_results")
    ap.add_argument('--seed', type=int, default=42)
    ap.add_argument('--also-deletion-seeds', action='store_true')
    args = ap.parse_args()
    
    t0 = time.time()
    print(f"Loading binary...", flush=True)
    masks, caps, dims, nrows = load_wang512_numpy(args.binary)
    print(f"  Loaded {nrows} rows in {time.time()-t0:.1f}s", flush=True)
    
    rng = np.random.default_rng(args.seed)
    args.outdir.mkdir(parents=True, exist_ok=True)
    
    results = []
    admissible = []
    trace_passed = []
    sat_found = []
    
    # Generate and test candidates
    seeds = []
    
    # Add deletion seeds if requested
    if args.also_deletion_seeds:
        del_path = WORKSPACE / "data" / "pivot_fixed_n22" / "rank23_deletion_wang22.json"
        if del_path.exists():
            data = json.load(open(del_path))
            for src in data['results']:
                for bd in src['best_deletions'][:3]:
                    seeds.append((f"del_{src['name']}_{bd['deleted_A']}", bd['candidate_A_multiset']))
    
    # Random seeds
    for i in range(args.n_random):
        seeds.append((f"random_{args.seed}_{i}", generate_random_seed(rng)))
    
    for idx, (name, seed) in enumerate(seeds):
        print(f"\n--- Candidate {idx+1}/{len(seeds)}: {name} ---", flush=True)
        t1 = time.time()
        
        ms, n_viol, iters = swap_search(masks, caps, seed, args.max_swap_iters)
        search_time = time.time() - t1
        
        flat_sum = sum(mat33_rank(a) for a in ms)
        rec = {
            'name': name,
            'seed': [int(x) for x in seed],
            'final_multiset': [int(x) for x in ms],
            'violations': n_viol,
            'swap_iters': iters,
            'search_sec': search_time,
            'flat_sum_A': flat_sum,
        }
        
        print(f"  Search: {n_viol} violations after {iters} iters, {search_time:.1f}s, flat={flat_sum}", flush=True)
        
        if n_viol > 0:
            rec['status'] = 'NOT_ADMISSIBLE'
            results.append(rec)
            continue
        
        admissible.append(rec)
        
        # Trace filter
        t2 = time.time()
        trace_ok, trace_data = trace_filter(ms)
        trace_time = time.time() - t2
        rec['trace_consistent'] = trace_ok
        rec['trace_sec'] = trace_time
        rec['trace_tight_count'] = trace_data.get('tight_lambda_count', 0)
        
        print(f"  Trace: {'CONSISTENT' if trace_ok else 'INCONSISTENT'}, "
              f"{rec['trace_tight_count']} tight, {trace_time:.2f}s", flush=True)
        
        if not trace_ok:
            rec['status'] = 'TRACE_REJECTED'
            results.append(rec)
            continue
        
        trace_passed.append(rec)
        
        # Brent completion
        t3 = time.time()
        brent_dir = args.outdir / "brent" / name
        sat, brent_data = brent_completion(ms, brent_dir, name, args.brent_timeout)
        brent_time = time.time() - t3
        rec['brent_sat'] = sat
        rec['brent_sec'] = brent_time
        rec['brent_returncode'] = brent_data.get('returncode', -1)
        rec['brent_vars'] = brent_data.get('vars', 0)
        rec['brent_clauses'] = brent_data.get('clauses', 0)
        
        if sat is True:
            rec['status'] = 'SAT_FOUND'
            rec['verification_diff'] = brent_data.get('verification_diff')
            sat_found.append(rec)
            print(f"  *** SAT! Brent completion found valid B/C! diff={rec['verification_diff']} ***", flush=True)
            print(f"  Witness: {brent_dir}/{name}_witness.json", flush=True)
        elif sat is False:
            rec['status'] = 'BRENT_UNSAT'
            print(f"  UNSAT in {brent_time:.1f}s ({brent_data.get('vars',0)} vars, "
                  f"{brent_data.get('clauses',0)} clauses)", flush=True)
        else:
            rec['status'] = 'BRENT_UNKNOWN'
            print(f"  UNKNOWN/timeout in {brent_time:.1f}s", flush=True)
        
        results.append(rec)
    
    # Summary
    summary = {
        'schema': 'pipeline_v1',
        'total_seeds': len(seeds),
        'admissible_count': len(admissible),
        'trace_passed_count': len(trace_passed),
        'sat_count': len(sat_found),
        'total_elapsed_sec': time.time() - t0,
        'results': results,
    }
    
    out = args.outdir / "pipeline_summary.json"
    out.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    
    print(f"\n{'='*60}")
    print(f"Pipeline complete: {len(seeds)} seeds → {len(admissible)} admissible → "
          f"{len(trace_passed)} trace-passed → {len(sat_found)} SAT")
    print(f"Total time: {time.time()-t0:.1f}s")
    print(f"Summary: {out}")
    
    if sat_found:
        print(f"\n*** RANK-22 ALGORITHM FOUND! ***")
        for r in sat_found:
            print(f"  {r['name']}: A={r['final_multiset']}")


if __name__ == '__main__':
    main()
