#!/usr/bin/env python3
"""Smart seeded Wang evaluation: deletion seeds from known rank-21 E11 supports.

Strategy: take known rank-21 E11 supports with exactly 21 distinct directions,
delete all C(21,2)=210 pairs, evaluate each 19-point support against the
complete Wang system, and report the best violation counts.

Zero-violation supports would be candidates for fixed-A Brent completion.
"""
from __future__ import annotations

import json
import os
import struct
import sys
import time
from itertools import combinations
from pathlib import Path

import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent
S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))

POOL_PATH = Path("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy")
OUTDIR = SESSION / "workspace/data/constructive_pipeline"


def load_binary_constraints_correct(path: str):
    """Load E11WANG1 format with correct BBHQQQQ per-row layout."""
    rows = []
    with open(path, 'rb') as f:
        magic = f.read(8)
        assert magic == b'E11WANG1', f"Bad magic: {magic}"
        nrows = struct.unpack('<I', f.read(4))[0]
        for _ in range(nrows):
            hdr = f.read(4)  # cap(1) + dim(1) + reserved(2)
            cap = hdr[0]
            words = struct.unpack('<4Q', f.read(32))
            pts = []
            for w_idx, w in enumerate(words):
                for bit in range(64):
                    if w & (1 << bit):
                        pts.append(w_idx * 64 + bit)
            rows.append((cap, pts))
    return rows


def evaluate_support_fast(support_set: set, constraint_masks: list, constraint_caps: list) -> int:
    """Fast violation count using precomputed numpy arrays."""
    violations = 0
    for i, (mask_words, cap) in enumerate(zip(constraint_masks, constraint_caps)):
        occ = 0
        for p in support_set:
            w_idx = p >> 6
            bit = p & 63
            if mask_words[w_idx] & (1 << bit):
                occ += 1
        if occ > cap:
            violations += 1
    return violations


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-rows", type=int, default=5, help="Max pool rows to use")
    ap.add_argument("--constraints", type=str, 
                    default=str(SESSION / "workspace/data/wang_native/quotient_binaries/e11_all_n19.bin"))
    args = ap.parse_args()
    
    OUTDIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    
    print("Loading rank-21 E11 pool...")
    pool = np.load(str(POOL_PATH))
    
    # Extract distinct 8-bit A-supports
    supports = []
    for row_idx in range(pool.shape[0]):
        terms = pool[row_idx].reshape(-1, 3)
        u_masks = sorted(set(int(t[0]) & 0xFF for t in terms if int(t[0]) & 0xFF != 0))
        supports.append((row_idx, u_masks))
    
    # Filter to rows with exactly 21 distinct directions
    good_rows = [(idx, s) for idx, s in supports if len(s) == 21]
    print(f"  Pool rows with 21 distinct directions: {len(good_rows)}")
    
    if not good_rows:
        # Use rows with most distinct directions
        supports.sort(key=lambda x: -len(x[1]))
        good_rows = supports[:args.max_rows]
        print(f"  Using top {len(good_rows)} rows (max distinct: {len(good_rows[0][1])})")
    else:
        good_rows = good_rows[:args.max_rows]
    
    print(f"\nLoading constraints from {args.constraints}...")
    raw_rows = load_binary_constraints_correct(args.constraints)
    print(f"  Loaded {len(raw_rows)} constraint rows")
    
    # Precompute constraint arrays for fast evaluation
    caps = []
    masks = []
    for cap, pts in raw_rows:
        caps.append(cap)
        words = [0, 0, 0, 0]
        for p in pts:
            words[p >> 6] |= 1 << (p & 63)
        masks.append(words)
    
    # Evaluate deletion seeds
    results = []
    best_viols = float('inf')
    best_support = None
    total_seeds = 0
    
    for pool_idx, support in good_rows:
        n = len(support)
        seeds = list(combinations(range(n), n - 19))  # indices to DELETE
        print(f"\n  Pool row {pool_idx}: {n} pts -> {len(seeds)} deletion seeds")
        
        for del_indices in seeds:
            seed = [support[i] for i in range(n) if i not in del_indices]
            seed_set = set(seed)
            
            viols = 0
            for msk, cap in zip(masks, caps):
                occ = 0
                for p in seed_set:
                    if msk[p >> 6] & (1 << (p & 63)):
                        occ += 1
                if occ > cap:
                    viols += 1
            
            total_seeds += 1
            if viols < best_viols:
                best_viols = viols
                best_support = sorted(seed)
                deleted = [support[i] for i in del_indices]
                print(f"    NEW BEST: viols={viols}, seed from row {pool_idx}, "
                      f"deleted={deleted}, support={best_support}")
            
            if viols == 0:
                print(f"\n  *** ZERO-VIOLATION SUPPORT FOUND! ***")
                break
        
        if best_viols == 0:
            break
    
    # Top results
    summary = {
        "mode": "e11_deletion_seeds",
        "target": 19,
        "total_seeds_tested": total_seeds,
        "pool_rows_used": len(good_rows),
        "best_violations": best_viols,
        "best_support": best_support,
        "elapsed_sec": time.time() - t0,
    }
    
    out_path = OUTDIR / "e11_deletion_seed_evaluation.json"
    out_path.write_text(json.dumps(summary, indent=2))
    print(f"\nTested {total_seeds} seeds, best violations: {best_viols}")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
