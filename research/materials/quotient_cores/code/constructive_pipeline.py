#!/usr/bin/env python3
"""Smart constructive pipeline: seeded hill-climbing + fixed-A Brent completion.

Strategy: 
1. Seed from known rank-21 E11 supports by deleting 2 of 21 points -> 19-point seeds.
2. Evaluate each seed against the all-cap Wang system.
3. Hill-climb with plateau moves, large-neighborhood swap, row weighting.
4. Pipe zero- or near-zero-violation supports to fixed-A Brent completion.

Also runs the same pipeline on rank-2 and rank-3 quotient tensors.

Uses the compiled C++ hill-climber for speed, but adds Python orchestration for
seeding, Brent completion, and result tracking.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from itertools import combinations
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent
S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))

POOL_PATH = Path("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy")
WANG_BIN_DIR = SESSION / "workspace/data/wang_native/quotient_binaries"
HILLCLIMB = SESSION / "workspace/scripts/wang_hillclimb"
OUTDIR = SESSION / "workspace/data/constructive_pipeline"


def load_pool_supports() -> List[List[int]]:
    """Load distinct quotient A-directions from the known rank-21 E11 pool."""
    pool = np.load(str(POOL_PATH))
    supports = []
    for row_idx in range(pool.shape[0]):
        terms = pool[row_idx].reshape(-1, 3)
        u_masks = [int(t[0]) & 0xFF for t in terms]
        nonzero = sorted(set(m for m in u_masks if m != 0))
        supports.append(nonzero)
    return supports


def load_binary_constraints(path: str) -> List[Tuple[int, List[int]]]:
    """Load E11WANG1 format constraints. Returns list of (cap, point_list)."""
    import struct
    rows = []
    with open(path, 'rb') as f:
        magic = f.read(8)
        if not magic.startswith(b'E11WANG1'):
            raise ValueError(f"Bad magic: {magic}")
        while True:
            hdr = f.read(4)
            if len(hdr) < 4:
                break
            cap = struct.unpack('<I', hdr)[0]
            words = struct.unpack('<4Q', f.read(32))
            pts = []
            for w_idx, w in enumerate(words):
                for bit in range(64):
                    if w & (1 << bit):
                        pts.append(w_idx * 64 + bit)
            rows.append((cap, pts))
    return rows


def evaluate_support(support: List[int], constraints: List[Tuple[int, List[int]]]) -> int:
    """Count violated constraints for a given support."""
    support_set = set(support)
    violations = 0
    for cap, pts in constraints:
        occ = sum(1 for p in pts if p in support_set)
        if occ > cap:
            violations += 1
    return violations


def fast_evaluate_numpy(support: List[int], bin_path: str) -> int:
    """Fast violation count using the compiled hill-climber in eval mode."""
    supp_str = ",".join(str(s) for s in sorted(support))
    # Use the hill-climber with 0 restarts just to get the initial violation count
    # This is a hack; better to have a dedicated eval mode.
    # For now, use Python evaluation.
    return -1  # placeholder


def generate_deletion_seeds(support: List[int], target: int) -> List[List[int]]:
    """Generate all C(n, n-target) deletion seeds from a support."""
    n = len(support)
    delete_count = n - target
    if delete_count <= 0:
        return [support[:target]]
    seeds = []
    for to_delete in combinations(range(n), delete_count):
        seed = [support[i] for i in range(n) if i not in to_delete]
        seeds.append(sorted(seed))
    return seeds


def run_hillclimb_from_seed(seed: List[int], bin_path: str, target: int,
                            time_limit: float = 30.0, restarts: int = 5) -> Dict:
    """Run the C++ hill-climber seeded from a specific support."""
    seed_str = ",".join(str(s) for s in sorted(seed))
    out_path = OUTDIR / f"hillclimb_seed_{hash(seed_str) & 0xFFFFFFFF:08x}.json"
    
    cmd = [
        str(HILLCLIMB),
        "--constraints", str(bin_path),
        "--target", str(target),
        "--restarts", str(restarts),
        "--time-limit", str(int(time_limit)),
        "--seed-support", seed_str,
        "--output", str(out_path),
    ]
    
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=time_limit + 10)
        if out_path.exists():
            return json.loads(out_path.read_text())
        return {"status": "no_output", "returncode": result.returncode, "stderr": result.stderr[:500]}
    except subprocess.TimeoutExpired:
        return {"status": "timeout"}
    except Exception as e:
        return {"status": "error", "message": str(e)}


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["e11_seed", "rank2", "rank3", "all"], default="e11_seed")
    ap.add_argument("--max-seeds", type=int, default=50)
    ap.add_argument("--target", type=int, default=19)
    ap.add_argument("--time-per-seed", type=float, default=10.0)
    ap.add_argument("--eval-only", action="store_true",
                    help="Only evaluate seeds, don't hill-climb")
    args = ap.parse_args()
    
    OUTDIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    
    if args.mode == "e11_seed":
        # Load pool and generate deletion seeds
        print("Loading rank-21 E11 pool...")
        all_supports = load_pool_supports()
        
        # Find pool rows with exactly 21 distinct nonzero A-directions
        # (some may have fewer due to repeats)
        good_rows = [(i, s) for i, s in enumerate(all_supports) if len(s) >= 21]
        print(f"  Pool rows with >= 21 distinct directions: {len(good_rows)}")
        
        # Find the best rows (most distinct directions)
        good_rows.sort(key=lambda x: -len(x[1]))
        print(f"  Max distinct: {len(good_rows[0][1]) if good_rows else 0}")
        
        # For rows with exactly 21 distinct, deletion gives C(21,2)=210 seeds each
        target_rows = [(i, s) for i, s in good_rows if len(s) == 21][:5]
        print(f"  Using {len(target_rows)} rows with 21 distinct directions")
        
        # Load constraints
        bin_path = str(WANG_BIN_DIR / "e11_all_n19.bin")
        if not Path(bin_path).exists():
            print(f"ERROR: {bin_path} not found")
            return
        
        print("Loading constraints...")
        constraints = load_binary_constraints(bin_path)
        print(f"  Loaded {len(constraints)} rows")
        
        # Evaluate seeds
        results = []
        best_viols = float('inf')
        seeds_tested = 0
        
        for row_idx, support in target_rows:
            seeds = generate_deletion_seeds(support, args.target)
            print(f"\n  Row {row_idx}: {len(support)} pts -> {len(seeds)} deletion seeds")
            
            for seed in seeds[:args.max_seeds]:
                viols = evaluate_support(seed, constraints)
                seeds_tested += 1
                if viols < best_viols:
                    best_viols = viols
                    print(f"    NEW BEST: seed from row {row_idx}, viols={viols}, support={seed}")
                
                results.append({
                    "source_row": row_idx,
                    "support": seed,
                    "violations": viols,
                })
                
                if viols == 0:
                    print(f"\n  *** ZERO-VIOLATION SUPPORT FOUND! ***")
                    print(f"  Support: {seed}")
                    # TODO: pipe to fixed-A Brent completion
                    break
            
            if best_viols == 0:
                break
        
        # Sort by violations
        results.sort(key=lambda x: x["violations"])
        
        summary = {
            "mode": "e11_seed",
            "target": args.target,
            "seeds_tested": seeds_tested,
            "best_violations": best_viols,
            "top_10": results[:10],
            "elapsed_sec": time.time() - t0,
        }
        
        out_path = OUTDIR / "e11_deletion_seed_evaluation.json"
        out_path.write_text(json.dumps(summary, indent=2))
        print(f"\nTested {seeds_tested} seeds, best violations: {best_viols}")
        print(f"Saved {out_path}")
        print(json.dumps(summary, indent=2)[:2000])


if __name__ == "__main__":
    main()
