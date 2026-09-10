#!/usr/bin/env python3
"""Correct lift-bit feasibility checker using WANG512 full-tensor rows.

For pivot p (h = bit_length(p)-1), quotient direction q, lift bit eps:
  a(q, 0) = embed(q)         (bit h=0)
  a(q, 1) = embed(q) ^ p     (bit h=1)

Full-tensor row W with cap c: #{q in S : a(q, eps_q) in W} <= c.

DFS over eps assignments with correct incremental counting.
"""
import json, struct, time, argparse
from pathlib import Path
from collections import Counter
import numpy as np


def load_wang512(path):
    raw = path.read_bytes()
    assert raw[:8] == b"WANG512\x01", f"Bad magic: {raw[:8]}"
    nrows = struct.unpack_from("<I", raw, 8)[0]
    masks, caps = [], []
    off = 12
    for _ in range(nrows):
        cap, dim, _ = struct.unpack_from("<BBH", raw, off)
        off += 4
        words = struct.unpack_from("<8Q", raw, off)
        off += 64
        m = 0
        for i, w in enumerate(words):
            m |= w << (64 * i)
        masks.append(m)
        caps.append(cap)
    return masks, caps


def embed(q, h):
    low = q & ((1 << h) - 1)
    high = (q >> h) << (h + 1)
    return low | high


def check_lift(support, pivot, masks512, caps512):
    """Correct DFS over lift-bit assignments with incremental counting."""
    h = int(pivot).bit_length() - 1
    n = len(support)
    orig0 = [embed(q, h) for q in support]
    orig1 = [embed(q, h) ^ pivot for q in support]

    # Filter to rows where at least one point is affected and cap < n
    binding = []
    for i in range(len(masks512)):
        cap = caps512[i]
        if cap <= 0 or cap >= n:
            continue
        mask = masks512[i]
        in0 = [(mask >> orig0[j]) & 1 for j in range(n)]
        in1 = [(mask >> orig1[j]) & 1 for j in range(n)]
        if any(in0[j] or in1[j] for j in range(n)):
            binding.append((cap, in0, in1))

    print(f"  Binding rows: {len(binding)} (from {len(masks512)} total)")
    nB = len(binding)

    # DFS: start with counts=0, incrementally add each point
    counts = [0] * nB
    eps = [0] * n
    solutions = []
    nodes = [0]
    t0 = time.time()

    def prunable():
        """Check if any row already exceeds cap (can't be reduced by future decisions)."""
        for ri in range(nB):
            if counts[ri] > binding[ri][0]:
                return True
        return False

    def dfs(pos):
        nodes[0] += 1
        if nodes[0] > 50_000_000:
            return "LIMIT"
        if time.time() - t0 > 300:
            return "TIMEOUT"
        if prunable():
            return None
        if pos == n:
            solutions.append(tuple(eps))
            return "FOUND" if len(solutions) >= 5 else None

        # Try eps[pos] = 0
        eps[pos] = 0
        for ri in range(nB):
            counts[ri] += binding[ri][1][pos]  # in0
        r = dfs(pos + 1)
        for ri in range(nB):
            counts[ri] -= binding[ri][1][pos]
        if r in ("FOUND", "LIMIT", "TIMEOUT"):
            return r

        # Try eps[pos] = 1
        eps[pos] = 1
        for ri in range(nB):
            counts[ri] += binding[ri][2][pos]  # in1
        r = dfs(pos + 1)
        for ri in range(nB):
            counts[ri] -= binding[ri][2][pos]
        eps[pos] = 0
        if r in ("FOUND", "LIMIT", "TIMEOUT"):
            return r
        return None

    result = dfs(0)
    elapsed = time.time() - t0
    # Reconstruct original directions for first solution
    first_orig = None
    if solutions:
        first_orig = []
        for j in range(n):
            if solutions[0][j] == 0:
                first_orig.append(orig0[j])
            else:
                first_orig.append(orig1[j])
    return {
        "feasible": len(solutions) > 0,
        "n_solutions": len(solutions),
        "first_eps": list(solutions[0]) if solutions else None,
        "first_original_dirs": first_orig,
        "nodes": nodes[0],
        "elapsed_sec": elapsed,
        "binding_rows": len(binding),
        "dfs_result": result,
    }


def minimize_cut(support, pivot, masks512, caps512):
    """Greedy minimization: remove points while infeasibility holds."""
    current = list(support)
    for _ in range(len(support)):
        removed = False
        for i in range(len(current)):
            trial = current[:i] + current[i+1:]
            r = check_lift(trial, pivot, masks512, caps512)
            if not r["feasible"]:
                print(f"    Removed {current[i]}: still infeasible "
                      f"({len(trial)} pts, {r['nodes']} nodes)")
                current = trial
                removed = True
                break
            else:
                print(f"    Keep {current[i]}: feasible without it "
                      f"({r['nodes']} nodes)")
        if not removed:
            break
    return current


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot", type=int, required=True)
    ap.add_argument("--support", required=True)
    ap.add_argument("--full-rows", type=Path, required=True)
    ap.add_argument("--minimize", action="store_true")
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()

    p = Path(args.support)
    if p.exists():
        d = json.loads(p.read_text())
        if isinstance(d, list):
            sup = [int(x) for x in d]
        else:
            for k in ["support", "solution"]:
                if k in d:
                    sup = [int(x) for x in d[k]]; break
            else:
                for r in reversed(d.get("rounds", [])):
                    if r.get("fully_admissible") and r.get("solution"):
                        sup = [int(x) for x in r["solution"]]; break
    else:
        sup = [int(x) for x in args.support.split(",")]

    masks512, caps512 = load_wang512(args.full_rows)
    print(f"Pivot: {args.pivot}, Support: {len(sup)} pts, Full rows: {len(masks512)}")

    result = check_lift(sup, args.pivot, masks512, caps512)
    result["support"] = sup
    result["pivot"] = args.pivot
    print(f"\nFeasible: {result['feasible']}, nodes: {result['nodes']}, "
          f"time: {result['elapsed_sec']:.3f}s")

    if args.minimize and not result["feasible"]:
        print("\nMinimizing infeasible subset...")
        t0 = time.time()
        cut = minimize_cut(sup, args.pivot, masks512, caps512)
        result["minimal_cut"] = cut
        result["minimal_cut_size"] = len(cut)
        result["minimize_elapsed_sec"] = time.time() - t0
        print(f"\nMinimal cut: {len(cut)} points: {cut}")

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Saved {args.out}")


if __name__ == "__main__":
    main()
