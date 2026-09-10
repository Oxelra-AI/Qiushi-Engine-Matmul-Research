#!/usr/bin/env python3
"""Direct lift-bit feasibility using the Wang LUT (no binary generation needed).

Loads the full 8.2M-entry LUT, extracts rows relevant to a given quotient
support, and runs DFS over lift-bit assignments.
"""
import json, struct, time, argparse, sys, pickle
from pathlib import Path
from collections import Counter
import numpy as np

S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))


def embed(q, h):
    low = q & ((1 << h) - 1)
    high = (q >> h) << (h + 1)
    return low | high


def load_lut_and_build_rows(lut_path, support, pivot, max_cap=5):
    """Build lift-bit rows directly from the LUT."""
    from wang_capacity_lazy import unpack_basis
    from core_capacity_from_wang_lut import load_lut

    h = int(pivot).bit_length() - 1
    n = len(support)
    orig0 = [embed(q, h) for q in support]
    orig1 = [embed(q, h) ^ pivot for q in support]

    lut, _ = load_lut(lut_path)
    print(f"  LUT entries: {len(lut)}")

    # For each LUT entry, compute cap at length 20
    # and check if any support point's original direction falls in it
    binding = []
    cap_hist = Counter()
    dim_hist = Counter()
    rows_checked = 0

    for key9, lb0 in lut.items():
        lb = int(lb0)
        cap = 20 - lb
        rows_checked += 1
        if cap <= 0 or cap >= n:
            continue  # non-binding
        if cap > max_cap:
            continue
        dim = int(key9) & 0xF
        basis = list(unpack_basis(int(key9)))
        pts_set = set()
        d = len(basis)
        for m in range(1, 1 << d):
            v = 0
            for i, b in enumerate(basis):
                if (m >> i) & 1:
                    v ^= int(b)
            pts_set.add(v)

        # Check which support points (at each eps) fall in this subspace
        in0 = [1 if orig0[j] in pts_set else 0 for j in range(n)]
        in1 = [1 if orig1[j] in pts_set else 0 for j in range(n)]
        if any(in0[j] or in1[j] for j in range(n)):
            binding.append((cap, in0, in1))
            cap_hist[cap] += 1
            dim_hist[dim] += 1

    print(f"  Rows checked: {rows_checked}")
    print(f"  Binding rows: {len(binding)}")
    print(f"  Cap hist: {dict(sorted(cap_hist.items()))}")
    print(f"  Dim hist: {dict(sorted(dim_hist.items()))}")
    return binding


def dfs_check(binding, n, max_nodes=50_000_000, max_sec=300):
    """DFS over lift-bit assignments."""
    nB = len(binding)
    counts = [0] * nB
    eps = [0] * n
    solutions = []
    nodes = [0]
    t0 = time.time()

    def dfs(pos):
        nodes[0] += 1
        if nodes[0] > max_nodes:
            return "LIMIT"
        if time.time() - t0 > max_sec:
            return "TIMEOUT"
        for ri in range(nB):
            if counts[ri] > binding[ri][0]:
                return None
        if pos == n:
            solutions.append(tuple(eps))
            return "FOUND" if len(solutions) >= 3 else None

        # Try eps[pos] = 0
        eps[pos] = 0
        for ri in range(nB):
            counts[ri] += binding[ri][1][pos]
        r = dfs(pos + 1)
        for ri in range(nB):
            counts[ri] -= binding[ri][1][pos]
        if r in ("FOUND", "LIMIT", "TIMEOUT"):
            return r

        # Try eps[pos] = 1
        eps[pos] = 1
        for ri in range(nB):
            counts[ri] += binding[ri][2][pos]
        r = dfs(pos + 1)
        for ri in range(nB):
            counts[ri] -= binding[ri][2][pos]
        eps[pos] = 0
        if r in ("FOUND", "LIMIT", "TIMEOUT"):
            return r
        return None

    result = dfs(0)
    elapsed = time.time() - t0
    return {
        "feasible": len(solutions) > 0,
        "n_solutions": len(solutions),
        "first_eps": list(solutions[0]) if solutions else None,
        "nodes": nodes[0],
        "elapsed_sec": elapsed,
        "binding_rows": nB,
        "dfs_result": result,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot", type=int, required=True)
    ap.add_argument("--support", required=True)
    ap.add_argument("--max-cap", type=int, default=5)
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

    lut_path = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
    print(f"Pivot: {args.pivot}, Support: {len(sup)} pts, max_cap: {args.max_cap}")

    t0 = time.time()
    binding = load_lut_and_build_rows(lut_path, sup, args.pivot, args.max_cap)
    build_time = time.time() - t0
    print(f"  Row build time: {build_time:.1f}s")

    result = dfs_check(binding, len(sup))
    result["support"] = sup
    result["pivot"] = args.pivot
    result["max_cap"] = args.max_cap
    result["row_build_sec"] = build_time
    print(f"\nFeasible: {result['feasible']}, nodes: {result['nodes']}, "
          f"DFS time: {result['elapsed_sec']:.3f}s, total: {time.time()-t0:.1f}s")

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Saved {args.out}")


if __name__ == "__main__":
    main()
