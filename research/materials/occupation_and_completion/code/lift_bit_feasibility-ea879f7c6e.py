#!/usr/bin/env python3
"""Lift-bit feasibility checker for quotient supports.

For a quotient pivot p and a quotient support S = {q_1,...,q_n}, each quotient
direction q has a lift bit epsilon_q in {0,1} indicating which preimage of q was
selected as the original A-direction:
  a(q, 0) = embed(q)         [bit h of a is 0]
  a(q, 1) = embed(q) XOR p   [bit h of a is 1]

where h = bit_length(p)-1 and embed inserts a zero bit at position h.

Every full-tensor subspace W gives the constraint:
  #{q in S : a(q, epsilon_q) in W} <= cap_full(W) = 20 - LB_full(W)

where LB_full is from the full-tensor Wang LUT.

For fixed S with n points, the lift-bit assignment is a vector epsilon in {0,1}^n.
If no epsilon satisfies all constraints, S is lift-infeasible.
If S is lift-infeasible, it cannot arise from any rank-20 decomposition with this pivot.

We also find inclusion-minimal infeasible subsets: A subset S such that
all 2^|A| lift assignments violate some constraint. This gives the cut
sum_{q in A} x_q <= |A|-1.
"""
from __future__ import annotations
import argparse, json, struct, time
from pathlib import Path
from collections import Counter
import numpy as np


def load_wang_lut(lut_path: Path) -> dict[int, int]:
    """Load the full-tensor Wang LUT: maps subspace_id -> lower_bound."""
    # Use the E11WANG1 format or the original LUT
    # For this script, we use the full 9-dimensional LUT
    import struct
    raw = lut_path.read_bytes()
    if raw[:8] == b"E11WANG1":
        # Binary row format, but this is a quotient binary, not what we want
        raise ValueError("Need full-tensor LUT, not quotient binary")
    # Try loading as numpy/json
    if lut_path.suffix == ".npy":
        return dict(enumerate(np.load(lut_path).tolist()))
    raise ValueError(f"Unknown LUT format: {lut_path}")


def load_full_rows_from_quotient(path: Path):
    """Load binary rows (256-bit mask + 4-byte cap)."""
    raw = path.read_bytes()
    assert raw[:8] == b"E11WANG1"
    nrows = int.from_bytes(raw[8:16], "little")
    masks, caps = [], []
    off = 16
    for _ in range(nrows):
        m = int.from_bytes(raw[off:off+32], "little")
        c = int.from_bytes(raw[off+32:off+36], "little", signed=True)
        masks.append(m); caps.append(c)
        off += 36
    return masks, caps


def embed(q: int, h: int) -> int:
    """Insert a zero bit at position h: lower h bits stay, upper bits shift left by 1."""
    low = q & ((1 << h) - 1)
    high = (q >> h) << (h + 1)
    return low | high


def original_direction(q: int, eps: int, pivot: int, h: int) -> int:
    """Reconstruct the original 9-bit A-direction from quotient q and lift bit eps."""
    e = embed(q, h)
    if eps == 0:
        return e
    else:
        return e ^ pivot


def check_lift_feasibility(support: list[int], pivot: int,
                           full_masks: list[int], full_caps: list[int],
                           n_full: int = 20) -> dict:
    """Check if any lift-bit assignment for the support is feasible.

    Uses DFS over epsilon assignments, pruning when a constraint is violated.
    Returns feasibility status and statistics.
    """
    h = int(pivot).bit_length() - 1
    n = len(support)

    # Precompute for each point: original direction for eps=0 and eps=1
    orig0 = [original_direction(q, 0, pivot, h) for q in support]
    orig1 = [original_direction(q, 1, pivot, h) for q in support]

    # Precompute row incidence: for each row, which points are in it for each eps
    # Row i has mask M_i: point j with eps=e contributes iff bit orig_e[j] is set in M_i
    # For efficiency, precompute for each (row, point): (in_at_0, in_at_1)
    # Then during DFS, maintain counts per row

    nrows = len(full_masks)
    # For each row, compute the count contribution for each point at each eps
    # To keep memory manageable, only track "interesting" rows (cap < n)
    interesting = [(i, full_masks[i], full_caps[i])
                   for i in range(nrows) if 0 < full_caps[i] < n]

    # For each interesting row, precompute incidence per point
    row_data = []
    for ri, (idx, mask, cap) in enumerate(interesting):
        inc0 = []  # points in row at eps=0
        inc1 = []  # points in row at eps=1
        for j in range(n):
            in0 = (mask >> orig0[j]) & 1
            in1 = (mask >> orig1[j]) & 1
            inc0.append(in0)
            inc1.append(in1)
        row_data.append((cap, inc0, inc1))

    # DFS over epsilon assignments
    epsilon = [0] * n
    counts = [0] * len(row_data)  # current count per interesting row
    # Initialize counts for all eps=0
    for ri, (cap, inc0, inc1) in enumerate(row_data):
        counts[ri] = sum(inc0)

    # Check initial (all eps=0) assignment
    def is_feasible():
        for ri, (cap, _, _) in enumerate(row_data):
            if counts[ri] > cap:
                return False
        return True

    # BFS/DFS: try flipping each point's eps from 0 to 1
    solutions = []
    nodes = 0
    max_depth = 0
    t0 = time.time()

    def dfs(pos):
        nonlocal nodes, max_depth
        nodes += 1
        if nodes > 10_000_000:
            return "LIMIT"
        if time.time() - t0 > 60:
            return "TIMEOUT"

        # Check feasibility
        for ri, (cap, _, _) in enumerate(row_data):
            if counts[ri] > cap:
                return None

        if pos == n:
            solutions.append(list(epsilon))
            if len(solutions) >= 10:
                return "FOUND_MANY"
            return "FOUND_ONE"

        if pos > max_depth:
            max_depth = pos

        # Try eps=0 (already set)
        result = dfs(pos + 1)
        if result in ("FOUND_MANY", "LIMIT", "TIMEOUT"):
            return result

        # Try eps=1: flip point pos from 0 to 1
        epsilon[pos] = 1
        for ri, (cap, inc0, inc1) in enumerate(row_data):
            counts[ri] += inc1[pos] - inc0[pos]
        result = dfs(pos + 1)
        if result in ("FOUND_MANY", "LIMIT", "TIMEOUT"):
            # restore
            for ri, (cap, inc0, inc1) in enumerate(row_data):
                counts[ri] -= inc1[pos] - inc0[pos]
            epsilon[pos] = 0
            return result
        # restore
        for ri, (cap, inc0, inc1) in enumerate(row_data):
            counts[ri] -= inc1[pos] - inc0[pos]
        epsilon[pos] = 0
        return result

    result = dfs(0)
    elapsed = time.time() - t0
    return {
        "feasible": len(solutions) > 0,
        "solutions_found": len(solutions),
        "first_solution": solutions[0] if solutions else None,
        "nodes": nodes,
        "max_depth": max_depth,
        "elapsed_sec": elapsed,
        "interesting_rows": len(row_data),
        "dfs_result": result,
    }


def find_minimal_cut(support, pivot, full_masks, full_caps, n_full=20):
    """Find an inclusion-minimal infeasible subset of the support.

    Strategy: start with full support (known infeasible), try removing each point.
    If still infeasible without point i, remove it. Otherwise keep it.
    """
    h = int(pivot).bit_length() - 1
    current = list(support)
    for _ in range(len(support)):
        removed_one = False
        for i in range(len(current)):
            trial = current[:i] + current[i+1:]
            res = check_lift_feasibility(trial, pivot, full_masks, full_caps, n_full)
            if not res["feasible"]:
                current = trial
                removed_one = True
                break
        if not removed_one:
            break
    return current


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot", type=int, required=True)
    ap.add_argument("--support", required=True, help="Support as comma-separated or JSON file")
    ap.add_argument("--full-rows", type=Path, required=True, help="Full-tensor Wang binary")
    ap.add_argument("--minimize", action="store_true")
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()

    # Parse support
    p = Path(args.support)
    if p.exists():
        data = json.loads(p.read_text())
        if isinstance(data, list):
            sup = [int(x) for x in data]
        else:
            for key in ["support", "solution"]:
                if key in data:
                    sup = [int(x) for x in data[key]]
                    break
            else:
                if "rounds" in data:
                    for r in reversed(data["rounds"]):
                        if r.get("fully_admissible") and r.get("solution"):
                            sup = [int(x) for x in r["solution"]]
                            break
    else:
        sup = [int(x) for x in args.support.split(",")]

    full_masks, full_caps = load_full_rows_from_quotient(args.full_rows)
    print(f"Support: {len(sup)} points, pivot: {args.pivot}")
    print(f"Full rows: {len(full_masks)}")

    t0 = time.time()
    result = check_lift_feasibility(sup, args.pivot, full_masks, full_caps)
    result["support"] = sup
    result["pivot"] = args.pivot
    print(f"Feasible: {result['feasible']}, nodes: {result['nodes']}, "
          f"elapsed: {result['elapsed_sec']:.3f}s")

    if args.minimize and not result["feasible"]:
        print("Finding minimal infeasible subset...")
        t1 = time.time()
        minimal = find_minimal_cut(sup, args.pivot, full_masks, full_caps)
        result["minimal_cut"] = minimal
        result["minimal_cut_size"] = len(minimal)
        result["minimize_elapsed_sec"] = time.time() - t1
        print(f"Minimal cut: {len(minimal)} points: {minimal}")

    result["total_elapsed_sec"] = time.time() - t0
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Saved {args.out}")


if __name__ == "__main__":
    main()
