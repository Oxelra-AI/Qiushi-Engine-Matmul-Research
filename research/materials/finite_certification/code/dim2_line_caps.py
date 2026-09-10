#!/usr/bin/env python3
"""Check line caps at each of the eight load-bearing dim-2 orbits 484-491.

The review warns: the occupation CP-SAT/MILP models use integer multiplicity
variables (correct), but safe-DFS certificates enumerate distinct supports.
If any quotient line cap > 1 at the target support size, a distinct-support DFS
proves the wrong statement.

For a dim-2 node W with quotient dimension k=7, quotient lines are 1-dim
subspaces of F_2^7.  The line cap is  L - LB(U), where U is the dim-3
superspace of W obtained by lifting the line.  If this cap is 1 for all
lines at target L = LB(W) = 18, then any length-18 A-multiset supported
on distinct quotient directions is the same as the integer problem,
and safe-DFS is valid.
"""
from __future__ import annotations
import json, pickle, sys, time
from pathlib import Path
from collections import Counter

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from node_local_occupation_closure import (
    rref_basis, pack_basis, free_bits_from_rref, lift_q
)

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
CACHE_PATH = Path("data/wang_f2_lb20/wang_orbit_closed_cache.pkl")
OUT = Path("data/audit/dim2_line_caps.json")


def main():
    with LUT_PATH.open("rb") as f:
        data = pickle.load(f)
    lut = data["lut"] if isinstance(data, dict) and "lut" in data else data
    with CACHE_PATH.open("rb") as f:
        cache = pickle.load(f)

    orbits = cache["orbits"]
    target_indices = [484, 485, 486, 487, 488, 489, 490, 491]
    results = []

    for idx in target_indices:
        orb = next(o for o in orbits if o["cert_index"] == idx)
        W_basis = orb["basis"]
        W = rref_basis(W_basis, 9)
        d = len(W)
        k = 9 - d  # quotient dimension = 7
        L = orb["raw_lb"]  # Should be 18
        free = free_bits_from_rref(W, 9)

        # Enumerate all 1-dim quotient subspaces (lines): q in {1, ..., 2^k - 1}
        line_caps = {}
        all_cap_1 = True
        max_cap = 0
        for q in range(1, 1 << k):
            # Lift q into ambient space
            v = lift_q(q, free)
            # Build dim-3 superspace U = W + <v>
            U = rref_basis((*W, v), 9)
            key = pack_basis(U)
            lb_U = lut.get(key)
            if lb_U is None:
                cap = None
                all_cap_1 = False
            else:
                cap = L - lb_U
                if cap != 1:
                    all_cap_1 = False
                if cap > max_cap:
                    max_cap = cap
            line_caps[q] = {"lb_U": lb_U, "cap": cap}

        cap_hist = Counter()
        for lc in line_caps.values():
            if lc["cap"] is not None:
                cap_hist[lc["cap"]] += 1

        rec = {
            "cert_index": idx,
            "W_basis": list(W_basis),
            "W_rref": list(W),
            "dim": d,
            "quotient_dim": k,
            "target_L": L,
            "n_quotient_directions": (1 << k) - 1,
            "all_line_caps_equal_1": all_cap_1,
            "max_line_cap": max_cap,
            "cap_histogram": dict(sorted((int(a), int(b)) for a, b in cap_hist.items())),
            "dfs_distinct_valid": all_cap_1,
        }
        results.append(rec)
        print(f"idx={idx} dim={d} k={k} L={L} all_cap_1={all_cap_1} max_cap={max_cap} hist={dict(cap_hist)}")

    summary = {
        "schema": "dim2_line_caps_v1",
        "target_indices": target_indices,
        "all_nodes_caps_eq_1": all(r["all_line_caps_equal_1"] for r in results),
        "records": results,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"schema": summary["schema"],
                       "all_cap_1": summary["all_nodes_caps_eq_1"],
                       "out": str(OUT)}, indent=2))


if __name__ == "__main__":
    main()
