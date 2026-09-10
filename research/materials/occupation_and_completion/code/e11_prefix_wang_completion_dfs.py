#!/usr/bin/env python3
"""Exact DFS for small remaining E11 Wang completions of an A-prefix.

The dense membership matrix M[p,i] tells whether quotient point p lies in
subspace inequality i.  For prefix occupancy occ0, slack_i=cap_i-occ0_i.  A
remaining point p is allowable at a node exactly when it avoids every zero-slack
subspace at that node.  This gives a fast exact recursive search for h=rank-|P|
small (especially h<=3) without copying all 417k inequalities for every tuple.
"""
from __future__ import annotations

import argparse
import json
import pickle
import time
from pathlib import Path

import numpy as np


def stats_for_slack(slack: np.ndarray, caps: np.ndarray, dims: np.ndarray, Ls: np.ndarray) -> dict:
    # Negative slack corresponds to prefix violations.
    bad = np.flatnonzero(slack < 0)
    out = {"violation_count": int(len(bad)), "max_excess": int((-slack[bad]).max()) if len(bad) else 0}
    if len(bad):
        by_dim = {}; by_L = {}
        for i in bad:
            by_dim[str(int(dims[i]))] = by_dim.get(str(int(dims[i])), 0) + 1
            by_L[str(int(Ls[i]))] = by_L.get(str(int(Ls[i])), 0) + 1
        out["violations_by_dim8"] = by_dim
        out["violations_by_L"] = by_L
    return out


def completion_stats(prefix: list[int], comp: list[int], M: np.ndarray, caps: np.ndarray, dims: np.ndarray, Ls: np.ndarray) -> dict:
    occ = np.zeros(len(caps), dtype=np.int16)
    for p in prefix + comp:
        occ += M[p].astype(np.int16)
    excess = occ - caps
    bad = np.flatnonzero(excess > 0)
    out = {"violation_count": int(len(bad)), "max_excess": int(excess[bad].max()) if len(bad) else 0}
    if len(bad):
        by_dim={}; by_L={}
        for i in bad:
            by_dim[str(int(dims[i]))] = by_dim.get(str(int(dims[i])),0)+1
            by_L[str(int(Ls[i]))] = by_L.get(str(int(Ls[i])),0)+1
        out["violations_by_dim8"] = by_dim; out["violations_by_L"] = by_L
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cache", type=Path, default=Path("data/e11_capacity_sat/e11_capacity_cache.pkl"))
    ap.add_argument("--membership", type=Path, default=Path("data/e11_occupation_sat/e11_membership.npy"))
    ap.add_argument("--prefix", required=True)
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--max-survivors", type=int, default=1000)
    ap.add_argument("--node-limit", type=int, default=0, help="0 means no limit")
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    t0 = time.time()
    with args.cache.open("rb") as f:
        cache = pickle.load(f)
    M = np.load(args.membership, mmap_mode="r")
    caps = np.asarray(cache["caps"], dtype=np.int16)
    dims = np.asarray(cache["dims"], dtype=np.int16)
    Ls = np.asarray(cache["Ls"], dtype=np.int16)
    prefix = [int(x) for x in args.prefix.split(",") if x.strip()]
    h = args.rank - len(prefix)
    if h < 0:
        raise ValueError("prefix longer than rank")
    slack0 = caps.copy()
    for p in prefix:
        slack0 -= M[p].astype(np.int16)
    base_stats = stats_for_slack(slack0, caps, dims, Ls)
    survivors: list[list[int]] = []
    nodes_by_depth = {str(i): 0 for i in range(h + 1)}
    allowed_counts_head: list[dict] = []
    stopped = False
    best_partial_dead_end = None

    def update_best_partial(comp: list[int], reason: str) -> None:
        nonlocal best_partial_dead_end
        st = completion_stats(prefix, comp, M, caps, dims, Ls)
        rec = {"partial_completion": list(comp), "filled_remaining_terms": len(comp), "unfilled_remaining_terms": h - len(comp), "reason": reason, "stats_for_prefix_plus_partial_only": st}
        if best_partial_dead_end is None or (st["violation_count"], st["max_excess"], -len(comp)) < (best_partial_dead_end["stats_for_prefix_plus_partial_only"]["violation_count"], best_partial_dead_end["stats_for_prefix_plus_partial_only"]["max_excess"], -best_partial_dead_end["filled_remaining_terms"]):
            best_partial_dead_end = rec

    def dfs(slack: np.ndarray, start: int, left: int, comp: list[int]) -> None:
        nonlocal stopped
        if stopped:
            return
        depth = h - left
        nodes_by_depth[str(depth)] += 1
        if args.node_limit and sum(nodes_by_depth.values()) > args.node_limit:
            stopped = True
            return
        if np.any(slack < 0):
            update_best_partial(comp, "negative_slack")
            return
        if left == 0:
            survivors.append(list(comp))
            if len(survivors) >= args.max_survivors:
                stopped = True
            return
        zero = np.flatnonzero(slack <= 0)
        allowed = []
        if len(zero) == 0:
            allowed = list(range(start, 256))
        else:
            Z = M[:, zero]
            # p is allowed iff it is not in any zero-slack subspace.
            hit = np.asarray(Z.sum(axis=1)).reshape(-1) > 0
            allowed = [p for p in range(start, 256) if not bool(hit[p])]
        if len(allowed_counts_head) < 30:
            allowed_counts_head.append({"partial": list(comp), "left": left, "start": start, "zero_slack_constraints": int(len(zero)), "allowed_count": len(allowed), "allowed_head": allowed[:30]})
        if not allowed:
            update_best_partial(comp, "no_allowed_next_point")
            return
        for p in allowed:
            dfs(slack - M[p].astype(np.int16), p, left - 1, comp + [p])
            if stopped:
                return

    if base_stats["violation_count"] == 0:
        dfs(slack0, 1, h, [])
    result = {
        "purpose": "exact small-h DFS for complete E11 Wang occupation completion of a prefix",
        "field": "F2",
        "rank": args.rank,
        "prefix": prefix,
        "prefix_size": len(prefix),
        "remaining_terms": h,
        "base_prefix_stats": base_stats,
        "nodes_by_depth": nodes_by_depth,
        "allowed_counts_head": allowed_counts_head,
        "survivor_count_recorded": len(survivors),
        "record_truncated_or_node_limited": bool(stopped),
        "survivor_completions_head": survivors[:args.max_survivors],
        "best_partial_dead_end_recorded": best_partial_dead_end,
        "complete_wang_subtree_refuted": bool(base_stats["violation_count"] > 0 or (not stopped and len(survivors) == 0)),
        "meaning": "If complete_wang_subtree_refuted is true, the prefix has no completion satisfying all 417,199 E11 Wang occupation inequalities. If survivors exist, they are A-side candidates only and still need fixed-A Brent solving.",
        "elapsed_sec": time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: result[k] for k in ["prefix_size", "remaining_terms", "nodes_by_depth", "survivor_count_recorded", "record_truncated_or_node_limited", "complete_wang_subtree_refuted", "elapsed_sec"]}, indent=2, sort_keys=True))
    if best_partial_dead_end:
        print("best_partial_dead_end", json.dumps(best_partial_dead_end, sort_keys=True)[:1000])
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
