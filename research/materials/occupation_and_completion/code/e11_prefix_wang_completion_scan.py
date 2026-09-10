#!/usr/bin/env python3
"""Scan complete Wang-occupation completions of a fixed E11 A-prefix.

For a prefix P and target rank 19, enumerate all multisets of h=19-|P|
remaining nonzero A masks (for small h) and test the complete 417,199-row E11
Wang occupation system using the dense membership matrix.  This is only an
A-side necessary condition, but it exactly tells whether a prefix subtree is
already impossible before any Brent B/C solving.
"""
from __future__ import annotations

import argparse
import json
import pickle
import time
from itertools import combinations_with_replacement
from pathlib import Path

import numpy as np


def stats_for_occ(occ: np.ndarray, caps: np.ndarray, dims: np.ndarray, Ls: np.ndarray) -> dict:
    excess = occ - caps
    bad = np.flatnonzero(excess > 0)
    out = {"violation_count": int(len(bad)), "max_excess": int(excess[bad].max()) if len(bad) else 0}
    if len(bad):
        by_dim = {}
        by_L = {}
        for i in bad:
            by_dim[str(int(dims[i]))] = by_dim.get(str(int(dims[i])), 0) + 1
            by_L[str(int(Ls[i]))] = by_L.get(str(int(Ls[i])), 0) + 1
        out["violations_by_dim8"] = by_dim
        out["violations_by_L"] = by_L
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cache", type=Path, default=Path("data/e11_capacity_sat/e11_capacity_cache.pkl"))
    ap.add_argument("--membership", type=Path, default=Path("data/e11_occupation_sat/e11_membership.npy"))
    ap.add_argument("--prefix", required=True)
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--max-survivors", type=int, default=2000)
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
    if len(prefix) > args.rank:
        raise ValueError("prefix longer than rank")
    h = args.rank - len(prefix)
    occ0 = np.zeros(len(caps), dtype=np.int16)
    for p in prefix:
        occ0 += M[p].astype(np.int16)
    base_stats = stats_for_occ(occ0, caps, dims, Ls)
    survivors = []
    tested = 0
    best = None
    if h <= 0:
        combos = [tuple()]
    else:
        combos = combinations_with_replacement(range(1, 256), h)
    for combo in combos:
        tested += 1
        occ = occ0.copy()
        for p in combo:
            occ += M[p].astype(np.int16)
        st = stats_for_occ(occ, caps, dims, Ls)
        if best is None or (st["violation_count"], st["max_excess"]) < (best["stats"]["violation_count"], best["stats"]["max_excess"]):
            best = {"completion": list(combo), "stats": st}
        if st["violation_count"] == 0:
            survivors.append(list(combo))
            if len(survivors) >= args.max_survivors:
                break
    result = {
        "purpose": "exact complete-Wang completion scan for a fixed E11 A-prefix",
        "field": "F2",
        "rank": args.rank,
        "prefix": prefix,
        "prefix_size": len(prefix),
        "remaining_terms": h,
        "base_prefix_stats": base_stats,
        "tested_completions": tested,
        "survivor_count_recorded": len(survivors),
        "record_truncated": len(survivors) >= args.max_survivors,
        "survivor_completions_head": survivors[:args.max_survivors],
        "best_nonzero_or_first": best,
        "complete_wang_subtree_refuted": base_stats["violation_count"] > 0 or (h >= 0 and len(survivors) == 0 and not (len(survivors) >= args.max_survivors)),
        "meaning": "If complete_wang_subtree_refuted is true, no A-completion of this prefix satisfies the full E11 Wang occupation system. If survivors exist, only those full A-multisets need fixed-A Brent solving; Wang feasibility alone is not a CPD witness.",
        "elapsed_sec": time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: result[k] for k in ["prefix_size", "remaining_terms", "tested_completions", "survivor_count_recorded", "complete_wang_subtree_refuted", "elapsed_sec"]}, indent=2, sort_keys=True))
    if best:
        print("best", json.dumps(best, sort_keys=True)[:1000])
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
