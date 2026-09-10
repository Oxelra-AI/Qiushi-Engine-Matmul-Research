#!/usr/bin/env python3
"""Heuristic local search for complete E11 Wang occupation-feasible rank-19 supports.

The complete occupation model is a necessary A-side condition for an E11 rank-19
CPD.  This script does not prove infeasibility; it tries to construct an actual
19-multiset passing all cached Wang constraints by minimizing total/excess
violations.  Any successful support is immediately useful for exact fixed-U SAT.
"""
from __future__ import annotations

import argparse
import json
import pickle
import random
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np

SCRIPTS_A02 = Path("scripts")
if str(SCRIPTS_A02) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_A02))
from e11_capacity_incremental_sat import build_or_load_constraint_cache, mask_to_points  # noqa: E402


def load_cache(path: Path):
    with path.open("rb") as f:
        return pickle.load(f)


def point_caps(cache: dict) -> dict[int, int]:
    out = {}
    for m, cap, d in zip(cache["masks"], cache["caps"], cache["dims"]):
        if d == 1 and int(m).bit_count() == 1:
            out[int(m).bit_length()] = int(cap)
    return out


def random_multiset(rng: random.Random, caps: dict[int, int], rank: int) -> dict[int, int]:
    sol = {}
    points = list(range(1, 256))
    while sum(sol.values()) < rank:
        p = rng.choice(points)
        if sol.get(p, 0) < caps[p]:
            sol[p] = sol.get(p, 0) + 1
    return dict(sorted(sol.items()))


def sol_masks(sol: dict[int, int]) -> tuple[int, dict[int, int]]:
    sm = 0; extra = {}
    for p, c in sol.items():
        sm |= 1 << (p - 1)
        if c > 1:
            extra[p] = c - 1
    return sm, extra


def occ_for(mask: int, sm: int, extra: dict[int, int]) -> int:
    o = (int(mask) & sm).bit_count()
    for p, e in extra.items():
        if (int(mask) >> (p - 1)) & 1:
            o += e
    return o


def score(sol: dict[int, int], cache: dict, weights_by_dim: dict[int, float] | None = None, max_report: int = 20) -> tuple[float, dict, list[dict]]:
    sm, extra = sol_masks(sol)
    total = 0.0
    vcnt = 0
    max_excess = 0
    by_dim = Counter()
    by_L = Counter()
    head = []
    for i, (m, cap) in enumerate(zip(cache["masks"], cache["caps"])):
        if not m:
            continue
        o = occ_for(m, sm, extra)
        if o > cap:
            exc = o - cap
            d = cache["dims"][i]
            L = cache["Ls"][i]
            w = (weights_by_dim or {}).get(d, 1.0)
            total += w * exc * exc
            vcnt += 1
            max_excess = max(max_excess, exc)
            by_dim[d] += 1
            by_L[L] += 1
            if len(head) < max_report:
                head.append({"index": i, "key8": cache["keys8"][i], "dim8": d, "L": L, "cap": cap, "occupancy": o, "excess": exc, "points_head": mask_to_points(m)[:32]})
    # prioritize eliminating high excess/count; scalar makes comparisons fast enough.
    obj = total + 10000.0 * max_excess + 0.01 * vcnt
    stats = {"objective": obj, "weighted_excess_sq": total, "violation_count": vcnt, "max_excess": max_excess, "violations_by_dim8": dict(by_dim), "violations_by_L": dict(by_L)}
    return obj, stats, head


def multiset_list(sol: dict[int, int]) -> list[int]:
    out=[]
    for p,c in sorted(sol.items()): out.extend([p]*c)
    return out


def neighbors(sol: dict[int, int], caps: dict[int, int], rng: random.Random, samples: int):
    ms = multiset_list(sol)
    pts = list(range(1, 256))
    yielded = set()
    for _ in range(samples):
        i = rng.randrange(len(ms))
        old = ms[i]
        new = rng.choice(pts)
        if new == old:
            continue
        d = dict(sol)
        d[old] -= 1
        if d[old] == 0:
            del d[old]
        if d.get(new, 0) >= caps[new]:
            continue
        d[new] = d.get(new, 0) + 1
        key = tuple(multiset_list(d))
        if key in yielded:
            continue
        yielded.add(key)
        yield dict(sorted(d.items()))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cache", type=Path, default=Path("data/e11_capacity_sat/e11_capacity_cache.pkl"))
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--trials", type=int, default=20)
    ap.add_argument("--steps", type=int, default=200)
    ap.add_argument("--neighbor-samples", type=int, default=80)
    ap.add_argument("--seed", type=int, default=2026090408)
    ap.add_argument("--out", type=Path, default=Path("data/e11_capacity_local_search/result.json"))
    args = ap.parse_args()
    t0 = time.time()
    if not args.cache.exists():
        build_or_load_constraint_cache(args.lut, args.cache, args.rank)
    cache = load_cache(args.cache)
    caps = point_caps(cache)
    rng = random.Random(args.seed)
    best_sol = None; best_obj = None; best_stats = None; best_head = None
    logs = []
    for tr in range(args.trials):
        cur = random_multiset(rng, caps, args.rank)
        cur_obj, cur_stats, cur_head = score(cur, cache)
        T = 5.0
        if best_obj is None or cur_obj < best_obj:
            best_sol, best_obj, best_stats, best_head = cur, cur_obj, cur_stats, cur_head
            print(f"trial {tr} init best obj={best_obj:.2f} stats={best_stats} ms={multiset_list(best_sol)}")
        for st in range(args.steps):
            best_n = None; best_n_obj = None; best_n_stats = None; best_n_head = None
            for nb in neighbors(cur, caps, rng, args.neighbor_samples):
                o, s, h = score(nb, cache)
                if best_n_obj is None or o < best_n_obj:
                    best_n, best_n_obj, best_n_stats, best_n_head = nb, o, s, h
            if best_n is None:
                continue
            accept = best_n_obj <= cur_obj or rng.random() < np.exp((cur_obj - best_n_obj) / max(T, 1e-9))
            if accept:
                cur, cur_obj, cur_stats, cur_head = best_n, best_n_obj, best_n_stats, best_n_head
            T *= 0.97
            if best_n_obj is not None and (best_obj is None or best_n_obj < best_obj):
                best_sol, best_obj, best_stats, best_head = best_n, best_n_obj, best_n_stats, best_n_head
                print(f"trial {tr} ARTIFACT {st}: best obj={best_obj:.2f} stats={best_stats} ms={multiset_list(best_sol)}")
                logs.append({"trial": tr, "ARTIFACT": st, "best_obj": best_obj, "best_stats": best_stats, "multiset": multiset_list(best_sol)})
                if best_stats["violation_count"] == 0:
                    break
        if best_stats and best_stats["violation_count"] == 0:
            break
    result = {"problem": "heuristic complete E11 Wang occupation support local search", "field":"F2", "rank_s":args.rank,
              "best_solution": None if best_sol is None else {str(k):v for k,v in best_sol.items()},
              "best_multiset": None if best_sol is None else multiset_list(best_sol),
              "best_stats": best_stats, "best_violations_head": best_head, "logs_tail": logs[-100:], "elapsed_sec": time.time()-t0,
              "meaning": "A zero-violation multiset is a complete Wang-occupation-feasible A-support for fixed-U SAT; nonzero violations are heuristic only."}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"best_stats":best_stats,"best_multiset":result["best_multiset"],"elapsed_sec":result["elapsed_sec"]}, indent=2, sort_keys=True))
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
