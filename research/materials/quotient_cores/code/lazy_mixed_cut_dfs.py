#!/usr/bin/env python3
r"""analysise: lazy DFS using mixed-source support cuts as partial-support pruning.

This is a pilot, not a proof-producing exhaustive engine unless timeout=false and
coverage metadata is interpreted carefully.  It tests whether the small-coefficient
mixed-source inequalities help at the partial-support level where the previous
unconditional eB/eC budget check did not fire.
"""
from __future__ import annotations

import argparse
import collections
import json
import pickle
import sys
import time
from pathlib import Path
from typing import List, Sequence, Tuple

import numpy as np

SCRIPTS = Path("scripts")
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import contraction_weight_excess_search as base  # noqa:E402
import mixed_source_cuts as cutsmod  # noqa:E402

OUTDIR = Path("data/mixed_source_cuts")
S_RANK = 19
POINTS = base.POINTS


def point_list_from_bs(bs: int) -> List[int]:
    return base.points_from_bitset(int(bs))


def load_wang(max_cap: int = 2):
    records, _ = base.load_complete_records()
    rows = []
    for rec in records:
        L = int(rec["L"]); cap = S_RANK - L
        if cap <= 0 or cap >= S_RANK:
            continue
        if max_cap and cap > max_cap:
            continue
        pts = point_list_from_bs(int(rec["point_bitset"]))
        rows.append((pts, cap, int(rec["L"]), int(rec["dim8"]), int(rec["key8"])))
    rows.sort(key=lambda r: (r[1], len(r[0])))
    return rows


def load_mixed_cuts(path: Path, max_cuts: int = 5000, min_gap: int = 3, min_K: int = 12):
    with path.open() as f:
        payload = json.load(f)
    arr = []
    for rec in payload["cuts"]:
        if int(rec["gap_K_minus_LD"]) < min_gap or int(rec["K"]) < min_K:
            continue
        bs1 = int(rec["coeff1_bitset"]); bs2 = int(rec["coeff2_bitset"])
        coeff = np.zeros(256, dtype=np.int8)
        coeff_pts = []
        for p in POINTS:
            c = 2 if ((bs2 >> (p-1)) & 1) else (1 if ((bs1 >> (p-1)) & 1) else 0)
            coeff[p] = c
            if c:
                coeff_pts.append(p)
        arr.append({k: rec[k] for k in ("mu", "lam_B", "nu_C", "K", "L_D", "gap_K_minus_LD", "dual_dim", "rank_tuple", "coeff_counts_0_1_2") if k in rec} | {
            "coeff": coeff, "coeff_pts": coeff_pts,
            "max_coeff": 2,
        })
        if max_cuts and len(arr) >= max_cuts:
            break
    return arr


def dfs(time_limit: float = 60.0, first_point: int = 1, wang_cap: int = 2,
        cuts_path: Path = OUTDIR / "unique_nondominated_cuts_top50k.json",
        max_cuts: int = 5000, min_gap: int = 3, min_K: int = 12,
        store_solutions: int = 20) -> dict:
    t0 = time.time()
    wang_rows = load_wang(wang_cap)
    mcuts = load_mixed_cuts(cuts_path, max_cuts=max_cuts, min_gap=min_gap, min_K=min_K)
    build_sec = round(time.time() - t0, 3)

    point_wang = {p: [] for p in POINTS}
    for i, (pts, cap, _L, _dim, _key) in enumerate(wang_rows):
        for p in pts:
            point_wang[p].append(i)
    point_cuts = {p: [] for p in POINTS}
    for i, rec in enumerate(mcuts):
        for p in rec["coeff_pts"]:
            point_cuts[p].append(i)

    occ = [0] * len(wang_rows)
    lhs = [0] * len(mcuts)
    selected = [0] * (S_RANK + 1)
    solutions = []
    stats = collections.Counter()
    prune_depth = collections.Counter()
    cut_prune_head = []
    timeout = False

    def future_max_cut(cut_idx: int, min_point: int, remaining_to_pick: int) -> int:
        coeff = mcuts[cut_idx]["coeff"]
        vals = []
        for p in range(min_point, 256):
            vals.append(int(coeff[p]))
        vals.sort(reverse=True)
        return sum(vals[:remaining_to_pick])

    def dfs_rec(depth: int, min_point: int):
        nonlocal timeout
        if time.time() - t0 > time_limit:
            timeout = True
            return
        stats["nodes"] += 1
        if depth > S_RANK:
            stats["leaves"] += 1
            sol = list(selected[1:S_RANK+1])
            if len(solutions) < store_solutions:
                solutions.append(sol)
            return
        remaining_to_pick = S_RANK - depth + 1
        if 255 - min_point + 1 < remaining_to_pick:
            stats["not_enough_points_prunes"] += 1
            return
        for p in range(min_point, 256):
            if timeout:
                return
            if 255 - p < remaining_to_pick - 1:
                break
            # Wang row upper-bound pruning.
            ok = True
            for rid in point_wang[p]:
                if occ[rid] + 1 > wang_rows[rid][1]:
                    ok = False
                    break
            if not ok:
                stats["wang_prunes"] += 1
                prune_depth[("wang", depth)] += 1
                continue
            # Select p.
            selected[depth] = p
            for rid in point_wang[p]:
                occ[rid] += 1
            affected_cuts = point_cuts[p]
            for cid in affected_cuts:
                lhs[cid] += int(mcuts[cid]["coeff"][p])
            # Mixed cut future upper-bound pruning.
            rem_after = remaining_to_pick - 1
            ok = True
            checked = 0
            for cid, rec in enumerate(mcuts):
                # Fast necessary: if current lhs plus all future best coefficients below K.
                # Exact top coefficients among remaining points keep correlation within each cut.
                ub = lhs[cid] + future_max_cut(cid, p + 1, rem_after)
                checked += 1
                if ub < int(rec["K"]):
                    ok = False
                    stats["mixed_cut_prunes"] += 1
                    prune_depth[("mixed", depth)] += 1
                    if len(cut_prune_head) < 20:
                        cut_prune_head.append({
                            "depth": depth, "point": p, "partial": list(selected[1:depth+1]),
                            "cut_index": cid, "lhs_current": int(lhs[cid]), "future_max": int(ub - lhs[cid]),
                            "ub": int(ub), "K": int(rec["K"]),
                            "cut": {k: v for k, v in rec.items() if k not in ("coeff", "coeff_pts")},
                        })
                    break
            stats["mixed_cut_checks"] += checked
            if ok:
                dfs_rec(depth + 1, p + 1)
            # Undo.
            for cid in affected_cuts:
                lhs[cid] -= int(mcuts[cid]["coeff"][p])
            for rid in point_wang[p]:
                occ[rid] -= 1

    if first_point > 0:
        selected[1] = first_point
        for rid in point_wang[first_point]:
            occ[rid] += 1
        for cid in point_cuts[first_point]:
            lhs[cid] += int(mcuts[cid]["coeff"][first_point])
        dfs_rec(2, first_point + 1)
    else:
        dfs_rec(1, 1)

    return {
        "schema": "s0908_lazy_mixed_cut_dfs_v1",
        "meaning": "Timeout-limited DFS pilot. timeout=false with no leaves would be a support-level exclusion for the loaded rows/cuts and branch settings only; timeout=true is not evidence of completeness.",
        "params": {"time_limit": time_limit, "first_point": first_point, "wang_cap": wang_cap, "cuts_path": str(cuts_path), "max_cuts": max_cuts, "min_gap": min_gap, "min_K": min_K},
        "build_sec": build_sec,
        "wang_rows": len(wang_rows),
        "wang_cap_hist": {str(k): int(v) for k, v in sorted(collections.Counter(cap for _pts, cap, _L, _d, _k in wang_rows).items())},
        "mixed_cuts_loaded": len(mcuts),
        "mixed_cut_gap_hist": {str(k): int(v) for k, v in sorted(collections.Counter(int(c["gap_K_minus_LD"]) for c in mcuts).items())},
        "elapsed_sec": round(time.time() - t0, 3),
        "timeout": bool(timeout),
        "stats": {str(k): int(v) for k, v in sorted(stats.items(), key=lambda kv: str(kv[0]))},
        "prune_depth_head": {str(k): int(v) for k, v in list(sorted(prune_depth.items(), key=lambda kv: str(kv[0])))[:80]},
        "cut_prune_head": cut_prune_head,
        "solutions_found_or_stored": len(solutions),
        "solutions_head": solutions,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--time-limit", type=float, default=60)
    ap.add_argument("--first-point", type=int, default=1)
    ap.add_argument("--wang-cap", type=int, default=2)
    ap.add_argument("--cuts-path", default=str(OUTDIR / "unique_nondominated_cuts_top50k.json"))
    ap.add_argument("--max-cuts", type=int, default=5000)
    ap.add_argument("--min-gap", type=int, default=3)
    ap.add_argument("--min-K", type=int, default=12)
    ap.add_argument("--out", default=str(OUTDIR / "lazy_mixed_cut_dfs.json"))
    args = ap.parse_args()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    result = dfs(time_limit=args.time_limit, first_point=args.first_point, wang_cap=args.wang_cap,
                 cuts_path=Path(args.cuts_path), max_cuts=args.max_cuts, min_gap=args.min_gap, min_K=args.min_K)
    outpath = Path(args.out)
    with outpath.open("w") as f:
        json.dump(result, f, indent=2, sort_keys=True)
    compact = dict(result); compact.pop("solutions_head", None); compact.pop("cut_prune_head", None)
    print(json.dumps(compact, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
