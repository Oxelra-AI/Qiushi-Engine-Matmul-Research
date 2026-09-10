#!/usr/bin/env python3
r"""analysisf: vectorized lazy DFS with mixed-source support cuts.

Same mathematical test as lazy_mixed_cut_dfs.py, but future upper bounds
for coefficient-0/1/2 cuts are computed by suffix counts and numpy arrays.  This
is an engineering pilot to see whether direct mixed-source cuts can prune earlier
than the auxiliary eB/eC formulation.  Timeout-limited output is not a proof.
"""
from __future__ import annotations

import argparse
import collections
import json
import sys
import time
from pathlib import Path

import numpy as np

SCRIPTS = Path("scripts")
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import contraction_weight_excess_search as base  # noqa:E402

OUTDIR = Path("data/mixed_source_cuts")
S_RANK = 19
POINTS = base.POINTS


def load_wang(max_cap: int):
    records, _ = base.load_complete_records()
    rows = []
    for rec in records:
        L = int(rec["L"]); cap = S_RANK - L
        if cap <= 0 or cap >= S_RANK:
            continue
        if max_cap and cap > max_cap:
            continue
        rows.append((base.points_from_bitset(int(rec["point_bitset"])), cap, L, int(rec["dim8"]), int(rec["key8"])))
    rows.sort(key=lambda r: (r[1], len(r[0])))
    return rows


def load_cuts(path: Path, max_cuts: int, min_gap: int, min_K: int, require_non_dlocal: bool = False):
    with path.open() as f:
        payload = json.load(f)
    recs = []
    coeff_rows = []
    K = []
    for rec in payload["cuts"]:
        if int(rec["gap_K_minus_LD"]) < min_gap or int(rec["K"]) < min_K:
            continue
        # Optionally skip the common lam=nu top-gap family; those often reduce to D-local Wang combinations.
        if require_non_dlocal and int(rec.get("lam_B", -1)) == int(rec.get("nu_C", -2)):
            continue
        bs1 = int(rec["coeff1_bitset"]); bs2 = int(rec["coeff2_bitset"])
        coeff = np.zeros(256, dtype=np.int8)
        for p in POINTS:
            if (bs2 >> (p-1)) & 1:
                coeff[p] = 2
            elif (bs1 >> (p-1)) & 1:
                coeff[p] = 1
        coeff_rows.append(coeff)
        K.append(int(rec["K"]))
        recs.append({k: rec[k] for k in ("mu", "lam_B", "nu_C", "K", "L_D", "gap_K_minus_LD", "dual_dim", "rank_tuple", "coeff_counts_0_1_2") if k in rec})
        if max_cuts and len(recs) >= max_cuts:
            break
    if coeff_rows:
        C = np.vstack(coeff_rows).astype(np.int8)
        Karr = np.array(K, dtype=np.int16)
        # suffix counts from threshold p: available points are p..255 inclusive.
        is1 = (C == 1).astype(np.int16)
        is2 = (C == 2).astype(np.int16)
        suf1 = np.zeros((C.shape[0], 257), dtype=np.int16)
        suf2 = np.zeros((C.shape[0], 257), dtype=np.int16)
        suf1[:, 1:256] = np.flip(np.cumsum(np.flip(is1[:, 1:256], axis=1), axis=1), axis=1)
        suf2[:, 1:256] = np.flip(np.cumsum(np.flip(is2[:, 1:256], axis=1), axis=1), axis=1)
    else:
        C = np.zeros((0, 256), dtype=np.int8); Karr = np.zeros(0, dtype=np.int16)
        suf1 = np.zeros((0, 257), dtype=np.int16); suf2 = np.zeros((0, 257), dtype=np.int16)
    return recs, C, Karr, suf1, suf2


def dfs(time_limit: float, first_point: int, wang_cap: int, cuts_path: Path, max_cuts: int,
        min_gap: int, min_K: int, require_non_dlocal: bool, store_solutions: int = 20):
    t0 = time.time()
    wang_rows = load_wang(wang_cap)
    recs, C, K, suf1, suf2 = load_cuts(cuts_path, max_cuts, min_gap, min_K, require_non_dlocal)
    ncuts = int(K.shape[0])
    build_sec = round(time.time() - t0, 3)

    point_wang = {p: [] for p in POINTS}
    for i, (pts, cap, _L, _d, _k) in enumerate(wang_rows):
        for p in pts:
            point_wang[p].append(i)

    occ = np.zeros(len(wang_rows), dtype=np.int16)
    lhs = np.zeros(ncuts, dtype=np.int16)
    selected = [0] * (S_RANK + 1)
    stats = collections.Counter()
    prune_depth = collections.Counter()
    cut_prune_head = []
    solutions = []
    timeout = False

    def mixed_ok(next_min_point: int, rem_after: int, depth: int, point: int) -> bool:
        nonlocal cut_prune_head
        if ncuts == 0:
            return True
        if next_min_point > 255:
            c2 = np.zeros(ncuts, dtype=np.int16); c1 = c2
        else:
            c2 = suf2[:, next_min_point]
            c1 = suf1[:, next_min_point]
        take2 = np.minimum(c2, rem_after)
        rem1 = rem_after - take2
        take1 = np.minimum(c1, rem1)
        ub = lhs + 2 * take2 + take1
        bad = np.nonzero(ub < K)[0]
        stats["mixed_cut_checks"] += ncuts
        if bad.size:
            cid = int(bad[0])
            stats["mixed_cut_prunes"] += 1
            prune_depth[("mixed", depth)] += 1
            if len(cut_prune_head) < 20:
                cut_prune_head.append({
                    "depth": int(depth), "point": int(point), "partial": list(selected[1:depth+1]),
                    "cut_index": cid, "lhs_current": int(lhs[cid]),
                    "future_ub": int(ub[cid]), "K": int(K[cid]), "cut": recs[cid],
                })
            return False
        return True

    def rec(depth: int, min_point: int):
        nonlocal timeout
        if time.time() - t0 > time_limit:
            timeout = True
            return
        stats["nodes"] += 1
        if depth > S_RANK:
            stats["leaves"] += 1
            if len(solutions) < store_solutions:
                solutions.append(list(selected[1:S_RANK+1]))
            return
        remaining = S_RANK - depth + 1
        if 255 - min_point + 1 < remaining:
            stats["not_enough_points_prunes"] += 1
            return
        for p in range(min_point, 256):
            if timeout:
                return
            if 255 - p < remaining - 1:
                break
            ok = True
            for rid in point_wang[p]:
                if occ[rid] + 1 > wang_rows[rid][1]:
                    ok = False; break
            if not ok:
                stats["wang_prunes"] += 1
                prune_depth[("wang", depth)] += 1
                continue
            selected[depth] = p
            for rid in point_wang[p]:
                occ[rid] += 1
            if ncuts:
                lhs[:] += C[:, p]
            ok = mixed_ok(p + 1, remaining - 1, depth, p)
            if ok:
                rec(depth + 1, p + 1)
            if ncuts:
                lhs[:] -= C[:, p]
            for rid in point_wang[p]:
                occ[rid] -= 1

    if first_point > 0:
        selected[1] = first_point
        for rid in point_wang[first_point]:
            occ[rid] += 1
        if ncuts:
            lhs[:] += C[:, first_point]
        rec(2, first_point + 1)
    else:
        rec(1, 1)

    return {
        "schema": "s0908_lazy_mixed_cut_dfs_fast_v1",
        "meaning": "Timeout-limited vectorized DFS pilot using Wang cap rows plus selected direct mixed-source cuts. Not a global proof when timeout=true or when only a subset of rows/cuts is loaded.",
        "params": {"time_limit": time_limit, "first_point": first_point, "wang_cap": wang_cap, "cuts_path": str(cuts_path), "max_cuts": max_cuts, "min_gap": min_gap, "min_K": min_K, "require_non_dlocal_heuristic": require_non_dlocal},
        "build_sec": build_sec,
        "wang_rows": len(wang_rows),
        "wang_cap_hist": {str(k): int(v) for k, v in sorted(collections.Counter(cap for _pts, cap, _L, _d, _k in wang_rows).items())},
        "mixed_cuts_loaded": ncuts,
        "mixed_cut_gap_hist": {str(k): int(v) for k, v in sorted(collections.Counter(int(r["gap_K_minus_LD"]) for r in recs).items())},
        "elapsed_sec": round(time.time() - t0, 3),
        "timeout": bool(timeout),
        "stats": {str(k): int(v) for k, v in sorted(stats.items(), key=lambda kv: str(kv[0]))},
        "prune_depth_head": {str(k): int(v) for k, v in list(sorted(prune_depth.items(), key=lambda kv: str(kv[0])))[:100]},
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
    ap.add_argument("--require-non-dlocal", action="store_true")
    ap.add_argument("--out", default=str(OUTDIR / "lazy_mixed_cut_dfs_fast.json"))
    args = ap.parse_args()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    result = dfs(args.time_limit, args.first_point, args.wang_cap, Path(args.cuts_path), args.max_cuts, args.min_gap, args.min_K, args.require_non_dlocal)
    with Path(args.out).open("w") as f:
        json.dump(result, f, indent=2, sort_keys=True)
    compact = dict(result); compact.pop("solutions_head", None); compact.pop("cut_prune_head", None)
    print(json.dumps(compact, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
