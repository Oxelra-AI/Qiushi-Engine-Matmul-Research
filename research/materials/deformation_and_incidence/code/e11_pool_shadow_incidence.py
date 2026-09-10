#!/usr/bin/env python3
"""Incidence and 3x3-shadow profiles for E11 rank-21 pools and equal-W deletions.

Purpose: test the corrected shadow filter on many known exact decompositions and
map the local rank-19 near-miss surface obtained by deleting two same-W terms from
rank-21 E11 core decompositions.  These computations do not prove any global rank
bound; they provide exact finite-field evidence for which support patterns survive
cheap B/C shadow necessary conditions.
"""
from __future__ import annotations

import argparse
import collections
import json
import sys
import time
from pathlib import Path
from typing import List, Tuple

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
import e11_shadow_filter as shadow  # noqa: E402


def row_to_terms(row) -> List[Tuple[int, int, int]]:
    r = len(row) // 3
    return [(int(row[3*t]), int(row[3*t+1]), int(row[3*t+2])) for t in range(r)]


def bitrow(row: List[int]) -> int:
    x = 0
    for i, b in enumerate(row):
        if int(b) & 1:
            x |= 1 << i
    return x


def rank_int(rows: List[int]) -> int:
    basis = {}
    r = 0
    for x0 in rows:
        x = int(x0)
        while x:
            p = x.bit_length() - 1
            if p in basis:
                x ^= basis[p]
            else:
                basis[p] = x
                r += 1
                break
    return r


def consistent_int(rows: List[int], rhs: List[int], nvars: int):
    rA = rank_int(rows)
    rB = rank_int([row | ((int(b)&1) << nvars) for row, b in zip(rows, rhs)])
    return rA == rB, rA, rB


def shadow_summary_for_support(us: List[int], inv_lams: List[int]) -> dict:
    nvars = 9 * len(us)
    tensor_rows, tensor_rhs = shadow.build_tensor_shadow_rows(us)
    tight = [lam for lam in inv_lams if sum(shadow.dot8(lam, u) for u in us) == 9]
    rows = [bitrow(r) for r in tensor_rows]
    rhs = list(tensor_rhs)
    for lam in tight:
        tr, tb = shadow.add_trace_rows(us, [lam], transpose_coeff=False)
        rows.extend(bitrow(r) for r in tr)
        rhs.extend(tb)
    ok, rA, rB = consistent_int(rows, rhs, nvars)
    return {"ok": ok, "rank": rA, "aug_rank": rB, "tight_count": len(tight), "tight": tight}


def gf2_rank_vecs(masks: List[int], n: int) -> int:
    rows = []
    for m in masks:
        x = 0
        for i in range(n):
            if (int(m) >> i) & 1:
                x |= 1 << i
        rows.append(x)
    return rank_int(rows)


def incidence_profile(us: List[int], point_to_orbit: dict[int, int] | None = None) -> dict:
    slice_weights = [sum((int(u) >> s) & 1 for u in us) for s in range(8)]
    counts = collections.Counter(us)
    prof = {
        "rank_terms": len(us),
        "total_a_weight": sum(int(u).bit_count() for u in us),
        "slice_weights": slice_weights,
        "min_slice_weight": min(slice_weights),
        "max_slice_weight": max(slice_weights),
        "distinct_u": len(counts),
        "max_u_multiplicity": max(counts.values()) if counts else 0,
        "u_span_rank": gf2_rank_vecs(us, 8),
    }
    if point_to_orbit is not None:
        nonzero = [u for u in us if u]
        if nonzero:
            orbits = [point_to_orbit[int(u)] for u in nonzero]
            prof["min_orbit"] = min(orbits)
            prof["orbit_hist"] = {str(k): v for k, v in sorted(collections.Counter(orbits).items())}
    return prof


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pool", type=Path, default=Path("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy"))
    ap.add_argument("--orbits", type=Path, default=Path("data/e11_orbits/e11_quotient_orbits.json"))
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--max-deletions", type=int, default=0, help="0 means all same-W deletion pairs")
    args = ap.parse_args()
    t0 = time.time()
    pool = np.load(args.pool)
    orbit_data = json.loads(args.orbits.read_text())
    point_to_orbit = {int(k): int(v) for k, v in orbit_data["point_orbits"]["point_to_orbit"].items()}
    inv_lams = shadow.invertible_lambda_masks()

    rank21_profiles = []
    shadow_failures = []
    rank21_hist = collections.Counter()
    tight_hist = collections.Counter()
    min_orbit_hist = collections.Counter()
    for idx, row in enumerate(pool):
        terms = row_to_terms(row)
        us = [u for u, v, w in terms]
        prof = incidence_profile(us, point_to_orbit)
        sh = shadow_summary_for_support(us, inv_lams)
        prof["shadow"] = {k: sh[k] for k in ["ok", "rank", "aug_rank", "tight_count"]}
        rank21_profiles.append(prof if idx < 12 else None)
        rank21_hist[(prof["total_a_weight"], prof["min_slice_weight"], prof["distinct_u"], prof["max_u_multiplicity"])] += 1
        tight_hist[sh["tight_count"]] += 1
        min_orbit_hist[prof.get("min_orbit", -1)] += 1
        if not sh["ok"]:
            shadow_failures.append({"row": idx, "u": us, "profile": prof, "shadow": sh})

    deletion_records_head = []
    deletion_hist = collections.Counter()
    deletion_shadow_hist = collections.Counter()
    deletion_count = 0
    deletion_inconsistent_examples = []
    seen_supports = set()
    for idx, row in enumerate(pool):
        terms = row_to_terms(row)
        groups = collections.defaultdict(list)
        for t, (u, v, w) in enumerate(terms):
            groups[w].append(t)
        for w, inds in groups.items():
            if len(inds) < 2:
                continue
            for a_i in range(len(inds)):
                for b_i in range(a_i + 1, len(inds)):
                    i = inds[a_i]; j = inds[b_i]
                    remaining = [terms[t][0] for t in range(len(terms)) if t not in (i, j)]
                    deletion_count += 1
                    key = tuple(sorted(remaining))
                    seen_supports.add(key)
                    prof = incidence_profile(remaining, point_to_orbit)
                    sh = shadow_summary_for_support(remaining, inv_lams)
                    deletion_hist[(prof["total_a_weight"], prof["min_slice_weight"], prof["distinct_u"], prof["max_u_multiplicity"], sh["tight_count"])] += 1
                    deletion_shadow_hist[(sh["ok"], sh["tight_count"], sh["rank"], sh["aug_rank"])] += 1
                    if len(deletion_records_head) < 20:
                        deletion_records_head.append({"pool_row": idx, "deleted_terms": [i, j], "deleted_w": int(w), "remaining_u": remaining, "profile": prof, "shadow": {k: sh[k] for k in ["ok", "rank", "aug_rank", "tight_count", "tight"]}})
                    if not sh["ok"] and len(deletion_inconsistent_examples) < 20:
                        deletion_inconsistent_examples.append({"pool_row": idx, "deleted_terms": [i, j], "deleted_w": int(w), "remaining_u": remaining, "profile": prof, "shadow": {k: sh[k] for k in ["ok", "rank", "aug_rank", "tight_count", "tight"]}})
                    if args.max_deletions and deletion_count >= args.max_deletions:
                        break
                if args.max_deletions and deletion_count >= args.max_deletions:
                    break
            if args.max_deletions and deletion_count >= args.max_deletions:
                break
        if args.max_deletions and deletion_count >= args.max_deletions:
            break

    result = {
        "purpose": "incidence and corrected shadow-filter profiles for exact rank-21 E11 core pool and same-W rank-19 deletion surfaces",
        "pool": str(args.pool),
        "pool_rows": int(len(pool)),
        "rank21_all_shadow_consistent": len(shadow_failures) == 0,
        "rank21_shadow_failures_head": shadow_failures[:5],
        "rank21_incidence_hist": {str(k): v for k, v in sorted(rank21_hist.items(), key=lambda kv: str(kv[0]))},
        "rank21_tight_count_hist": {str(k): v for k, v in sorted(tight_hist.items())},
        "rank21_min_orbit_hist": {str(k): v for k, v in sorted(min_orbit_hist.items())},
        "rank21_profile_head": [p for p in rank21_profiles if p is not None],
        "same_w_deletion_pairs_scanned": deletion_count,
        "unique_remaining_u_multisets": len(seen_supports),
        "deletion_incidence_shadow_hist": {str(k): v for k, v in sorted(deletion_hist.items(), key=lambda kv: str(kv[0]))},
        "deletion_shadow_rank_hist": {str(k): v for k, v in sorted(deletion_shadow_hist.items(), key=lambda kv: str(kv[0]))},
        "deletion_inconsistent_count": sum(v for k, v in deletion_shadow_hist.items() if k[0] is False),
        "deletion_inconsistent_examples_head": deletion_inconsistent_examples,
        "deletion_records_head": deletion_records_head,
        "meaning": "All rank-21 controls should pass the shadow system if the convention is correct. Same-W deletion rows are local rank-19 near-miss surfaces from known pools; shadow rejection is only necessary-condition evidence and not a global lower bound.",
        "elapsed_sec": time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "status": "ok",
        "out": str(args.out),
        "pool_rows": int(len(pool)),
        "rank21_all_shadow_consistent": len(shadow_failures) == 0,
        "rank21_tight_count_hist": result["rank21_tight_count_hist"],
        "same_w_deletion_pairs_scanned": deletion_count,
        "unique_remaining_u_multisets": len(seen_supports),
        "deletion_inconsistent_count": result["deletion_inconsistent_count"],
        "deletion_shadow_rank_hist_head": list(result["deletion_shadow_rank_hist"].items())[:10],
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
