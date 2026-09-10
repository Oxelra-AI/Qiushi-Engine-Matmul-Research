#!/usr/bin/env python3
"""analysis: orbit-level profile of Wang rows hit by analysis rep2 models.

The analysis rank-aware CP-SAT run was adaptive: rows violated by one model are
inserted before the next model is solved.  Raw row-set disjointness therefore
carries little meaning.  This script asks a branch-invariant question instead:
which Wang-row orbits under the setwise stabilizer of the normalized adjacent
pair {1,2} appear in the violation sets of several different mixed supports?

The output is a research guide for row-family promotion or mathematical
compression; it is not a support exclusion or tensor-rank result.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

from wang_capacity_lazy import (
    make_actions,
    subspace_points_from_basis,
    transform_key,
    transform_mask,
    unpack_basis,
)


def load_models(path: Path):
    obj = json.loads(path.read_text())
    prefix = tuple(obj["prefix"])
    models = []
    for rec in obj["round_log"]:
        if rec.get("status") in {"OPTIMAL", "FEASIBLE"} and "selected_points" in rec:
            models.append({
                "round": int(rec["round"]),
                "support": tuple(sorted(set(prefix) | set(rec["selected_points"]))),
                "rank1_total": int(rec.get("rank1_count", 0)) + len(prefix),
                "higher_rank_total": int(rec.get("higher_rank_count", 0)),
                "reported_new_violations": int(rec.get("new_violations", -1)),
            })
    return obj, prefix, models


def occ(points, support: set[int]) -> int:
    return sum(1 for p in points if p in support)


def orbit_size(rows, stab) -> int:
    return len({transform_key(rows, img) for img in stab})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rankaware-result", default="data/rep2_rankaware/result.json")
    ap.add_argument("--lut", default="data/wang_f2_lb20/wang_subspace_lut.pkl")
    ap.add_argument("--out", default="data/corrected_strategy/rep2_common_violation_orbits.json")
    ap.add_argument("--top", type=int, default=80)
    args = ap.parse_args()

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    source_obj, prefix, models = load_models(Path(args.rankaware_result))
    supports = [set(m["support"]) for m in models]
    prefix_set = set(prefix)
    print(f"models={len(models)} prefix={prefix}")

    with open(args.lut, "rb") as f:
        payload = pickle.load(f)
    lut = {int(k): int(v) for k, v in payload["lut"].items()}
    print(f"lut={len(lut):,}")

    print("building prefix setwise stabilizer...")
    t_stab = time.time()
    actions = make_actions()
    stab = [img for img in actions if {transform_mask(p, img) for p in prefix} == prefix_set]
    print(f"stab={len(stab)} sec={time.time()-t_stab:.1f}")

    canon_cache: dict[int, int] = {}
    orbit_rows: dict[int, set[int]] = defaultdict(set)
    orbit_model_counts: dict[int, list[int]] = defaultdict(lambda: [0] * len(models))
    orbit_model_max_excess: dict[int, list[int]] = defaultdict(lambda: [0] * len(models))
    orbit_meta: dict[int, dict] = {}
    raw_model_sets = [set() for _ in models]
    type_all = Counter()
    type_by_model = [Counter() for _ in models]

    def canonize(key: int, rows) -> int:
        got = canon_cache.get(key)
        if got is not None:
            return got
        c = min(transform_key(rows, img) for img in stab)
        canon_cache[key] = c
        return c

    print("scanning LUT and canonicalizing violated rows...")
    t0 = time.time()
    for n, (key, lb) in enumerate(lut.items(), start=1):
        rows = unpack_basis(key)
        points = subspace_points_from_basis(rows)
        cap = 20 - int(lb)
        prefix_occ = occ(points, prefix_set)
        residual = cap - prefix_occ
        dim = len(rows)
        per_model = []
        any_bad = False
        for i, support in enumerate(supports):
            o = occ(points, support)
            excess = o - cap
            if excess > 0:
                any_bad = True
                per_model.append((i, excess))
                raw_model_sets[i].add(int(key))
                typ = (dim, int(lb), cap, prefix_occ, residual, excess)
                type_all[typ] += 1
                type_by_model[i][typ] += 1
        if any_bad:
            c = canonize(int(key), rows)
            orbit_rows[c].add(int(key))
            if c not in orbit_meta:
                orbit_meta[c] = {
                    "canonical_key_hex": hex(c),
                    "representative_basis": list(unpack_basis(c)),
                    "dim": dim,
                    "lb": int(lb),
                    "cap_for_s20": cap,
                    "prefix_occ": prefix_occ,
                    "residual_after_prefix": residual,
                }
            for i, excess in per_model:
                orbit_model_counts[c][i] += 1
                orbit_model_max_excess[c][i] = max(orbit_model_max_excess[c][i], excess)
        if n % 2_000_000 == 0:
            print(f"  {n:,}/{len(lut):,} rows; violated_orbits={len(orbit_rows)}; sec={time.time()-t0:.1f}")

    orbit_entries = []
    for c, rows in orbit_rows.items():
        counts = orbit_model_counts[c]
        maxex = orbit_model_max_excess[c]
        hit_models = [models[i]["round"] for i, cnt in enumerate(counts) if cnt]
        meta = dict(orbit_meta[c])
        # Only compute exact stabilizer-orbit size for orbits that recur enough
        hit_count = sum(1 for cnt in counts if cnt)
        size_val = None
        if hit_count >= 3:
            size_val = orbit_size(unpack_basis(c), stab)
        meta.update({
            "hit_model_count": hit_count,
            "hit_rounds": hit_models,
            "row_count_seen": len(rows),
            "orbit_size_under_prefix_stabilizer": size_val,
            "per_model_row_counts": counts,
            "per_model_max_excess": maxex,
        })
        orbit_entries.append(meta)

    orbit_entries.sort(key=lambda e: (-e["hit_model_count"], -sum(e["per_model_row_counts"]), e["dim"], -e["lb"], e["canonical_key_hex"]))

    hit_hist = Counter(e["hit_model_count"] for e in orbit_entries)
    common_all = [e for e in orbit_entries if e["hit_model_count"] == len(models)]
    common_4 = [e for e in orbit_entries if e["hit_model_count"] >= 4]

    pairwise = []
    orbit_sets_by_model = []
    for i in range(len(models)):
        s = {c for c, counts in orbit_model_counts.items() if counts[i]}
        orbit_sets_by_model.append(s)
    for i in range(len(models)):
        for j in range(i + 1, len(models)):
            raw_i, raw_j = raw_model_sets[i], raw_model_sets[j]
            orb_i, orb_j = orbit_sets_by_model[i], orbit_sets_by_model[j]
            pairwise.append({
                "rounds": [models[i]["round"], models[j]["round"]],
                "raw_intersection": len(raw_i & raw_j),
                "raw_union": len(raw_i | raw_j),
                "orbit_intersection": len(orb_i & orb_j),
                "orbit_union": len(orb_i | orb_j),
                "orbit_jaccard": len(orb_i & orb_j) / len(orb_i | orb_j) if (orb_i | orb_j) else None,
            })

    def type_obj(typ, cnt):
        dim, lb, cap, po, residual, excess = typ
        return {
            "count": cnt,
            "dim": dim,
            "lb": lb,
            "cap_for_s20": cap,
            "prefix_occ": po,
            "residual_after_prefix": residual,
            "excess": excess,
        }

    result = {
        "schema": "rep2_common_violation_orbits_v1",
        "source_result": args.rankaware_result,
        "interpretation": "raw disjointness is expected after adaptive insertion; recurring row orbits under the prefix stabilizer are the meaningful reusable signal here",
        "final_status": source_obj.get("final_status"),
        "prefix": list(prefix),
        "model_summaries": models,
        "lut_rows": len(lut),
        "setwise_stabilizer_order": len(stab),
        "unique_raw_violated_rows": len(set().union(*raw_model_sets)) if raw_model_sets else 0,
        "unique_violated_orbits": len(orbit_entries),
        "orbit_hit_count_histogram": dict(sorted(hit_hist.items())),
        "orbits_hit_by_all_models": len(common_all),
        "orbits_hit_by_at_least_4_models": len(common_4),
        "pairwise_overlap": pairwise,
        "top_row_types_all_models": [type_obj(t, c) for t, c in type_all.most_common(25)],
        "top_orbits": orbit_entries[: args.top],
        "common_all_model_orbits": common_all,
        "elapsed_sec": round(time.time() - t0, 2),
    }

    out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out_path),
        "unique_raw": result["unique_raw_violated_rows"],
        "unique_orbits": result["unique_violated_orbits"],
        "hit_hist": result["orbit_hit_count_histogram"],
        "all_model_orbits": result["orbits_hit_by_all_models"],
        "at_least_4": result["orbits_hit_by_at_least_4_models"],
        "elapsed_sec": result["elapsed_sec"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
