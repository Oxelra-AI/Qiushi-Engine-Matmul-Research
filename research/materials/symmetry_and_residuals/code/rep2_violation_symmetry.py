#!/usr/bin/env python3
"""analysis: corrected analysis of rep2 rank-aware CP-SAT violation rows.

This script is not a proof engine.  It reads the analysis rank-aware CP-SAT
models for the adjacent-pair branch, reconstructs their complete Wang-row
violations, and groups the violated rows under the setwise stabilizer of the
fixed prefix {1,2}.  The purpose is to replace the earlier over-reading of raw
zero overlap: in an adaptive separation run, later models already satisfy rows
inserted from earlier models, so raw disjointness is expected.  What remains
useful is the row-type and branch-symmetry profile of the supports.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, Sequence

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

from wang_capacity_lazy import (
    make_actions,
    rref_key,
    subspace_points_from_basis,
    transform_key,
    transform_mask,
    unpack_basis,
)


def parse_models(path: Path):
    obj = json.loads(path.read_text())
    prefix = list(obj["prefix"])
    models = []
    for rec in obj["round_log"]:
        if rec.get("status") in {"OPTIMAL", "FEASIBLE"} and "selected_points" in rec:
            support = tuple(sorted(set(prefix) | set(rec["selected_points"])))
            models.append(
                {
                    "round": rec["round"],
                    "support": support,
                    "rank1_count_candidates": rec.get("rank1_count"),
                    "higher_rank_count_candidates": rec.get("higher_rank_count"),
                    "reported_new_violations": rec.get("new_violations"),
                }
            )
    return obj, prefix, models


def support_count(points: Iterable[int], support: set[int]) -> int:
    return sum(1 for p in points if p in support)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--rankaware-result",
        default="data/rep2_rankaware/result.json",
    )
    ap.add_argument(
        "--lut",
        default="data/wang_f2_lb20/wang_subspace_lut.pkl",
    )
    ap.add_argument(
        "--out",
        default="data/corrected_strategy/rep2_rankaware_violation_symmetry.json",
    )
    args = ap.parse_args()

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    analysis, prefix, models = parse_models(Path(args.rankaware_result))
    prefix_set = set(prefix)
    support_sets = [set(m["support"]) for m in models]
    print(f"Models: {len(models)}; prefix={prefix}; support sizes={[len(s) for s in support_sets]}")

    print("Loading LUT...")
    t0 = time.time()
    with open(args.lut, "rb") as f:
        payload = pickle.load(f)
    lut = {int(k): int(v) for k, v in payload["lut"].items()}
    print(f"  rows={len(lut):,}; load_sec={time.time()-t0:.1f}")

    by_model_keys: list[set[int]] = [set() for _ in models]
    by_model_excess: list[Counter] = [Counter() for _ in models]
    by_model_type: list[Counter] = [Counter() for _ in models]

    print("Scanning LUT once for all supports...")
    t1 = time.time()
    for n, (key, lb) in enumerate(lut.items(), start=1):
        basis = unpack_basis(key)
        pts = subspace_points_from_basis(basis)
        cap = 20 - int(lb)
        dim = len(basis)
        prefix_occ = support_count(pts, prefix_set)
        residual = cap - prefix_occ
        typ_base = (dim, int(lb), cap, prefix_occ, residual)
        for i, support in enumerate(support_sets):
            occ = support_count(pts, support)
            if occ > cap:
                by_model_keys[i].add(int(key))
                excess = occ - cap
                by_model_excess[i][excess] += 1
                by_model_type[i][typ_base + (excess,)] += 1
        if n % 2_000_000 == 0:
            print(f"  processed {n:,}/{len(lut):,} in {time.time()-t1:.1f}s")

    print("Building setwise stabilizer of prefix...")
    t2 = time.time()
    actions = make_actions()
    stab = [img for img in actions if {transform_mask(p, img) for p in prefix} == prefix_set]
    print(f"  actions={len(actions)} stab={len(stab)} sec={time.time()-t2:.1f}")

    all_violated = sorted(set().union(*by_model_keys)) if by_model_keys else []
    canon_cache: dict[int, int] = {}
    print(f"Canonicalizing {len(all_violated)} unique violated rows...")
    t3 = time.time()
    for idx, key in enumerate(all_violated, start=1):
        rows = unpack_basis(key)
        canon_cache[key] = min(transform_key(rows, img) for img in stab)
        if idx % 1000 == 0:
            print(f"  canon {idx}/{len(all_violated)} in {time.time()-t3:.1f}s")

    by_model_orbits = [{canon_cache[k] for k in keys} for keys in by_model_keys]

    pairwise = []
    for i in range(len(models)):
        for j in range(i + 1, len(models)):
            raw_i, raw_j = by_model_keys[i], by_model_keys[j]
            orb_i, orb_j = by_model_orbits[i], by_model_orbits[j]
            raw_inter = len(raw_i & raw_j)
            raw_union = len(raw_i | raw_j)
            orb_inter = len(orb_i & orb_j)
            orb_union = len(orb_i | orb_j)
            pairwise.append(
                {
                    "rounds": [models[i]["round"], models[j]["round"]],
                    "raw_intersection": raw_inter,
                    "raw_union": raw_union,
                    "raw_jaccard": raw_inter / raw_union if raw_union else None,
                    "orbit_intersection": orb_inter,
                    "orbit_union": orb_union,
                    "orbit_jaccard": orb_inter / orb_union if orb_union else None,
                }
            )

    common_raw = set.intersection(*by_model_keys) if by_model_keys else set()
    common_orbits = set.intersection(*by_model_orbits) if by_model_orbits else set()

    model_summaries = []
    for m, keys, orbs, excess_ctr, type_ctr in zip(
        models, by_model_keys, by_model_orbits, by_model_excess, by_model_type
    ):
        top_types = []
        for typ, cnt in type_ctr.most_common(15):
            dim, lb, cap, prefix_occ, residual, excess = typ
            top_types.append(
                {
                    "count": cnt,
                    "dim": dim,
                    "lb": lb,
                    "cap": cap,
                    "prefix_occ": prefix_occ,
                    "residual_after_prefix": residual,
                    "excess": excess,
                }
            )
        model_summaries.append(
            {
                "round": m["round"],
                "support": list(m["support"]),
                "rank1_total_including_prefix": (m.get("rank1_count_candidates") or 0) + len(prefix),
                "higher_rank_total": m.get("higher_rank_count_candidates"),
                "reported_new_violations": m.get("reported_new_violations"),
                "recomputed_violations": len(keys),
                "violation_orbits_under_prefix_stabilizer": len(orbs),
                "excess_histogram": dict(sorted(excess_ctr.items())),
                "top_row_types": top_types,
            }
        )

    result = {
        "schema": "rep2_rankaware_violation_symmetry_v1",
        "purpose": "corrected interpretation of adaptive CP-SAT separation models; not a feasibility proof",
        "source_result": args.rankaware_result,
        "prefix": prefix,
        "final_status": analysis.get("final_status"),
        "adaptive_separation_warning": (
            "Rows violated by an earlier model are inserted before later models are solved; "
            "therefore raw zero overlap of violation sets is expected and is not evidence of an inherent obstruction to convergence."
        ),
        "lut_rows_scanned": len(lut),
        "model_count": len(models),
        "setwise_stabilizer_order": len(stab),
        "unique_violated_rows_across_models": len(all_violated),
        "unique_violated_row_orbits_across_models": len(set(canon_cache.values())),
        "raw_rows_common_to_all_models": len(common_raw),
        "row_orbits_common_to_all_models": len(common_orbits),
        "pairwise_overlap": pairwise,
        "model_summaries": model_summaries,
        "elapsed_sec": round(time.time() - t0, 2),
    }

    out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out_path),
        "unique_rows": result["unique_violated_rows_across_models"],
        "unique_orbits": result["unique_violated_row_orbits_across_models"],
        "common_raw": result["raw_rows_common_to_all_models"],
        "common_orbits": result["row_orbits_common_to_all_models"],
        "elapsed_sec": result["elapsed_sec"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
