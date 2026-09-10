#!/usr/bin/env python3
"""Complete E11 Wang scan for analysis tight-rank geometry samples.

Loads the local-swap rank-weight samples and checks them against all 417,199
E11 quotient Wang occupation rows.  This separates scalar rank-weight feasibility
from complete Wang admissibility.
"""
from __future__ import annotations

import json, pickle, sys, time
from collections import Counter
from pathlib import Path
from typing import Sequence

S0904 = Path("scripts")
if str(S0904) not in sys.path:
    sys.path.insert(0, str(S0904))

from core_capacity_all_mip import enumerate_subspace_keys  # type: ignore
from core_capacity_from_wang_lut import CoreQuotient  # type: ignore
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis  # type: ignore

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
IN_PATH = Path("data/tight_rank_geometry/rankweight_mutation_geometry.json")
OUT_PATH = Path("data/tight_rank_geometry/complete_wang_scan_tight_samples.json")


def load_lut():
    with LUT_PATH.open("rb") as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload["lut"].items()}, payload.get("meta", {})


def build_records(lut):
    t0 = time.time()
    core = CoreQuotient(1)
    records = []
    by_dim = Counter(); by_L = Counter(); by_cap = Counter()
    for key8 in enumerate_subspace_keys(8):
        key9 = core.key9_from_key8(key8)
        L = int(lut[key9])
        pts = subspace_points_from_basis(unpack_basis(key8))
        bitset = 0
        for p in pts:
            bitset |= 1 << (int(p) - 1)
        rec = {
            "key8": int(key8), "key9": int(key9), "dim8": int(key8 & 0xF),
            "dim9": int(key9 & 0xF), "L": L, "cap19": 19 - L,
            "point_count": len(pts), "point_bitset": bitset,
        }
        records.append(rec)
        by_dim[rec["dim8"]] += 1; by_L[L] += 1; by_cap[19 - L] += 1
    return records, {"constraint_count": len(records), "by_dim8": dict(sorted(by_dim.items())), "by_L": dict(sorted(by_L.items())), "by_cap19": dict(sorted(by_cap.items())), "elapsed_sec": time.time() - t0}


def scan(label: str, support: Sequence[int], records, max_head: int = 20):
    bits = 0
    for p in support:
        bits |= 1 << (int(p) - 1)
    viol = []
    by_dim = Counter(); by_L = Counter(); by_excess = Counter()
    for rec in records:
        occ = (bits & int(rec["point_bitset"])).bit_count()
        cap = int(rec["cap19"])
        if occ > cap:
            excess = occ - cap
            by_dim[rec["dim8"]] += 1; by_L[rec["L"]] += 1; by_excess[excess] += 1
            if len(viol) < max_head or excess > min(v["excess"] for v in viol):
                v = {k: rec[k] for k in ["key8", "key9", "dim8", "dim9", "L", "cap19", "point_count"]}
                v.update({"occupancy": occ, "excess": excess, "basis8": list(unpack_basis(rec["key8"])), "basis9": list(unpack_basis(rec["key9"]))})
                viol.append(v)
                viol.sort(key=lambda x: (x["excess"], x["L"], x["occupancy"], x["dim8"]), reverse=True)
                viol = viol[:max_head]
    return {
        "label": label,
        "support": list(map(int, support)),
        "violation_count": sum(by_excess.values()),
        "max_excess": max(by_excess.keys(), default=0),
        "violations_by_dim8": dict(sorted(by_dim.items())),
        "violations_by_L": dict(sorted(by_L.items())),
        "violations_by_excess": dict(sorted(by_excess.items())),
        "violations_head": viol,
    }


def main():
    t0 = time.time()
    lut, meta = load_lut()
    print(f"loaded LUT {len(lut):,} coverage={meta.get('coverage_ok')}")
    records, rmeta = build_records(lut)
    print("records", json.dumps({k: rmeta[k] for k in ["constraint_count", "elapsed_sec"]}, sort_keys=True))
    data = json.loads(IN_PATH.read_text())
    inputs = []
    for s in data["summaries"]:
        inputs.append((s["label"], s["support"], {k: s[k] for k in ["domain_hist", "zero_terms", "linear", "affine_dim", "trans_fail", "tight_count", "tight_by_matrix_rank"]}))
    results = []
    for label, support, geom in inputs:
        rec = scan(label, support, records)
        rec["tight_geometry_brief"] = geom
        results.append(rec)
        print("scan", json.dumps({"label": label, "viol": rec["violation_count"], "max_excess": rec["max_excess"], "by_L": rec["violations_by_L"], "geom": geom}, sort_keys=True)[:1600])
    results_sorted = sorted(results, key=lambda r: (r["violation_count"], r["max_excess"]))
    aggregate = {
        "support_count": len(results),
        "best_by_violation": [{"label": r["label"], "violation_count": r["violation_count"], "max_excess": r["max_excess"], "violations_by_L": r["violations_by_L"], "tight_geometry_brief": r["tight_geometry_brief"]} for r in results_sorted[:8]],
        "violation_count_hist": dict(sorted(Counter(r["violation_count"] for r in results).items())),
        "min_violation_count": results_sorted[0]["violation_count"] if results_sorted else None,
        "zero_violation_count": sum(1 for r in results if r["violation_count"] == 0),
    }
    payload = {"schema": "complete_wang_scan_tight_samples_v1", "field": "F2", "purpose": "Complete E11 Wang scan of analysis rank-weight/tight-domain samples.", "lut_meta_brief": {"coverage_ok": meta.get("coverage_ok"), "conflict_count": meta.get("conflict_count"), "subspace_count": meta.get("subspace_count")}, "core_table_meta": rmeta, "aggregate": aggregate, "results": results, "elapsed_sec": time.time() - t0}
    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(OUT_PATH), "aggregate": aggregate}, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
