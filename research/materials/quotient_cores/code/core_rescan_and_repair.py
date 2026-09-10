#!/usr/bin/env python3
r"""analysis: repair analysis E11-core conclusions using the complete core table.

This script deliberately uses the complete 417,199-row E11 quotient Wang table
from analysis.  It corrects two analysis hazards:

* counting full 9D Wang subspaces and relabeling dimension-1 is not the same as
  the E11 quotient table (only full subspaces containing E11 project to core
  rows);
* scanning only spans of selected support points can miss violations where a
  larger subspace has the same selected occupancy but a stronger inherited Wang
  lower bound.

The output records exact core L-distributions, complete scans of the current
near-miss supports, and for each base violation compares the violating row with
span(selected points inside the row).
"""
from __future__ import annotations

import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Sequence

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import build_core_constraints  # noqa: E402
from wang_capacity_lazy import (  # noqa: E402
    in_rowspace,
    pack_basis,
    rref_basis,
    subspace_points_from_basis,
    unpack_basis,
)

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/core_incidence"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"

SUPPORTS: Dict[str, List[int]] = {
    "54_base_9violation": [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219],
    "12violation_no36_with192": [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219],
    "far_L15_28viol": [2,3,16,20,24,28,31,65,72,96,97,108,114,130,146,159,162,216,252],
    "far_L14_44viol": [8,18,20,22,24,27,31,64,65,72,73,128,144,160,162,216,219,224,252],
}

SPAN_ONLY_KEYS = {
    4456163387397,
    6635867678725,
    4456163313813,
    7748268402853,
    4436873709717,
    4417508755461,
    3389833137899526,
    2823584649578518,
}


def bitset_for_support(A: Sequence[int]) -> int:
    b = 0
    for p in A:
        b |= 1 << (int(p) - 1)
    return b


def occupancy_bitset(rec: dict, support_bits: int) -> int:
    return (int(rec["point_bitset"]) & support_bits).bit_count()


def point_list_from_bitset(bs: int) -> List[int]:
    return [i + 1 for i in range(255) if (bs >> i) & 1]


def span_key8(points: Iterable[int]) -> int:
    pts = list(points)
    return pack_basis(rref_basis(pts, n=8))


def build_record_index(records: Sequence[dict]) -> Dict[int, dict]:
    return {int(r["key8"]): r for r in records}


def full_scan(label: str, support: Sequence[int], records: Sequence[dict], rec_by_key: Dict[int, dict], s: int = 19) -> dict:
    bits = bitset_for_support(support)
    violations: List[dict] = []
    slack_hist = Counter()
    slack_by_dim_L = Counter()
    near_rows_by_dim_L = Counter()
    near_rows = []

    for rec in records:
        L = int(rec["L"])
        cap = s - L
        occ = occupancy_bitset(rec, bits)
        slack = cap - occ
        if -2 <= slack <= 3:
            slack_hist[slack] += 1
            slack_by_dim_L[(int(rec["dim8"]), L, slack)] += 1
        if 0 <= slack <= 2:
            near_rows_by_dim_L[(int(rec["dim8"]), L, slack)] += 1
        if occ > cap:
            row_pts_bits = int(rec["point_bitset"]) & bits
            selected_pts = point_list_from_bitset(row_pts_bits)
            skey = span_key8(selected_pts)
            srec = rec_by_key[skey]
            span_occ = occupancy_bitset(srec, bits)
            span_cap = s - int(srec["L"])
            item = {
                "key8": int(rec["key8"]),
                "basis8": list(unpack_basis(int(rec["key8"]))),
                "key9": int(rec["key9"]),
                "dim8": int(rec["dim8"]),
                "dim9": int(rec["dim9"]),
                "L": L,
                "cap": cap,
                "occupancy": occ,
                "excess": occ - cap,
                "selected_points": selected_pts,
                "selected_point_count": len(selected_pts),
                "span_of_selected_key8": int(skey),
                "span_of_selected_basis8": list(unpack_basis(skey)),
                "span_of_selected_dim8": int(skey & 0xF),
                "span_of_selected_L": int(srec["L"]),
                "span_of_selected_cap": span_cap,
                "span_of_selected_occupancy": span_occ,
                "span_of_selected_excess": span_occ - span_cap,
                "same_as_selected_span": bool(int(rec["key8"]) == int(skey)),
                "would_be_seen_by_span_only_scan": bool(int(rec["key8"]) in SPAN_ONLY_KEYS),
            }
            violations.append(item)

    by_dim = Counter(v["dim8"] for v in violations)
    by_L = Counter(v["L"] for v in violations)
    by_excess = Counter(v["excess"] for v in violations)
    missed = [v for v in violations if not v["would_be_seen_by_span_only_scan"]]
    violations.sort(key=lambda v: (v["excess"], v["L"], v["occupancy"], v["dim8"], v["key8"]), reverse=True)

    return {
        "label": label,
        "support": list(map(int, support)),
        "support_size": len(set(support)),
        "total_terms": len(support),
        "complete_constraint_count": len(records),
        "complete_violation_count": len(violations),
        "violations_by_dim8": {str(k): int(v) for k, v in sorted(by_dim.items())},
        "violations_by_L": {str(k): int(v) for k, v in sorted(by_L.items())},
        "violations_by_excess": {str(k): int(v) for k, v in sorted(by_excess.items())},
        "violations": violations,
        "span_only_seen_count": sum(1 for v in violations if v["would_be_seen_by_span_only_scan"]),
        "span_only_missed_count": len(missed),
        "span_only_missed_violations": missed,
        "slack_histogram_m2_to_3": {str(k): int(v) for k, v in sorted(slack_hist.items())},
        "near_tight_rows_by_dim_L_slack_head": [
            {"dim8": int(dim), "L": int(L), "slack": int(slack), "count": int(cnt)}
            for (dim, L, slack), cnt in sorted(near_rows_by_dim_L.items(), key=lambda kv: (kv[0][0], kv[0][1], kv[0][2]))
        ],
    }


def main() -> None:
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    lut, lut_meta = load_lut(LUT_PATH)
    core = CoreQuotient(1)
    records, meta = build_core_constraints(core, lut)
    rec_by_key = build_record_index(records)

    by_dim_L = Counter((int(r["dim8"]), int(r["L"])) for r in records)
    by_dim = Counter(int(r["dim8"]) for r in records)
    by_L = Counter(int(r["L"]) for r in records)
    core_distribution = {
        "constraint_count": len(records),
        "by_dim8": {str(k): int(v) for k, v in sorted(by_dim.items())},
        "by_L": {str(k): int(v) for k, v in sorted(by_L.items())},
        "by_dim8_L": [
            {"dim8": int(dim), "L": int(L), "count": int(cnt)}
            for (dim, L), cnt in sorted(by_dim_L.items())
        ],
        "dimension_5_total": int(by_dim[5]),
        "dimension_5_L12_count": int(by_dim_L[(5, 12)]),
        "dimension_6_total": int(by_dim[6]),
        "dimension_6_L12_count": int(by_dim_L[(6, 12)]),
        "note": "These are E11 quotient rows only: full 9D rows containing the E11 pivot, projected to F2^8.",
    }

    scans = {}
    for name, supp in SUPPORTS.items():
        scans[name] = full_scan(name, supp, records, rec_by_key, s=19)

    result = {
        "schema": "complete_core_rescan_v1",
        "purpose": "Correct analysis overstatements and resume the E11 distinct branch from the complete 417,199-row core Wang table.",
        "elapsed_sec": time.time() - t0,
        "lut_meta_coverage_ok": lut_meta.get("coverage_ok"),
        "core_meta": meta,
        "core_distribution": core_distribution,
        "support_scans": scans,
        "corrections": {
            "full_dimension_histogram_not_core_table": True,
            "span_only_near_miss_scan_partial": True,
            "base_complete_violation_count": scans["54_base_9violation"]["complete_violation_count"],
            "base_span_only_seen_count": scans["54_base_9violation"]["span_only_seen_count"],
            "base_span_only_missed_count": scans["54_base_9violation"]["span_only_missed_count"],
        },
    }
    out = OUTDIR / "complete_core_rescan_and_corrections.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")

    print(json.dumps({
        "out": str(out),
        "elapsed_sec": round(time.time() - t0, 3),
        "core_dim_counts": core_distribution["by_dim8"],
        "core_dim5_L12": core_distribution["dimension_5_L12_count"],
        "core_dim6_L12": core_distribution["dimension_6_L12_count"],
        "support_violation_counts": {k: v["complete_violation_count"] for k, v in scans.items()},
        "base_span_only_seen": scans["54_base_9violation"]["span_only_seen_count"],
        "base_span_only_missed": scans["54_base_9violation"]["span_only_missed_count"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
