#!/usr/bin/env python3
"""analysis: exact check of the diffuse uniform LP point against current cut families.

The recent face-cut loop produces valid integer cuts of the form
    sum_{p in J} x_p <= 18
for individual infeasible support faces J.  This script records the structural
reason these cuts cannot by themselves yield an LP infeasibility proof: the
uniform point x_p=19/255 satisfies all complete E11 Wang inequalities and every
such face cut with |J| <= floor(18*255/19)=241.

The calculation is exact rational arithmetic for the uniform point; it does not
claim anything about integer support feasibility.
"""
from __future__ import annotations

import json
import math
import sys
import time
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import ROOT, build_core_constraints  # noqa: E402

LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
TRANSPORTED_J65 = ROOT / "workspace/data/j65_transport/transported_J65_family.json"
FACE1 = ROOT / "workspace/data/face_loop/face_cpsat_transJ65_random630631.json"
FACE2 = ROOT / "workspace/data/face_loop/face_cpsat_transJ65_random630632.json"
OVERLAP_BASE = ROOT / "workspace/data/transported_overlap/wang_invariance_check.json"
OUT = ROOT / "workspace/data/uniform_reach/uniform_cut_reach.json"


def points_from_bitset(mask: int) -> list[int]:
    pts = []
    bs = int(mask)
    while bs:
        bit = bs & -bs
        pts.append(bit.bit_length())
        bs ^= bit
    return pts


def load_face(path: Path) -> dict:
    if not path.exists():
        return {"path": str(path), "exists": False}
    d = json.loads(path.read_text())
    J = [int(p) for p in d.get("J_points", [])]
    return {
        "path": str(path),
        "exists": True,
        "status": d.get("status"),
        "J_size": len(J),
        "J_points": J,
        "uniform_lhs": str(Fraction(19 * len(J), 255)),
        "uniform_lhs_float": float(Fraction(19 * len(J), 255)),
        "face_cut_bound_if_proved": 18,
        "uniform_slack_to_bound_18": str(Fraction(18, 1) - Fraction(19 * len(J), 255)),
        "would_cut_uniform_if_face_bound_18": Fraction(19 * len(J), 255) > 18,
    }


def main() -> None:
    t0 = time.time()
    OUT.parent.mkdir(parents=True, exist_ok=True)
    lut, lut_meta = load_lut(LUT_PATH)
    records, complete_meta = build_core_constraints(CoreQuotient(1), lut)
    u = Fraction(19, 255)
    by_dim = defaultdict(lambda: {"count": 0, "min_cap": None, "max_uniform_lhs": Fraction(0), "min_slack": None, "example_min_slack": None})
    by_dim_L = {}
    violations = []
    min_slack = None
    min_slack_records = []
    cap_min_by_dim = {}
    cap_hist_by_dim = defaultdict(Counter)
    for i, rec in enumerate(records):
        dim = int(rec["dim8"])
        L = int(rec["L"])
        cap = 19 - L
        pop = int(rec["point_bitset"]).bit_count()
        lhs = u * pop
        slack = Fraction(cap, 1) - lhs
        if slack < 0:
            violations.append({"row_index": i, "dim8": dim, "L": L, "cap": cap, "pop": pop, "lhs": str(lhs), "slack": str(slack)})
        if min_slack is None or slack < min_slack:
            min_slack = slack
            min_slack_records = [{"row_index": i, "key8": int(rec["key8"]), "dim8": dim, "L": L, "cap": cap, "pop": pop, "lhs": str(lhs), "slack": str(slack)}]
        elif slack == min_slack and len(min_slack_records) < 20:
            min_slack_records.append({"row_index": i, "key8": int(rec["key8"]), "dim8": dim, "L": L, "cap": cap, "pop": pop, "lhs": str(lhs), "slack": str(slack)})
        s = by_dim[dim]
        s["count"] += 1
        if s["min_cap"] is None or cap < s["min_cap"]:
            s["min_cap"] = cap
        if lhs > s["max_uniform_lhs"]:
            s["max_uniform_lhs"] = lhs
        if s["min_slack"] is None or slack < s["min_slack"]:
            s["min_slack"] = slack
            s["example_min_slack"] = {"row_index": i, "key8": int(rec["key8"]), "L": L, "cap": cap, "pop": pop}
        cap_hist_by_dim[dim][cap] += 1
        key = (dim, L)
        if key not in by_dim_L:
            by_dim_L[key] = {"count": 0, "cap": cap, "pop_values": Counter(), "min_slack": None, "max_lhs": Fraction(0)}
        by_dim_L[key]["count"] += 1
        by_dim_L[key]["pop_values"][pop] += 1
        if lhs > by_dim_L[key]["max_lhs"]:
            by_dim_L[key]["max_lhs"] = lhs
        if by_dim_L[key]["min_slack"] is None or slack < by_dim_L[key]["min_slack"]:
            by_dim_L[key]["min_slack"] = slack
    # In this project every d-dimensional quotient subspace has 2^d-1 nonzero points; keep a check.
    dim_summary = {}
    for d in sorted(by_dim):
        s = by_dim[d]
        expected_pop = (1 << d) - 1
        dim_summary[str(d)] = {
            "row_count": int(s["count"]),
            "expected_nonzero_points_in_row": expected_pop,
            "uniform_lhs_expected": str(u * expected_pop),
            "uniform_lhs_expected_float": float(u * expected_pop),
            "min_capacity_recorded": int(s["min_cap"]),
            "min_slack_recorded": str(s["min_slack"]),
            "min_slack_recorded_float": float(s["min_slack"]),
            "example_min_slack": s["example_min_slack"],
            "cap_histogram": {str(k): int(v) for k, v in sorted(cap_hist_by_dim[d].items())},
        }
    dimL_summary = {}
    for (d, L), s in sorted(by_dim_L.items()):
        dimL_summary[f"d{d}_L{L}"] = {
            "count": int(s["count"]),
            "cap": int(s["cap"]),
            "pop_values": {str(k): int(v) for k, v in sorted(s["pop_values"].items())},
            "max_uniform_lhs": str(s["max_lhs"]),
            "min_slack": str(s["min_slack"]),
        }
    face_records = [load_face(FACE1), load_face(FACE2)]
    j65 = {"path": str(TRANSPORTED_J65), "exists": TRANSPORTED_J65.exists()}
    if TRANSPORTED_J65.exists():
        fam = json.loads(TRANSPORTED_J65.read_text())
        sizes = sorted({len(c["points"]) for c in fam.get("cuts", [])})
        vals = [Fraction(19 * n, 255) for n in sizes]
        j65.update({
            "unique_image_count": fam.get("unique_image_count"),
            "all_image_sizes": sizes,
            "uniform_lhs_values": [str(v) for v in vals],
            "uniform_lhs_float_values": [float(v) for v in vals],
            "bound": 18,
            "min_slack_to_bound": str(min(Fraction(18, 1) - v for v in vals)) if vals else None,
            "image_family_sha256": fam.get("image_family_sha256"),
        })
    overlap = {"path": str(OVERLAP_BASE), "exists": OVERLAP_BASE.exists()}
    if OVERLAP_BASE.exists():
        d = json.loads(OVERLAP_BASE.read_text())
        base = [int(p) for p in d.get("base_support", [])]
        val = Fraction(19 * len(base), 255)
        overlap.update({
            "base_support_size": len(base),
            "transported_image_count": d.get("unique_whole_support_image_count"),
            "bound": 15,
            "uniform_lhs": str(val),
            "uniform_lhs_float": float(val),
            "uniform_slack_to_bound_15": str(Fraction(15, 1) - val),
        })
    threshold = math.floor(Fraction(18 * 255, 19))
    payload = {
        "schema": "uniform_cut_reach_v1",
        "meaning": "Exact rational check that the diffuse point x_p=19/255 satisfies all complete E11 Wang rows and is untouched by the current small-face cuts. This separates LP-infeasibility ambitions from integer proof-search uses of face cuts.",
        "uniform_value_each_coordinate": str(u),
        "uniform_total": str(255 * u),
        "complete_wang_rows_checked": len(records),
        "complete_meta": complete_meta,
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "uniform_violations_count": len(violations),
        "uniform_violation_examples": violations[:10],
        "minimum_uniform_wang_slack": str(min_slack),
        "minimum_uniform_wang_slack_float": float(min_slack) if min_slack is not None else None,
        "minimum_slack_records_head": min_slack_records,
        "by_dimension": dim_summary,
        "by_dimension_and_L": dimL_summary,
        "face_cut_bound_18_size_threshold": threshold,
        "face_cut_threshold_statement": "Any cut sum_{p in J} x_p <= 18 with |J| <= floor(18*255/19)=241 is satisfied by the uniform point.",
        "current_transported_J65_family": j65,
        "new_faces": face_records,
        "radius3_overlap_family": overlap,
        "scientific_interpretation": "Small support-face exclusions can be sound learned clauses for integer search, but any LP-based global contradiction must introduce inequalities cutting diffuse configurations such as this uniform point; serial exclusions of 65-71 point faces cannot do that.",
        "elapsed_sec": round(time.time() - t0, 3),
    }
    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(OUT),
        "uniform_violations_count": len(violations),
        "minimum_uniform_wang_slack": str(min_slack),
        "threshold_for_bound18_face_size": threshold,
        "j65_uniform_lhs": j65.get("uniform_lhs_values"),
        "face_sizes": [r.get("J_size") for r in face_records],
        "elapsed_sec": payload["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
