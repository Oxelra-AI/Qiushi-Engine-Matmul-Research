#!/usr/bin/env python3
"""Validate and compare analysis face-conditioned local memberships.

This script independently recomputes local 4D Wang constraints and J-face fiber
capacities from the saved global fractional point.  It checks that every active
profile in the analysis convex combinations satisfies total=19, the face caps,
and the 66 induced local Wang inequalities, and that the convex combination
reconstructs the target profile.  It also compares with the original analysis
generic local mixtures to see whether those displayed mixtures used profiles
that exceed the J-face capacities.
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import build_core_constraints
from fractional_local_membership import build_local_constraints, dot2, eval_color, local_matrix

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/face_local_hull"
FACE_PATH = OUTDIR / "face_conditioned_local_hull_results.json"
GLOBAL_PATH = ROOT / "workspace/data/local_hull/global_fractional_solution.json"
GENERIC_PATHS = [
    ROOT / "workspace/data/local_hull/fractional_local_membership.json",
    ROOT / "workspace/data/local_hull/active_fractional_local_membership.json",
]
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"


def face_caps_and_target(ann: Sequence[int], x: np.ndarray, J: Sequence[int]):
    caps = [0] * 16
    target = np.zeros(16, dtype=float)
    for p in J:
        c = eval_color(p, ann)
        caps[c] += 1
        target[c] += x[p - 1]
    return caps, target


def profile_local_failures(profile: Sequence[int], caps: Sequence[int], constraints: Sequence[Dict]):
    fail = []
    if sum(profile) != 19:
        fail.append({"kind": "total", "sum": int(sum(profile))})
    for i, (v, cap) in enumerate(zip(profile, caps)):
        if int(v) < 0 or int(v) > int(cap):
            fail.append({"kind": "face_cap", "color": i, "value": int(v), "cap": int(cap), "excess": int(v) - int(cap)})
    for ci, con in enumerate(constraints):
        occ = sum(int(profile[v]) for v in con["perp_colors"])
        if occ > int(con["cap"]):
            fail.append({"kind": "local_wang", "constraint_index": ci, "occ": int(occ), "cap": int(con["cap"]), "L": int(con["L"]), "colors": list(con["perp_colors"])})
    return fail


def active_profiles_from_result(result: Dict):
    cert = result.get("hull_test", {}).get("membership_certificate")
    if not cert:
        return []
    return [{"profile_index": int(t[0]), "weight": float(t[1]), "profile": [int(z) for z in t[2]]} for t in cert.get("active_combination", [])]


def generic_by_ann():
    d = {}
    for path in GENERIC_PATHS:
        data = json.loads(path.read_text())
        for pr in data.get("pair_results", []):
            ann = tuple(int(z) for z in pr["annihilator_basis"])
            d[ann] = {"source_file": str(path), "source_pair_index": int(pr["pair_index"]), "result": pr}
    return d


def main():
    t0 = time.time()
    face = json.loads(FACE_PATH.read_text())
    glob = json.loads(GLOBAL_PATH.read_text())
    x = np.array(glob["global_lp"]["x_full"], dtype=float)
    J = [p for p, val in enumerate(x, start=1) if val > 1e-10]
    lut, _ = load_lut(LUT_PATH)
    records, _meta = build_core_constraints(CoreQuotient(1), lut)
    rec_by_key = {int(r["key8"]): r for r in records}
    gen = generic_by_ann()

    map_summaries = []
    face_failure_count = 0
    face_reconstruction_max = 0.0
    generic_invalid_maps = 0
    generic_invalid_weight_total = 0.0

    for mr in face.get("map_results", []):
        ann = [int(z) for z in mr["annihilator_basis"]]
        ann_key = tuple(ann)
        constraints = build_local_constraints(ann, rec_by_key)
        caps, target = face_caps_and_target(ann, x, J)
        A, b = local_matrix(constraints)
        local_slacks = b - A.dot(target)
        cap_slacks = np.array(caps, dtype=float) - target

        face_active = active_profiles_from_result(mr)
        recon = np.zeros(16, dtype=float)
        face_bad_profiles = []
        for ap in face_active:
            prof = ap["profile"]
            recon += ap["weight"] * np.array(prof, dtype=float)
            fails = profile_local_failures(prof, caps, constraints)
            if fails:
                face_bad_profiles.append({"profile_index": ap["profile_index"], "weight": ap["weight"], "failure_count": len(fails), "failures_head": fails[:5], "profile": prof})
        recon_err = float(np.max(np.abs(recon - target))) if face_active else None
        face_reconstruction_max = max(face_reconstruction_max, recon_err or 0.0)
        face_failure_count += len(face_bad_profiles)

        generic_info = gen.get(ann_key)
        generic_summary = None
        if generic_info:
            gp = generic_info["result"]
            g_active = active_profiles_from_result(gp)
            bad = []
            invalid_weight = 0.0
            max_cap_excess = 0
            for ap in g_active:
                fails = profile_local_failures(ap["profile"], caps, constraints)
                cap_fails = [f for f in fails if f["kind"] == "face_cap"]
                if cap_fails:
                    invalid_weight += ap["weight"]
                    max_cap_excess = max(max_cap_excess, max(int(f["excess"]) for f in cap_fails))
                    bad.append({"profile_index": ap["profile_index"], "weight": ap["weight"], "cap_failures_head": cap_fails[:5], "profile": ap["profile"]})
            if bad:
                generic_invalid_maps += 1
                generic_invalid_weight_total += invalid_weight
            generic_summary = {
                "source_file": generic_info["source_file"],
                "source_pair_index": generic_info["source_pair_index"],
                "active_combination_size": len(g_active),
                "profiles_exceeding_face_caps": len(bad),
                "invalid_mixture_weight_due_to_face_caps": invalid_weight,
                "max_face_cap_excess_in_generic_profiles": max_cap_excess,
                "bad_profiles_head": bad[:8],
            }

        map_summaries.append({
            "map_index": int(mr["map_index"]),
            "annihilator_basis": ann,
            "face_caps_match_output": caps == [int(z) for z in mr["face_fiber_caps"]],
            "target_recomputed_max_abs_error": float(np.max(np.abs(target - np.array(mr["target_profile"], dtype=float)))),
            "target_sum": float(target.sum()),
            "min_face_cap_slack": float(cap_slacks.min()),
            "min_local_wang_slack": float(local_slacks.min()),
            "tight_local_wang_constraints": int(np.sum(np.abs(local_slacks) < 1e-7)),
            "face_active_combination_size": len(face_active),
            "face_membership_reconstruction_max_abs_error": recon_err,
            "face_bad_profile_count": len(face_bad_profiles),
            "face_bad_profiles_head": face_bad_profiles[:5],
            "generic_mixture_face_comparison": generic_summary,
        })

    out = OUTDIR / "face_membership_validation_and_generic_comparison.json"
    out.write_text(json.dumps({
        "schema": "face_membership_validation_v1",
        "elapsed_sec": time.time() - t0,
        "meaning": "Independent validation of analysis face-conditioned local memberships and comparison with the analysis generic local mixtures. Generic profile failures mean the displayed analysis convex combination used local profiles impossible on the J face; alternative analysis face-valid combinations may still exist.",
        "global_solution_file": str(GLOBAL_PATH),
        "face_result_file": str(FACE_PATH),
        "J_size": len(J),
        "tested_map_count": len(map_summaries),
        "face_total_bad_profiles": face_failure_count,
        "face_reconstruction_max_abs_error": face_reconstruction_max,
        "generic_maps_with_face_invalid_displayed_profiles": generic_invalid_maps,
        "generic_total_invalid_mixture_weight_due_to_face_caps": generic_invalid_weight_total,
        "map_summaries": map_summaries,
    }, indent=2) + "\n")
    print(json.dumps({
        "out": str(out),
        "tested_map_count": len(map_summaries),
        "face_total_bad_profiles": face_failure_count,
        "face_reconstruction_max_abs_error": face_reconstruction_max,
        "generic_maps_with_face_invalid_displayed_profiles": generic_invalid_maps,
        "generic_total_invalid_mixture_weight_due_to_face_caps": generic_invalid_weight_total,
        "elapsed_sec": time.time() - t0,
    }, indent=2))


if __name__ == "__main__":
    main()
