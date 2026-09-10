#!/usr/bin/env python3
r"""analysis: orbit-closed low-Wang-row separator after transported overlap cuts.

This model asks whether the next candidates can be pushed out of the small set
of geometric row types already exposed by the base near-miss and analysis
transported-overlap searches.  It starts from all L>=threshold Wang rows, adds
all transported radius-3 overlap cuts, and adds the complete E11-stabilizer
orbit closures of violated low-L Wang rows from selected seed supports.  Then it
runs the usual adaptive complete-Wang separation.

The purpose is exploratory/global: row orbit closures preserve point incidences
and use the verified analysis Wang-table invariance.  SAT candidates are still
not complete unless the full Wang rescan returns zero violations and then B/C
completion succeeds; UNKNOWN is not a theorem.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient  # noqa: E402
from complete_core_and_transversal import ROOT, build_core_constraints, saturation_domains, transversal_failures  # noqa: E402
from candidate_source_qcut_scan import eval_candidate_sources  # noqa: E402
from quotient_rank_cuts import build_contractions, point_mask_for_q  # noqa: E402
from cert_trace_separator import add_certificate_cuts, build_phi, full_violation_scan, points_for_rec  # noqa: E402
from distinct_trace_cut_cpsat import load_hint, load_trace_cuts, generate_stabilizer_permutations  # noqa: E402
from trace_dependency_family import dot8, eval_support_local_dependency  # noqa: E402
from neighborhood_repair import DEFAULT_SUPPORT  # noqa: E402
from overlap_cut_separator import load_overlap_centers, overlap_summary, support_bitset  # noqa: E402
from violation_orbit_profile import load_support_from_separator  # noqa: E402
from wang_invariance_check import basis_images_from_perm, transform_key8  # noqa: E402

OUTDIR = ROOT / "workspace/data/transported_overlap"
DEFAULT_OVERLAP_ANALYSIS = OUTDIR / "transported_overlap_analysis.json"
DEFAULT_CERTCUT_PATH = ROOT / "workspace/data/trace_dependency_cuts/trace_certificate_family_cuts_augmented.json"


def load_lut(path: Path):
    with path.open("rb") as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload["lut"].items()}, payload.get("meta", {})


def parse_seed_names(text: str) -> List[str]:
    return [z.strip() for z in text.split(",") if z.strip()]


def load_seed_supports(names: Sequence[str]) -> List[dict]:
    seeds = []
    for name in names:
        if name == "base":
            seeds.append({"name": "base", "source": "analysis/54 base", "A_cols": list(DEFAULT_SUPPORT)})
        elif name == "L15":
            path = OUTDIR / "overlap_cut_separator_L15_cert_3r_180s.json"
            A = load_support_from_separator(path, 0)
            if A:
                seeds.append({"name": "L15_overlap_round0", "source": str(path), "A_cols": A})
        elif name == "L14":
            path = OUTDIR / "overlap_cut_separator_L14_cert_2r_240s.json"
            A = load_support_from_separator(path, 0)
            if A:
                seeds.append({"name": "L14_overlap_round0", "source": str(path), "A_cols": A})
        elif name.startswith("file:"):
            path = Path(name[5:])
            A = load_support_from_separator(path, 0)
            if A:
                seeds.append({"name": path.stem, "source": str(path), "A_cols": A})
        else:
            raise ValueError(f"unknown seed {name}; use base,L15,L14,file:<json>")
    return seeds


def orbit_closure(keys: Iterable[int], basis_images_list: Sequence[Sequence[int]]) -> set[int]:
    closure = set()
    cache = {}
    for key in sorted(set(int(k) for k in keys)):
        if key in cache:
            orb = cache[key]
        else:
            orb = tuple(sorted({transform_key8(key, imgs) for imgs in basis_images_list}))
            for z in orb:
                cache[z] = orb
        closure.update(orb)
    return closure


def add_wang_row(model, x, rec: dict, included: set[int]) -> bool:
    key = int(rec["key8"])
    if key in included:
        return False
    cap = 19 - int(rec["L"])
    if cap >= 19:
        return False
    pts = points_for_rec(rec)
    if not pts:
        return False
    model.Add(sum(x[p] for p in pts) <= cap)
    included.add(key)
    return True


def main() -> None:
    from ortools.sat.python import cp_model

    ap = argparse.ArgumentParser()
    ap.add_argument("--threshold-L", type=int, default=15)
    ap.add_argument("--seeds", default="base,L15,L14")
    ap.add_argument("--solver-time", type=float, default=240.0)
    ap.add_argument("--max-rounds", type=int, default=3)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=5521)
    ap.add_argument("--overlap-analysis", type=Path, default=DEFAULT_OVERLAP_ANALYSIS)
    ap.add_argument("--overlap-max", type=int, default=15)
    ap.add_argument("--cert-cuts", action="store_true")
    ap.add_argument("--cert-cut-path", type=Path, default=DEFAULT_CERTCUT_PATH)
    ap.add_argument("--trace-cuts", choices=["none", "minimal", "size5"], default="none")
    ap.add_argument("--max-size5-cuts", type=int, default=None)
    ap.add_argument("--hint-source", type=Path, default=OUTDIR / "overlap_cut_separator_L15_cert_3r_180s.json")
    ap.add_argument("--out", type=Path, default=OUTDIR / "orbit_closed_separator.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    s = 19
    points = list(range(1, 256))
    core = CoreQuotient(1)
    lut, _ = load_lut(ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl")
    records, meta = build_core_constraints(core, lut)
    rec_by_key = {int(r["key8"]): r for r in records}
    T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
    contractions = build_contractions(T_core)
    masks = {q: point_mask_for_q(q) for q in contractions}
    centers, overlap_meta = load_overlap_centers(args.overlap_analysis, None)
    center_bits = [support_bitset(c) for c in centers]

    perms = [tuple(int(x) for x in p) for p in generate_stabilizer_permutations(include_transpose=True)]
    basis_images_list = [basis_images_from_perm(p) for p in perms]
    seed_supports = load_seed_supports(parse_seed_names(args.seeds))
    seed_profiles = []
    seed_violation_keys = set()
    for sr in seed_supports:
        scan = full_violation_scan(sr["A_cols"], records, s)
        keys = {int(v["key8"]) for v in scan["violations"]}
        seed_violation_keys |= keys
        seed_profiles.append({
            "name": sr["name"],
            "source": sr["source"],
            "A_cols": sr["A_cols"],
            "violation_count": scan["complete_violation_count"],
            "violations_by_L": scan["violations_by_L"],
            "violations_by_dim8": scan["violations_by_dim8"],
            "seed_violation_keys": sorted(keys),
        })
    orbit_keys = orbit_closure(seed_violation_keys, basis_images_list)
    orbit_by_L = Counter(int(rec_by_key[k]["L"]) for k in orbit_keys)
    orbit_by_dim = Counter(int(k & 0xF) for k in orbit_keys)

    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in points}
    model.Add(sum(x[p] for p in points) == s)
    w = {}
    contraction_lb = 0
    for q, c in contractions.items():
        w[int(q)] = model.NewIntVar(0, s, f"w_{q}")
        model.Add(w[int(q)] == sum(x[p] for p in points if dot8(q, p)))
        if int(c["rank"]) > 0:
            model.Add(w[int(q)] >= int(c["rank"]))
            contraction_lb += 1

    included = set()
    initial_by_L = Counter()
    initial_rows = 0
    for rec in records:
        L = int(rec["L"])
        if L < args.threshold_L:
            continue
        if add_wang_row(model, x, rec, included):
            initial_rows += 1
            initial_by_L[L] += 1
    orbit_rows_added = 0
    for key in sorted(orbit_keys):
        if add_wang_row(model, x, rec_by_key[key], included):
            orbit_rows_added += 1

    overlap_cut_count = 0
    for c in centers:
        model.Add(sum(x[p] for p in c) <= int(args.overlap_max))
        overlap_cut_count += 1

    local_cuts = load_trace_cuts(args.trace_cuts, ROOT / "workspace/data/trace_dependency_cuts/trace_dependency_cuts.json", ROOT / "workspace/data/trace_dependency_cuts/trace_dependency_size5_cuts.pkl", args.max_size5_cuts)
    local_hist = Counter()
    for cut in local_cuts:
        p = int(cut["p"])
        H = [int(q) for q in cut["H"]]
        model.Add(sum(w[q] for q in H) >= 9 * len(H) + x[p])
        local_hist[len(H)] += 1

    cert_summary = None
    if args.cert_cuts:
        cert_summary = add_certificate_cuts(model, x, w, contractions, None, args.cert_cut_path)

    hint = load_hint(args.hint_source, None)
    hint_added = False
    if hint:
        hs = set(int(p) for p in hint)
        for p in points:
            model.AddHint(x[p], 1 if p in hs else 0)
        hint_added = True

    build_sec = time.time() - t0
    rounds = []
    phi = None
    for r in range(args.max_rounds):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(args.solver_time)
        solver.parameters.num_search_workers = int(args.workers)
        solver.parameters.random_seed = int(args.seed + r)
        ts = time.time()
        status = solver.Solve(model)
        solve_sec = time.time() - ts
        status_name = solver.StatusName(status)
        print(f"round {r}: status={status_name} solve_sec={solve_sec:.3f}")
        rec = {"round": r, "status": status_name, "solve_sec": round(solve_sec, 3)}
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            rounds.append(rec)
            break
        A = [p for p in points if solver.Value(x[p])]
        scan = full_violation_scan(A, records, s)
        sat = saturation_domains(T_core, A)
        trans = transversal_failures(sat["sat_records"], sat["B_domains"], sat["C_domains"], 9, 9, max_report=10)
        qscan = eval_candidate_sources(f"orbit_closed_round_{r}", A, contractions, masks, max_source_size=2, max_store=20)
        if phi is None:
            phi = build_phi(T_core)
        local_dep = eval_support_local_dependency(A, sorted(phi), phi, {p: None for p in points})
        ov = overlap_summary(A, center_bits)
        new_rows = []
        for v in scan["violations"]:
            key = int(v["key8"])
            if key not in included:
                new_rows.append(v)
                included.add(key)
        for v in new_rows:
            model.Add(sum(x[p] for p in v["points"]) <= int(v["cap"]))
        rec.update({
            "A_cols": A,
            "complete_wang_violations": scan["complete_violation_count"],
            "complete_wang_max_excess": scan["max_excess"],
            "violations_by_L": scan["violations_by_L"],
            "violations_by_dim8": scan["violations_by_dim8"],
            "violations_head": scan["violations_head"],
            "new_rows_added": len(new_rows),
            "total_rows_included_after_round": len(included),
            "overlap_to_certified_base_orbit": ov,
            "zero_domain_terms": len(sat["summary"]["zero_domain_terms"]),
            "linear_pass": sat["summary"]["linear_membership"]["necessary_linear_test_passed"],
            "affine_dim": sat["summary"]["linear_membership"].get("affine_solution_dimension_if_consistent"),
            "saturated_contractions": sat["summary"].get("saturated_contraction_count"),
            "transversal_failures": trans["failure_count_reported"],
            "quotient_rank_violations_size2": qscan["violated_guarded_instances"],
            "trace_local_dependency": local_dep,
        })
        print(f"  A={A}")
        print(f"  viol={scan['complete_violation_count']} byL={scan['violations_by_L']} new={len(new_rows)} maxov={ov['max_transported_overlap']} sat={rec['saturated_contractions']} trace_bad={local_dep['exact_local_inconsistent_terms']}")
        rounds.append(rec)
        if scan["complete_violation_count"] == 0:
            break
        if len(new_rows) == 0:
            model.Add(sum(x[p] for p in A) <= 18)

    result = {
        "schema": "orbit_closed_separator_v1",
        "field": "F2",
        "core": "E11 quotient core",
        "rank_s": s,
        "meaning": "Adaptive support search with point-level Wang rows, transported overlap cuts, and full stabilizer orbit closures of low-L violated rows from selected seeds.",
        "parameters": {
            "threshold_L": args.threshold_L,
            "seeds": args.seeds,
            "solver_time": args.solver_time,
            "max_rounds": args.max_rounds,
            "workers": args.workers,
            "seed": args.seed,
            "cert_cuts": bool(args.cert_cuts),
            "trace_cuts": args.trace_cuts,
            "max_size5_cuts": args.max_size5_cuts,
            "overlap_max": args.overlap_max,
            "hint_source": str(args.hint_source) if args.hint_source else None,
        },
        "build_sec": round(build_sec, 3),
        "complete_core_table_meta": meta,
        "initial_threshold_rows": initial_rows,
        "initial_threshold_rows_by_L": {str(k): int(v) for k, v in sorted(initial_by_L.items())},
        "seed_profiles": seed_profiles,
        "seed_violation_key_count": len(seed_violation_keys),
        "violation_orbit_closure_key_count": len(orbit_keys),
        "violation_orbit_closure_by_L": {str(k): int(v) for k, v in sorted(orbit_by_L.items())},
        "violation_orbit_closure_by_dim8": {str(k): int(v) for k, v in sorted(orbit_by_dim.items())},
        "orbit_rows_added_beyond_threshold": orbit_rows_added,
        "total_rows_initial_after_orbit_closure": len(included),
        "contraction_lower_bounds": contraction_lb,
        "overlap_cut_count": overlap_cut_count,
        "overlap_source": str(args.overlap_analysis),
        "local_trace_cuts": len(local_cuts),
        "local_trace_cut_size_hist": {str(k): int(v) for k, v in sorted(local_hist.items())},
        "certificate_cut_summary": cert_summary,
        "hint_added": hint_added,
        "rounds": rounds,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(args.out),
        "seed_violation_keys": len(seed_violation_keys),
        "orbit_closure_keys": len(orbit_keys),
        "orbit_rows_added_beyond_threshold": orbit_rows_added,
        "rounds": len(rounds),
        "last": rounds[-1] if rounds else None,
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True)[:5000])


if __name__ == "__main__":
    main()
