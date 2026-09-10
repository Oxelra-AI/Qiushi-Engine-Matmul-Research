#!/usr/bin/env python3
r"""analysis: adaptive Wang-row separator with corrected certificate cuts.

Start from the L>=15 distinct E11-core support model plus contraction lower
bounds and correctly guarded trace-certificate cuts.  After each CP-SAT support,
rescan the full 417,199-row E11 Wang table and add every violated row.  This is
an exact lazy separation experiment: a zero-violation support is a genuine
complete-Wang A-support candidate (still not a tensor decomposition), while
UNKNOWN/infeasible without proof remains search evidence only.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient  # noqa: E402
from complete_core_and_transversal import (  # noqa: E402
    ROOT,
    build_core_constraints,
    saturation_domains,
    transversal_failures,
)
from candidate_source_qcut_scan import eval_candidate_sources  # noqa: E402
from quotient_rank_cuts import build_contractions, point_mask_for_q  # noqa: E402
from distinct_cert_trace_cpsat import add_mod2_constraint  # noqa: E402
from distinct_trace_cut_cpsat import load_hint, load_trace_cuts  # noqa: E402
from trace_dependency_family import dot8, eval_support_local_dependency, trace_mask_correct  # noqa: E402
from dual_basis_instrument import gf2_mat_inv  # noqa: E402
from fixed_A_saturation import contraction_matrix, mat_rank_f2  # noqa: E402
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis  # noqa: E402

OUTDIR = ROOT / "workspace/data/trace_dependency_cuts"
CERTCUT_PATH = OUTDIR / "trace_certificate_family_cuts.json"


def load_lut(path: Path):
    with path.open("rb") as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload["lut"].items()}, payload.get("meta", {})


def build_phi(T_core: np.ndarray) -> Dict[int, int]:
    phi = {}
    for q in range(1, 1 << 8):
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) == 9:
            inv = gf2_mat_inv(M)
            if inv is None:
                raise RuntimeError(q)
            phi[int(q)] = trace_mask_correct(inv)
    return phi


def points_for_rec(rec: dict) -> List[int]:
    if "point_bitset" in rec:
        b = int(rec["point_bitset"])
        return [i + 1 for i in range(255) if (b >> i) & 1]
    return subspace_points_from_basis(unpack_basis(int(rec["key8"])))


def full_violation_scan(A: Sequence[int], records: Sequence[dict], s: int = 19) -> dict:
    Aset = set(int(x) for x in A)
    violations = []
    by_L = Counter()
    by_dim = Counter()
    max_excess = 0
    for rec in records:
        L = int(rec["L"])
        cap = s - L
        if cap >= s:
            continue
        pts = points_for_rec(rec)
        if not pts:
            continue
        occ = sum(1 for p in pts if p in Aset)
        if occ > cap:
            excess = occ - cap
            max_excess = max(max_excess, excess)
            by_L[L] += 1
            by_dim[int(rec["dim8"])] += 1
            violations.append({
                "key8": int(rec["key8"]),
                "L": L,
                "dim8": int(rec["dim8"]),
                "cap": cap,
                "occupancy": occ,
                "excess": excess,
                "point_count": len(pts),
                "points": pts,
            })
    return {
        "complete_violation_count": len(violations),
        "max_excess": max_excess,
        "violations_by_L": {str(k): int(v) for k, v in sorted(by_L.items())},
        "violations_by_dim8": {str(k): int(v) for k, v in sorted(by_dim.items())},
        "violations": violations,
        "violations_head": [{k: v for k, v in row.items() if k != "points"} for row in violations[:30]],
    }


def add_certificate_cuts(model, x, w, contractions, max_certs=None, cert_cut_path: Path = CERTCUT_PATH) -> dict:
    cert_data = json.loads(cert_cut_path.read_text())
    certs = cert_data.get("certificates", [])
    if max_certs is not None:
        certs = certs[: max(0, int(max_certs))]
    sat_bool = {}
    aux = 0
    for q, c in contractions.items():
        if int(c["rank"]) != 9:
            continue
        b = model.NewBoolVar(f"sat9_{q}")
        model.Add(w[int(q)] == 9).OnlyEnforceIf(b)
        model.Add(w[int(q)] >= 10).OnlyEnforceIf(b.Not())
        sat_bool[int(q)] = b
        aux += 1
    local_inc = 0
    parity = 0
    guard_sizes = []
    for ci, cert in enumerate(certs):
        G = [int(q) for q in cert["guard_qs"]]
        guard_sizes.append(len(G))
        g = model.NewBoolVar(f"cert{ci}_guard")
        aux += 1
        if G:
            model.AddBoolAnd([sat_bool[q] for q in G]).OnlyEnforceIf(g)
            model.AddBoolOr([sat_bool[q].Not() for q in G] + [g])
        else:
            model.Add(g == 1)
        inc = cert.get("inconsistent_directions", [])
        if inc:
            model.Add(sum(x[int(r["p"])] for r in inc) == 0).OnlyEnforceIf(g)
            local_inc += 1
        for r in inc:
            H = [int(q) for q in r.get("witness", [])]
            p = int(r["p"])
            if H:
                model.Add(sum(w[q] for q in H) >= 9 * len(H) + x[p])
                local_inc += 1
        free = [int(p) for p in cert.get("free_directions", [])]
        forced1 = [int(p) for p in cert.get("forced_1_directions", [])]
        nf = model.NewBoolVar(f"cert{ci}_nofree")
        aux += 1
        free_sum = sum(x[p] for p in free)
        model.Add(free_sum == 0).OnlyEnforceIf(nf)
        model.Add(free_sum >= 1).OnlyEnforceIf(nf.Not())
        active = model.NewBoolVar(f"cert{ci}_parity_active")
        aux += 1
        model.AddImplication(active, g)
        model.AddImplication(active, nf)
        model.AddBoolOr([g.Not(), nf.Not(), active])
        aux += add_mod2_constraint(model, [x[p] for p in forced1], int(cert["tensor_rhs_parity"]), active, f"cert{ci}_parity")
        parity += 1
    return {"certificate_count": len(certs), "guard_sizes": guard_sizes, "local_inconsistent_cuts": local_inc, "guarded_parity_cuts": parity, "aux_vars": aux}


def main() -> None:
    from ortools.sat.python import cp_model
    ap = argparse.ArgumentParser()
    ap.add_argument("--threshold-L", type=int, default=15)
    ap.add_argument("--solver-time", type=float, default=120.0)
    ap.add_argument("--max-rounds", type=int, default=6)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=5355)
    ap.add_argument("--cert-cuts", action="store_true")
    ap.add_argument("--cert-cut-path", type=Path, default=CERTCUT_PATH)
    ap.add_argument("--max-certs", type=int, default=None)
    ap.add_argument("--trace-cuts", choices=["none", "minimal", "size5"], default="none")
    ap.add_argument("--max-size5-cuts", type=int, default=None)
    ap.add_argument("--hint-source", type=Path, default=ROOT / "workspace/data/distinct_line_cover/best_L15_hint_rounds.json")
    ap.add_argument("--out", type=Path, default=OUTDIR / "cert_trace_separator.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    s = 19
    points = list(range(1, 256))
    core = CoreQuotient(1)
    lut, _meta_lut = load_lut(ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl")
    records, meta = build_core_constraints(core, lut)
    T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
    contractions = build_contractions(T_core)
    masks = {q: point_mask_for_q(q) for q in contractions}

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
    initial_rows = 0
    initial_by_L = Counter()
    for rec in records:
        L = int(rec["L"])
        if L < args.threshold_L:
            continue
        cap = s - L
        if cap >= s:
            continue
        pts = points_for_rec(rec)
        if not pts:
            continue
        model.Add(sum(x[p] for p in pts) <= cap)
        included.add(int(rec["key8"]))
        initial_rows += 1
        initial_by_L[L] += 1

    local_cuts = load_trace_cuts(args.trace_cuts, OUTDIR / "trace_dependency_cuts.json", OUTDIR / "trace_dependency_size5_cuts.pkl", args.max_size5_cuts)
    local_cut_size_hist = Counter()
    for cut in local_cuts:
        p = int(cut["p"])
        H = [int(q) for q in cut["H"]]
        model.Add(sum(w[q] for q in H) >= 9 * len(H) + x[p])
        local_cut_size_hist[len(H)] += 1

    cert_summary = None
    if args.cert_cuts:
        cert_summary = add_certificate_cuts(model, x, w, contractions, args.max_certs, args.cert_cut_path)

    hint = load_hint(args.hint_source, None)
    if hint:
        hs = set(int(z) for z in hint)
        for p in points:
            model.AddHint(x[p], 1 if p in hs else 0)

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
        qscan = eval_candidate_sources(f"separator_round_{r}", A, contractions, masks, max_source_size=2, max_store=20)
        if phi is None:
            phi = build_phi(T_core)
        local_dep = eval_support_local_dependency(A, sorted(phi), phi, {p: None for p in points})
        new_rows = []
        for v in scan["violations"]:
            key = int(v["key8"])
            if key not in included:
                new_rows.append(v)
                included.add(key)
        for v in new_rows:
            pts = v["points"]
            model.Add(sum(x[p] for p in pts) <= int(v["cap"]))
        rec.update({
            "A_cols": A,
            "complete_wang_violations": scan["complete_violation_count"],
            "complete_wang_max_excess": scan["max_excess"],
            "violations_by_L": scan["violations_by_L"],
            "violations_by_dim8": scan["violations_by_dim8"],
            "violations_head": scan["violations_head"],
            "new_rows_added": len(new_rows),
            "total_rows_included_after_round": len(included),
            "zero_domain_terms": len(sat["summary"]["zero_domain_terms"]),
            "linear_pass": sat["summary"]["linear_membership"]["necessary_linear_test_passed"],
            "affine_dim": sat["summary"]["linear_membership"].get("affine_solution_dimension_if_consistent"),
            "saturated_contractions": sat["summary"].get("saturated_contraction_count"),
            "transversal_failures": trans["failure_count_reported"],
            "quotient_rank_violations_size2": qscan["violated_guarded_instances"],
            "trace_local_dependency": local_dep,
        })
        print(f"  A={A}")
        print(f"  viol={scan['complete_violation_count']} byL={scan['violations_by_L']} new={len(new_rows)} sat={rec['saturated_contractions']} trace_local_bad={local_dep['exact_local_inconsistent_terms']}")
        rounds.append(rec)
        if scan["complete_violation_count"] == 0:
            break
        if len(new_rows) == 0:
            # Avoid repeated model if all violating rows were already present somehow.
            model.Add(sum(x[p] for p in A) <= 18)

    result = {
        "schema": "cert_trace_separator_v1",
        "field": "F2",
        "core": "E11 quotient core",
        "rank_s": s,
        "meaning": "Adaptive exact Wang-row separation starting from high-L rows plus optional sound trace-family cuts. Solver statuses are search evidence unless converted to proof.",
        "parameters": {
            "threshold_L": args.threshold_L,
            "solver_time": args.solver_time,
            "max_rounds": args.max_rounds,
            "workers": args.workers,
            "seed": args.seed,
            "cert_cuts": bool(args.cert_cuts),
            "cert_cut_path": str(args.cert_cut_path),
            "max_certs": args.max_certs,
            "trace_cuts": args.trace_cuts,
            "max_size5_cuts": args.max_size5_cuts,
            "hint_source": str(args.hint_source),
        },
        "build_sec": round(build_sec, 3),
        "initial_rows": initial_rows,
        "initial_rows_by_L": {str(k): int(v) for k, v in sorted(initial_by_L.items())},
        "contraction_lower_bounds": contraction_lb,
        "local_trace_cuts": len(local_cuts),
        "local_trace_cut_size_hist": {str(k): int(v) for k, v in sorted(local_cut_size_hist.items())},
        "certificate_cut_summary": cert_summary,
        "rounds": rounds,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(args.out), "rounds": len(rounds), "last": rounds[-1] if rounds else None, "elapsed_sec": result["elapsed_sec"]}, indent=2, sort_keys=True)[:5000])


if __name__ == "__main__":
    main()
