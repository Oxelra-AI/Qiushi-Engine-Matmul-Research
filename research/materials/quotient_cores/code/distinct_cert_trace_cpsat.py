#!/usr/bin/env python3
r"""analysis: distinct E11-core support search with corrected certificate cuts.

This CP-SAT model keeps all 255 point variables.  It can add two kinds of
sound trace-family restrictions:

1. Odd-dependency local cuts from trace_dependency_cuts.json or the
   enumerated size-5 family:
      sum_{q in H}(w(q)-9) >= x_p.
2. Guarded pure-parity cuts extracted from corrected XOR certificates.  For a
   certificate with saturated-contraction guard G, forced-1 directions O, free
   directions F, and tensor RHS r, impose
      sum_{p in O} x_p == r (mod 2)
   only when all q in G are saturated and no free direction is selected.  This
   repairs the analysis overinterpretation: parity is not imposed when selected
   escape/free directions can carry undetermined values.

FEASIBLE remains only an A-support candidate needing complete Wang rescanning,
fixed-A tests, corrected trace relaxation, and rank-one B/C completion.
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
    complete_core_wang_scan,
    saturation_domains,
    transversal_failures,
)
from candidate_source_qcut_scan import eval_candidate_sources  # noqa: E402
from quotient_rank_cuts import build_contractions, point_mask_for_q  # noqa: E402
from trace_compressed_support import build_compressed_system  # noqa: E402
from distinct_trace_cut_cpsat import load_lut, load_hint, load_trace_cuts  # noqa: E402
from trace_dependency_family import dot8, eval_support_local_dependency, trace_mask_correct  # noqa: E402
from dual_basis_instrument import gf2_mat_inv  # noqa: E402
from fixed_A_saturation import contraction_matrix, mat_rank_f2  # noqa: E402
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis  # noqa: E402

OUTDIR = ROOT / "workspace/data/trace_dependency_cuts"
CERTCUT_PATH = OUTDIR / "trace_certificate_family_cuts.json"


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


def add_mod2_constraint(model, terms, rhs: int, active_lit, name: str):
    # Linear enforced parity: sum terms = 2*k + rhs.
    n = len(terms)
    k = model.NewIntVar(0, max(0, n // 2 + 1), f"{name}_k")
    model.Add(sum(terms) - 2 * k == int(rhs)).OnlyEnforceIf(active_lit)
    return 1


def main() -> None:
    from ortools.sat.python import cp_model

    ap = argparse.ArgumentParser()
    ap.add_argument("--solver-time", type=float, default=300.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=5354)
    ap.add_argument("--min-L", type=int, default=15, help="Only include Wang rows with L>=min-L; 0 means all rows")
    ap.add_argument("--trace-cuts", choices=["none", "minimal", "size5"], default="none")
    ap.add_argument("--max-size5-cuts", type=int, default=None)
    ap.add_argument("--cert-cuts", choices=["none", "all"], default="none")
    ap.add_argument("--max-certs", type=int, default=None)
    ap.add_argument("--hint-source", type=Path, default=ROOT / "workspace/data/distinct_line_cover/best_L15_hint_rounds.json")
    ap.add_argument("--hint-round", type=int, default=None)
    ap.add_argument("--out", type=Path, default=OUTDIR / "distinct_cert_trace_cpsat.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    s = 19
    points = list(range(1, 256))
    core = CoreQuotient(1)
    lut, _lut_meta = load_lut(ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl")
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
        var = model.NewIntVar(0, s, f"w_{q}")
        w[int(q)] = var
        model.Add(var == sum(x[p] for p in points if dot8(q, p)))
        rk = int(c["rank"])
        if rk > 0:
            model.Add(var >= rk)
            contraction_lb += 1

    wang_count = 0
    dim_counts = Counter()
    skipped_by_minL = 0
    for rec in records:
        L = int(rec["L"])
        if args.min_L and L < args.min_L:
            skipped_by_minL += 1
            continue
        cap = s - L
        if cap >= s:
            continue
        pts = subspace_points_from_basis(unpack_basis(int(rec["key8"])))
        if pts:
            model.Add(sum(x[p] for p in pts) <= cap)
            wang_count += 1
            dim_counts[int(rec["dim8"])] += 1

    # Optional local trace-dependency cuts.
    cut_path = OUTDIR / "trace_dependency_cuts.json"
    size5_path = OUTDIR / "trace_dependency_size5_cuts.pkl"
    local_cuts = load_trace_cuts(args.trace_cuts, cut_path, size5_path, args.max_size5_cuts)
    local_cut_count = 0
    local_cut_size_hist = Counter()
    for cut in local_cuts:
        p = int(cut["p"])
        H = [int(q) for q in cut["H"]]
        model.Add(sum(w[q] for q in H) >= 9 * len(H) + x[p])
        local_cut_count += 1
        local_cut_size_hist[len(H)] += 1

    # Optional certificate pure-parity cuts with correct guards/free handling.
    cert_count = 0
    cert_local_inconsistent_cuts = 0
    cert_guarded_parity_cuts = 0
    cert_aux = 0
    cert_guard_sizes = []
    if args.cert_cuts == "all":
        cert_data = json.loads(CERTCUT_PATH.read_text())
        certs = cert_data.get("certificates", [])
        if args.max_certs is not None:
            certs = certs[: max(0, int(args.max_certs))]
        sat_bool = {}
        for q, c in contractions.items():
            if int(c["rank"]) != 9:
                continue
            b = model.NewBoolVar(f"sat9_{q}")
            # w(q)>=9 is already present for rank-9 q.
            model.Add(w[int(q)] == 9).OnlyEnforceIf(b)
            model.Add(w[int(q)] >= 10).OnlyEnforceIf(b.Not())
            sat_bool[int(q)] = b
            cert_aux += 1
        for ci, cert in enumerate(certs):
            cert_count += 1
            G = [int(q) for q in cert["guard_qs"]]
            cert_guard_sizes.append(len(G))
            # Whole certificate guard = all G saturated.
            g = model.NewBoolVar(f"cert{ci}_guard")
            cert_aux += 1
            if G:
                model.AddBoolAnd([sat_bool[q] for q in G]).OnlyEnforceIf(g)
                model.AddBoolOr([sat_bool[q].Not() for q in G] + [g])
            else:
                model.Add(g == 1)
            free = [int(p) for p in cert.get("free_directions", [])]
            inc_recs = cert.get("inconsistent_directions", [])
            forced1 = [int(p) for p in cert.get("forced_1_directions", [])]
            # Guard-level inconsistent directions: if all G saturated, none of them may be selected.
            if inc_recs:
                model.Add(sum(x[int(r["p"])] for r in inc_recs) == 0).OnlyEnforceIf(g)
                cert_local_inconsistent_cuts += 1
            # Stronger local witness cuts for the certificate's inconsistent directions.
            for r in inc_recs:
                p = int(r["p"])
                H = [int(q) for q in r.get("witness", [])]
                if H:
                    model.Add(sum(w[q] for q in H) >= 9 * len(H) + x[p])
                    cert_local_inconsistent_cuts += 1
            # no-free condition under this certificate.
            nf = model.NewBoolVar(f"cert{ci}_nofree")
            cert_aux += 1
            free_sum = sum(x[p] for p in free)
            model.Add(free_sum == 0).OnlyEnforceIf(nf)
            model.Add(free_sum >= 1).OnlyEnforceIf(nf.Not())
            active = model.NewBoolVar(f"cert{ci}_parity_active")
            cert_aux += 1
            model.AddImplication(active, g)
            model.AddImplication(active, nf)
            model.AddBoolOr([g.Not(), nf.Not(), active])
            cert_aux += add_mod2_constraint(model, [x[p] for p in forced1], int(cert["tensor_rhs_parity"]), active, f"cert{ci}_parity")
            cert_guarded_parity_cuts += 1

    hint = load_hint(args.hint_source, args.hint_round)
    hint_added = False
    if hint:
        hs = set(int(z) for z in hint)
        for p in points:
            model.AddHint(x[p], 1 if p in hs else 0)
        hint_added = True

    build_sec = time.time() - t0
    print(json.dumps({
        "build_sec": round(build_sec, 3),
        "wang_rows": wang_count,
        "wang_by_dim": {str(k): int(v) for k, v in sorted(dim_counts.items())},
        "skipped_by_minL": skipped_by_minL,
        "contraction_lower_bounds": contraction_lb,
        "local_trace_cuts": local_cut_count,
        "local_cut_size_hist": {str(k): int(v) for k, v in sorted(local_cut_size_hist.items())},
        "cert_count": cert_count,
        "cert_guard_sizes": cert_guard_sizes,
        "cert_local_inconsistent_cuts": cert_local_inconsistent_cuts,
        "cert_guarded_parity_cuts": cert_guarded_parity_cuts,
        "cert_aux": cert_aux,
        "hint_added": hint_added,
    }, indent=2, sort_keys=True))

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(args.solver_time)
    solver.parameters.num_search_workers = int(args.workers)
    solver.parameters.random_seed = int(args.seed)
    ts = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - ts
    status_name = solver.StatusName(status)
    print(f"status={status_name} solve_sec={solve_sec:.3f}")

    result = {
        "schema": "distinct_cert_trace_cpsat_v1",
        "field": "F2",
        "core": "E11 quotient core",
        "rank_s": s,
        "meaning": "255-variable distinct support model with complete/threshold Wang rows, contraction lower bounds, sound local trace-dependency cuts, and correctly guarded certificate parity cuts. Solver output is search evidence only unless converted to a proof.",
        "parameters": {
            "solver_time": args.solver_time,
            "workers": args.workers,
            "seed": args.seed,
            "min_L": args.min_L,
            "trace_cuts": args.trace_cuts,
            "max_size5_cuts": args.max_size5_cuts,
            "cert_cuts": args.cert_cuts,
            "max_certs": args.max_certs,
        },
        "constraint_summary": {
            "wang_rows": wang_count,
            "wang_by_dim": {str(k): int(v) for k, v in sorted(dim_counts.items())},
            "skipped_by_minL": skipped_by_minL,
            "contraction_weight_definitions": len(w),
            "contraction_lower_bounds": contraction_lb,
            "local_trace_dependency_cuts": local_cut_count,
            "local_cut_size_hist": {str(k): int(v) for k, v in sorted(local_cut_size_hist.items())},
            "certificate_count": cert_count,
            "certificate_guard_sizes": cert_guard_sizes,
            "certificate_local_inconsistent_cuts": cert_local_inconsistent_cuts,
            "certificate_guarded_parity_cuts": cert_guarded_parity_cuts,
            "certificate_aux_vars": cert_aux,
        },
        "hint_source": None if args.hint_source is None else str(args.hint_source),
        "hint_added": hint_added,
        "build_sec": round(build_sec, 3),
        "solver": "OR-Tools CP-SAT",
        "status": status_name,
        "solve_sec": round(solve_sec, 3),
    }

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        A = [p for p in points if solver.Value(x[p])]
        scan = complete_core_wang_scan("cert_solution", A, s, records, max_head=30)
        sat = saturation_domains(T_core, A)
        trans = transversal_failures(sat["sat_records"], sat["B_domains"], sat["C_domains"], 9, 9, max_report=10)
        qscan = eval_candidate_sources("cert_solution", A, contractions, masks, max_source_size=2, max_store=20)
        phi = build_phi(T_core)
        local_dep = eval_support_local_dependency(A, sorted(phi), phi, {p: None for p in points})
        compressed = build_compressed_system(T_core, A, {q: {**c, "M_inv": gf2_mat_inv(c["matrix"] if "matrix" in c else contraction_matrix(T_core, q))} for q, c in contractions.items()}, None) if False else None
        weights = {q: solver.Value(w[q]) for q in sorted(w)}
        result["solution"] = {
            "A_cols": A,
            "distinct_points": len(A),
            "complete_wang_violations": scan["complete_violation_count"],
            "complete_wang_max_excess": scan.get("max_excess"),
            "violations_by_L": scan.get("violations_by_full_lut_L"),
            "zero_domain_terms": len(sat["summary"]["zero_domain_terms"]),
            "linear_pass": sat["summary"]["linear_membership"]["necessary_linear_test_passed"],
            "affine_dim": sat["summary"]["linear_membership"].get("affine_solution_dimension_if_consistent"),
            "saturated_contractions": sat["summary"].get("saturated_contraction_count"),
            "transversal_failures": trans["failure_count_reported"],
            "quotient_rank_violations_size2": qscan["violated_guarded_instances"],
            "trace_local_dependency": local_dep,
            "rank9_weight_hist": {str(k): int(v) for k, v in sorted(Counter(weights[q] for q in weights if int(contractions[q]["rank"]) == 9).items())},
        }
        print("A_cols=", A)
        print("solution_checks=", json.dumps(result["solution"], indent=2, sort_keys=True)[:4000])
    result["total_elapsed_sec"] = round(time.time() - t0, 3)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Saved {args.out}")


if __name__ == "__main__":
    main()
