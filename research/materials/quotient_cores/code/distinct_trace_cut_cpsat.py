#!/usr/bin/env python3
r"""analysis: distinct E11-core support search with sound trace-dependency cuts.

This is a support-level search for the remaining distinct rank-19 E11 quotient
core branch over F2.  It keeps the 255 point variables.  The six analysis point
orbits are NOT collapsed to six count variables.  Optional symmetry breaking is
implemented only as whole-support lexicographic constraints under actual E11
stabilizer permutations, so the same group element acts on every selected point.

New trace-dependency cuts are the analysis sound linear implications:
    sum_{q in H} (w(q)-9) >= x_p,
where H is an odd dependency among corrected rank-9 trace functionals and
q(p)=1 for every q in H.  These cuts forbid selecting p while all contractions
in H are exactly saturated.  They are necessary B/C compatibility restrictions,
not complete rank-one completion and not a tensor-rank lower bound by themselves.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Sequence

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
from orbit_structure import bit8_to_mat3x3, gl3f2_elements, mat3x3_to_8bit, apply_conj  # noqa: E402
from trace_dependency_family import dot8, eval_support_local_dependency, min_odd_dependency, trace_mask_correct  # noqa: E402
from dual_basis_instrument import gf2_mat_inv  # noqa: E402
from fixed_A_saturation import contraction_matrix, mat_rank_f2  # noqa: E402
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis  # noqa: E402

OUTDIR = ROOT / "workspace/data/trace_dependency_cuts"
ALLMASK = (1 << 255) - 1


def load_lut(path: Path):
    with path.open("rb") as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload["lut"].items()}, payload.get("meta", {})


def load_hint(path: Path | None, round_index: int | None):
    if path is None or not path.exists():
        return None
    d = json.loads(path.read_text())
    rounds = d.get("rounds", [])
    if not rounds and "best_analyses" in d:
        rounds = d.get("best_analyses", [])
    if round_index is None:
        best = None
        for r in rounds:
            A = r.get("support") or r.get("A_cols")
            if not A or len(A) != 19 or len(set(A)) != 19:
                continue
            val = r.get("complete_wang_violations", 10**9)
            if best is None or val < best[0]:
                best = (val, A)
        return None if best is None else [int(x) for x in best[1]]
    for r in rounds:
        if r.get("round") == round_index:
            A = r.get("support") or r.get("A_cols")
            return None if not A else [int(x) for x in A]
    return None


def generate_stabilizer_permutations(include_transpose: bool = True) -> List[List[int]]:
    """Return deduplicated point maps perm[p]=g(p), p=0..255, perm[0]=0."""
    gl3 = gl3f2_elements()
    e1 = np.array([1, 0, 0], dtype=np.uint8)
    Ps = [P for P in gl3 if np.array_equal(P[:, 0] % 2, e1)]
    Qs = [Q for Q in gl3 if np.array_equal(Q[:, 0] % 2, e1)]
    maps = {}
    for P in Ps:
        for Q in Qs:
            for tr in ([False, True] if include_transpose else [False]):
                perm = [0] * 256
                ok = True
                for p in range(1, 256):
                    X = bit8_to_mat3x3(p)
                    if tr:
                        X = X.T.copy()
                    img = apply_conj(P, Q, X)
                    ip = mat3x3_to_8bit(img)
                    if ip == 0:
                        ok = False
                        break
                    perm[p] = int(ip)
                if ok:
                    maps[tuple(perm)] = perm
    return list(maps.values())


def add_lex_leq(model, xs: Sequence, perm: Sequence[int], points: Sequence[int], name: str) -> int:
    """Enforce whole vector x <=_lex perm(x); returns aux var count.

    Coordinates are ordered by `points`; y_i is x_{perm[p_i]}.  This is a
    whole-support condition under one group element, not independent orbit
    canonicalization.
    """
    aux = 0
    point_index = {p: i for i, p in enumerate(points)}
    pref = model.NewBoolVar(f"{name}_pref0")
    aux += 1
    model.Add(pref == 1)
    n = len(points)
    for i, p in enumerate(points):
        j = point_index[int(perm[p])]
        a = xs[i]
        b = xs[j]
        if j != i:
            # If previous coordinates are equal and x_i=1, then y_i must be 1.
            model.AddBoolOr([pref.Not(), a.Not(), b])
        if i == n - 1:
            break
        if j == i:
            # Equality at this coordinate is automatic; prefix carries forward.
            nxt = pref
        else:
            eq = model.NewBoolVar(f"{name}_eq{i}")
            aux += 1
            model.Add(a == b).OnlyEnforceIf(eq)
            model.Add(a + b == 1).OnlyEnforceIf(eq.Not())
            nxt = model.NewBoolVar(f"{name}_pref{i+1}")
            aux += 1
            model.AddImplication(nxt, pref)
            model.AddImplication(nxt, eq)
            model.AddBoolOr([pref.Not(), eq.Not(), nxt])
        pref = nxt
    return aux


def load_trace_cuts(mode: str, cut_path: Path, size5_path: Path, max_size5: int | None) -> List[dict]:
    if mode == "none":
        return []
    if mode == "minimal":
        data = json.loads(cut_path.read_text())
        return list(data.get("minimal_cuts", []))
    if mode == "size5":
        with size5_path.open("rb") as f:
            data = pickle.load(f)
        cuts = []
        for p, hs in data["cuts_by_p"].items():
            for H in hs:
                cuts.append({"p": int(p), "H": [int(q) for q in H], "size": len(H)})
                if max_size5 is not None and len(cuts) >= max_size5:
                    return cuts
        return cuts
    raise ValueError(mode)


def build_phi(T_core: np.ndarray) -> Dict[int, int]:
    phi = {}
    for q in range(1, 1 << 8):
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) == 9:
            M_inv = gf2_mat_inv(M)
            if M_inv is None:
                raise RuntimeError(q)
            phi[q] = trace_mask_correct(M_inv)
    return phi


def main() -> None:
    from ortools.sat.python import cp_model

    ap = argparse.ArgumentParser()
    ap.add_argument("--solver-time", type=float, default=300.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=5353)
    ap.add_argument("--min-L", type=int, default=0, help="Only include Wang rows with L>=min-L; 0 means complete table rows")
    ap.add_argument("--trace-cuts", choices=["none", "minimal", "size5"], default="none")
    ap.add_argument("--max-size5-cuts", type=int, default=None)
    ap.add_argument("--lex-symmetry", choices=["none", "sample", "all"], default="none")
    ap.add_argument("--lex-map-limit", type=int, default=64)
    ap.add_argument("--hint-source", type=Path, default=ROOT / "workspace/data/review/summary.json")
    ap.add_argument("--hint-round", type=int, default=None)
    ap.add_argument("--out", type=Path, default=OUTDIR / "distinct_trace_cut_cpsat.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    s = 19
    points = list(range(1, 256))
    core = CoreQuotient(1)
    lut, lut_meta = load_lut(ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl")
    records, meta = build_core_constraints(core, lut)
    T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
    contractions = build_contractions(T_core)
    masks = {q: point_mask_for_q(q) for q in contractions}

    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in points}
    model.Add(sum(x[p] for p in points) == s)

    # Reusable contraction weights w(q).
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

    # Complete or threshold Wang rows.
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
        if not pts:
            continue
        model.Add(sum(x[p] for p in pts) <= cap)
        wang_count += 1
        dim_counts[int(rec["dim8"])] += 1

    # Sound trace-dependency cuts.
    cut_path = OUTDIR / "trace_dependency_cuts.json"
    size5_path = OUTDIR / "trace_dependency_size5_cuts.pkl"
    cuts = load_trace_cuts(args.trace_cuts, cut_path, size5_path, args.max_size5_cuts)
    trace_cut_count = 0
    trace_cut_size_hist = Counter()
    for cut in cuts:
        p = int(cut["p"])
        H = [int(q) for q in cut["H"]]
        # sum(w(q)-9) >= x_p  <=> sum w(q) >= 9|H| + x_p.
        model.Add(sum(w[q] for q in H) >= 9 * len(H) + x[p])
        trace_cut_count += 1
        trace_cut_size_hist[len(H)] += 1

    # Optional whole-support lex constraints under genuine stabilizer maps.
    lex_maps_used = 0
    lex_aux = 0
    if args.lex_symmetry != "none":
        perms = generate_stabilizer_permutations(include_transpose=True)
        identity = tuple(range(256))
        perms = [p for p in perms if tuple(p) != identity]
        perms.sort(key=lambda perm: [perm[i] for i in points])
        if args.lex_symmetry == "sample":
            perms = perms[: max(0, int(args.lex_map_limit))]
        xs = [x[p] for p in points]
        for k, perm in enumerate(perms):
            lex_aux += add_lex_leq(model, xs, perm, points, f"lex{k}")
        lex_maps_used = len(perms)

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
        "trace_cuts": trace_cut_count,
        "trace_cut_size_hist": {str(k): int(v) for k, v in sorted(trace_cut_size_hist.items())},
        "lex_maps_used": lex_maps_used,
        "lex_aux_vars": lex_aux,
        "hint_added": hint_added,
    }, indent=2, sort_keys=True))

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(args.solver_time)
    solver.parameters.num_search_workers = int(args.workers)
    solver.parameters.random_seed = int(args.seed)
    # Keep logs off by default; returned stdout is enough for this ARTIFACT.
    ts = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - ts
    status_name = solver.StatusName(status)
    print(f"status={status_name} solve_sec={solve_sec:.3f}")

    result = {
        "schema": "distinct_trace_cut_cpsat_v1",
        "field": "F2",
        "core": "E11 quotient core",
        "rank_s": s,
        "meaning": "255-variable distinct A-support model with complete/threshold Wang rows, contraction lower bounds, optional sound trace-dependency cuts, and optional whole-support lex symmetry. FEASIBLE is only an A-support candidate needing B/C completion; INFEASIBLE still needs proof-producing replay.",
        "parameters": {
            "solver_time": args.solver_time,
            "workers": args.workers,
            "seed": args.seed,
            "min_L": args.min_L,
            "trace_cuts": args.trace_cuts,
            "max_size5_cuts": args.max_size5_cuts,
            "lex_symmetry": args.lex_symmetry,
            "lex_map_limit": args.lex_map_limit,
        },
        "constraint_summary": {
            "wang_rows": wang_count,
            "wang_by_dim": {str(k): int(v) for k, v in sorted(dim_counts.items())},
            "skipped_by_minL": skipped_by_minL,
            "contraction_weight_definitions": len(w),
            "contraction_lower_bounds": contraction_lb,
            "trace_dependency_cuts": trace_cut_count,
            "trace_cut_size_hist": {str(k): int(v) for k, v in sorted(trace_cut_size_hist.items())},
            "lex_maps_used": lex_maps_used,
            "lex_aux_vars": lex_aux,
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
        scan = complete_core_wang_scan("solution", A, s, records, max_head=30)
        sat = saturation_domains(T_core, A)
        trans = transversal_failures(sat["sat_records"], sat["B_domains"], sat["C_domains"], 9, 9, max_report=10)
        qscan = eval_candidate_sources("solution", A, contractions, masks, max_source_size=2, max_store=20)
        phi = build_phi(T_core)
        trace_dep = eval_support_local_dependency(A, sorted(phi), phi, {p: None for p in points})
        weights = {q: solver.Value(w[q]) for q in sorted(w)}
        result["solution"] = {
            "A_cols": A,
            "distinct_points": len(A),
            "complete_wang_violations": scan["complete_violation_count"],
            "complete_wang_max_excess": scan.get("max_excess"),
            "zero_domain_terms": len(sat["summary"]["zero_domain_terms"]),
            "linear_pass": sat["summary"]["linear_membership"]["necessary_linear_test_passed"],
            "affine_dim": sat["summary"]["linear_membership"].get("affine_solution_dimension_if_consistent"),
            "transversal_failures": trans["failure_count_reported"],
            "quotient_rank_violations_size2": qscan["violated_guarded_instances"],
            "trace_local_dependency": trace_dep,
            "rank9_weight_hist": {str(k): int(v) for k, v in sorted(Counter(weights[q] for q in weights if int(contractions[q]["rank"]) == 9).items())},
        }
        print("A_cols=", A)
        print("solution_checks=", json.dumps(result["solution"], indent=2, sort_keys=True)[:4000])

    result["total_elapsed_sec"] = round(time.time() - t0, 3)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Saved {args.out}")


if __name__ == "__main__":
    main()
