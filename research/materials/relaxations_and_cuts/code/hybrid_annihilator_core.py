#!/usr/bin/env python3
r"""analysis: hybrid Wang/annihilator-weight encoding for the E11 core.

For a subspace U <= F2^8 in the E11 quotient core let D=U^perp.
For a distinct length-19 support x_p and contraction weights

    w(q) = sum_{p: <q,p>=1} x_p,

we have

    sum_{q in D\{0}} w(q) = 2^(dim(D)-1) * (19 - sum_{p in U\{0}} x_p).

Thus the Wang occupation row sum_U x_p <= 19-L(U) is equivalently

    sum_{q in D\{0}} w(q) >= 2^(dim(D)-1) L(U),

provided total sum_p x_p = 19 and w is linked to the same support variables.
This script checks that identity on current near-miss supports and builds a
CP-SAT feasibility model that uses direct point rows for small U and the exact
annihilator-weight rows for large U.  The representation is exact for the
encoded Wang rows; solver statuses are computational evidence only unless a
proof object is later produced.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

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
from quotient_rank_cuts import build_contractions, point_mask_for_q  # noqa: E402
from candidate_source_qcut_scan import eval_candidate_sources  # noqa: E402
from wang_capacity_lazy import pack_basis, rref_basis, subspace_points_from_basis, unpack_basis  # noqa: E402

OUTDIR = ROOT / "workspace/data/hybrid_annihilator"
ALL_POINTS = list(range(1, 256))
ALLMASK = (1 << 255) - 1
S = 19


def load_lut(path: Path) -> Tuple[Dict[int, int], dict]:
    with path.open("rb") as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload["lut"].items()}, payload.get("meta", {})


def bitset_points(bitset: int) -> List[int]:
    return [i + 1 for i in range(255) if (int(bitset) >> i) & 1]


def parity_dot(q: int, p: int) -> int:
    return (int(q) & int(p)).bit_count() & 1


def annihilator_points(basis: Sequence[int], n: int = 8) -> List[int]:
    """Return all nonzero q in (F2^n)^* annihilating the rowspace basis."""
    bs = [int(b) for b in basis]
    return [q for q in range(1, 1 << n) if all(parity_dot(q, u) == 0 for u in bs)]


def annihilator_key_from_basis(basis: Sequence[int], n: int = 8) -> int:
    return pack_basis(rref_basis(annihilator_points(basis, n), n=n))


def weight_counts(A: Sequence[int]) -> Dict[int, int]:
    return {q: sum(1 for p in A if parity_dot(q, p)) for q in ALL_POINTS}


def load_hints() -> List[List[int]]:
    paths = [
        ROOT / "workspace/data/distinct_line_cover/threshold_L15_300s.json",
        ROOT / "workspace/data/distinct_line_cover/threshold_L17_180s.json",
        ROOT / "workspace/data/unconditional_qcuts/fresh_uncond_sep_10r.json",
        ROOT / "workspace/data/unconditional_qcuts/fresh_uncond_sep_50r.json",
        ROOT / "workspace/data/core_complete_transversal/core_e11_saturation_v3_complete_long.json",
    ]
    hints: List[List[int]] = []
    seen = set()
    for path in paths:
        if not path.exists():
            continue
        d = json.loads(path.read_text())
        containers = []
        if isinstance(d.get("solutions"), list):
            containers.extend(d["solutions"])
        if isinstance(d.get("rounds"), list):
            containers.extend(d["rounds"])
        for r in containers:
            A = r.get("A_cols") or r.get("support")
            if not A or len(A) != S or len(set(A)) != S:
                continue
            key = tuple(int(x) for x in A)
            if key not in seen:
                seen.add(key)
                hints.append(list(key))
    return hints


def choose_hint(records: Sequence[dict]) -> List[int] | None:
    hints = load_hints()
    if not hints:
        return None
    scored = []
    for A in hints:
        scan = complete_core_wang_scan("hint", A, S, records, max_head=1)
        scored.append((int(scan["complete_violation_count"]), A))
    scored.sort(key=lambda t: t[0])
    return scored[0][1]


def analyze_support(label: str, A: List[int], records: Sequence[dict], T: np.ndarray, contractions: Dict[int, dict], masks: Dict[int, int], max_head: int = 80) -> dict:
    scan = complete_core_wang_scan(label, A, S, records, max_head=max_head)
    sat = saturation_domains(T, A)
    trans = transversal_failures(sat["sat_records"], sat["B_domains"], sat["C_domains"], 9, 9, max_report=20)
    qscan = eval_candidate_sources(label, A, contractions, masks, max_source_size=2, max_store=20)
    return {
        "label": label,
        "A_cols": A,
        "complete_wang_violations": scan["complete_violation_count"],
        "max_excess": scan["max_excess"],
        "violations_by_dim8": scan["violations_by_dim8"],
        "violations_by_L": scan["violations_by_full_lut_L"],
        "violations_head": scan["violations_head"],
        "zero_domain_terms": len(sat["summary"]["zero_domain_terms"]),
        "linear_pass": sat["summary"]["linear_membership"]["necessary_linear_test_passed"],
        "affine_dim": sat["summary"]["linear_membership"].get("affine_solution_dimension_if_consistent"),
        "saturated_contractions": sat["summary"]["saturated_contraction_count"],
        "transversal_failures": trans["failure_count_reported"],
        "quotient_rank_violations_size2": qscan["violated_guarded_instances"],
    }


def support_from_args(args) -> List[int] | None:
    if args.support:
        vals = [int(x) for x in args.support.replace(",", " ").split()]
        if len(vals) != S or len(set(vals)) != S:
            raise ValueError("--support must give 19 distinct core point labels")
        return vals
    if args.support_json:
        d = json.loads(args.support_json.read_text())
        if "A_cols" in d:
            return [int(x) for x in d["A_cols"]]
        if d.get("solutions"):
            idx = int(args.support_index)
            return [int(x) for x in d["solutions"][idx]["A_cols"]]
        if d.get("rounds"):
            idx = int(args.support_index)
            r = d["rounds"][idx]
            return [int(x) for x in (r.get("support") or r.get("A_cols"))]
    return None


def analyze_annihilator_identity(A: List[int], records: Sequence[dict], contractions: Dict[int, dict], max_store: int = 80) -> dict:
    """Check the exact U/D identity and explain the violating high-codimension rows."""
    weights = weight_counts(A)
    support_bitset = 0
    for p in A:
        support_bitset |= 1 << (p - 1)

    identity_failures = []
    violation_details = []
    dual_dim_hist = Counter()
    repr_savings_by_dim = defaultdict(lambda: {"rows": 0, "direct_terms": 0, "ann_terms": 0})
    all_by_dim_L = Counter()
    selected_violation_D_keys_by_dim = defaultdict(list)

    for rec in records:
        d = int(rec["dim8"])
        L = int(rec["L"])
        pts_bitset = int(rec["point_bitset"])
        occ = (pts_bitset & support_bitset).bit_count()
        cap = S - L
        basis = unpack_basis(int(rec["key8"]))
        D = annihilator_points(basis, 8)
        k = 8 - d
        all_by_dim_L[(d, L)] += 1
        direct_terms = int(rec["point_count"])
        ann_terms = len(D)
        repr_savings_by_dim[d]["rows"] += 1
        repr_savings_by_dim[d]["direct_terms"] += direct_terms
        repr_savings_by_dim[d]["ann_terms"] += ann_terms
        if k > 0:
            lhs = sum(weights[q] for q in D)
            rhs_identity = (1 << (k - 1)) * (S - occ)
            req = (1 << (k - 1)) * L
            if lhs != rhs_identity:
                identity_failures.append({
                    "key8": int(rec["key8"]), "dim8": d, "L": L,
                    "lhs_sum_weights": lhs, "rhs_count_identity": rhs_identity,
                    "occ": occ, "D": D[:20],
                })
        else:
            lhs = 0
            req = 0
        if occ > cap:
            dual_dim_hist[k] += 1
            D_basis = rref_basis(D, n=8)
            D_key = pack_basis(D_basis)
            selected_violation_D_keys_by_dim[d].append(D_key)
            if len(violation_details) < max_store:
                q_weights = [{
                    "q": int(q),
                    "w": int(weights[q]),
                    "rank_Lq": int(contractions[q]["rank"]),
                    "B_dim": len(contractions[q]["B_space"]),
                    "C_dim": len(contractions[q]["C_space"]),
                } for q in D]
                violation_details.append({
                    "key8": int(rec["key8"]),
                    "basis8": list(basis),
                    "dim8": d,
                    "codim_dual_k": k,
                    "key9": int(rec["key9"]),
                    "L": L,
                    "cap": cap,
                    "occupancy": occ,
                    "outside_count": S - occ,
                    "excess": occ - cap,
                    "D_basis": list(D_basis),
                    "D_key": D_key,
                    "D_nonzero": D,
                    "annihilator_weight_sum": int(lhs),
                    "annihilator_requirement": int(req),
                    "annihilator_deficit": int(req - lhs),
                    "q_weights": q_weights,
                    "sum_individual_contraction_ranks": int(sum(contractions[q]["rank"] for q in D)),
                })

    # Incidence among the violating annihilators: a dim-6 occupation violation has a 2D D;
    # a dim-5 violation has a 3D D.  Record containments to see whether the twelve rows
    # are shadows of fewer dual pencils.
    containments = []
    dim6_keys = selected_violation_D_keys_by_dim.get(6, [])
    dim5_keys = selected_violation_D_keys_by_dim.get(5, [])
    dim6_sets = {key: set(subspace_points_from_basis(unpack_basis(key))) for key in dim6_keys}
    dim5_sets = {key: set(subspace_points_from_basis(unpack_basis(key))) for key in dim5_keys}
    for key5, set5 in dim5_sets.items():
        contained = [int(key6) for key6, set6 in dim6_sets.items() if set6.issubset(set5)]
        containments.append({
            "dim5_D_key": int(key5),
            "dim5_D_basis": list(unpack_basis(key5)),
            "contained_dim6_violation_D_keys": contained,
            "contained_count": len(contained),
        })

    by_dim_summary = {
        str(d): {
            "rows": int(v["rows"]),
            "direct_point_terms_total": int(v["direct_terms"]),
            "annihilator_weight_terms_total": int(v["ann_terms"]),
            "average_direct_terms": float(v["direct_terms"] / v["rows"]) if v["rows"] else 0.0,
            "average_annihilator_terms": float(v["ann_terms"] / v["rows"]) if v["rows"] else 0.0,
        }
        for d, v in sorted(repr_savings_by_dim.items())
    }
    return {
        "schema": "annihilator_identity_analysis_v1",
        "field": "F2",
        "core": "E11",
        "rank_s": S,
        "support": A,
        "support_size": len(A),
        "identity_checked_over_rows": len(records),
        "identity_failure_count": len(identity_failures),
        "identity_failures_head": identity_failures[:10],
        "explanation": "For each U, D=U^perp and sum_{q in D nonzero} w(q)=2^(dim(D)-1)*(19-occ(U)); Wang occ(U)<=19-L(U) becomes the displayed annihilator-weight lower bound. The check ties every weight to the same Boolean support.",
        "violating_rows_stored": len(violation_details),
        "violating_rows_by_dual_dimension": {str(k): int(v) for k, v in sorted(dual_dim_hist.items())},
        "violations": violation_details,
        "violation_D_containments": containments,
        "row_L_distribution_by_dim_head": {f"dim{d}_L{L}": int(v) for (d, L), v in sorted(all_by_dim_L.items())[:80]},
        "representation_term_summary_by_dim": by_dim_summary,
    }


def build_and_solve(args, records: Sequence[dict], T: np.ndarray, contractions: Dict[int, dict], masks: Dict[int, int]) -> dict:
    from ortools.sat.python import cp_model

    t0 = time.time()
    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in ALL_POINTS}
    model.Add(sum(x[p] for p in ALL_POINTS) == S)

    w = {}
    weight_equalities = 0
    if args.mode in ("hybrid", "annihilator"):
        for q in ALL_POINTS:
            w[q] = model.NewIntVar(0, S, f"w_{q}")
            model.Add(w[q] == sum(x[p] for p in ALL_POINTS if parity_dot(q, p)))
            weight_equalities += 1

    row_stats = Counter()
    row_stats_dim = Counter()
    row_stats_L = Counter()
    direct_point_terms = 0
    ann_weight_terms = 0
    wang_rows = 0
    skipped_rows = 0
    stored_examples = []

    for rec in records:
        L = int(rec["L"])
        if L < int(args.threshold_L):
            continue
        cap = S - L
        if cap >= S:
            skipped_rows += 1
            continue
        d = int(rec["dim8"])
        pts = bitset_points(int(rec["point_bitset"]))
        if not pts and cap >= 0:
            skipped_rows += 1
            continue
        use_ann = False
        if args.mode == "annihilator":
            use_ann = (8 - d) > 0
        elif args.mode == "hybrid":
            direct_n = len(pts)
            ann_n = (1 << (8 - d)) - 1 if d < 8 else 10**9
            use_ann = (d >= int(args.annihilator_dim_min)) and ann_n < direct_n
        elif args.mode == "direct":
            use_ann = False
        else:
            raise ValueError(args.mode)

        if use_ann:
            basis = unpack_basis(int(rec["key8"]))
            D = annihilator_points(basis, 8)
            k = 8 - d
            if k <= 0 or not D:
                skipped_rows += 1
                continue
            req = (1 << (k - 1)) * L
            model.Add(sum(w[q] for q in D) >= req)
            row_stats["annihilator"] += 1
            ann_weight_terms += len(D)
            if len(stored_examples) < 20 and (d >= 5 or L <= 12):
                stored_examples.append({
                    "repr": "annihilator",
                    "dim8": d,
                    "L": L,
                    "D_basis": list(rref_basis(D, n=8)),
                    "D_nonzero": D,
                    "rhs": req,
                    "ann_terms": len(D),
                    "direct_point_terms": len(pts),
                })
        else:
            model.Add(sum(x[p] for p in pts) <= cap)
            row_stats["direct"] += 1
            direct_point_terms += len(pts)
        wang_rows += 1
        row_stats_dim[d] += 1
        row_stats_L[L] += 1

    clb = 0
    if args.add_contraction_lower_bounds:
        if args.mode in ("hybrid", "annihilator"):
            for q, c in contractions.items():
                rk = int(c["rank"])
                if rk > 0:
                    model.Add(w[q] >= rk)
                    clb += 1
        else:
            for q, c in contractions.items():
                rk = int(c["rank"])
                if rk > 0:
                    model.Add(sum(x[p] for p in ALL_POINTS if parity_dot(q, p)) >= rk)
                    clb += 1

    hint = choose_hint(records) if args.use_hint else None
    hint_added = False
    if hint:
        hs = set(hint)
        for p in ALL_POINTS:
            model.AddHint(x[p], 1 if p in hs else 0)
        hint_added = True

    build_sec = time.time() - t0
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(args.solver_time)
    solver.parameters.num_search_workers = int(args.workers)
    solver.parameters.random_seed = int(args.seed)

    statuses = []
    solutions = []
    for it in range(int(args.enumerate)):
        ts = time.time()
        status = solver.Solve(model)
        sec = time.time() - ts
        status_name = solver.StatusName(status)
        statuses.append({"iteration": it, "status": status_name, "solve_sec": round(sec, 3)})
        print(f"iter {it} status={status_name} sec={sec:.2f}")
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            break
        A = [p for p in ALL_POINTS if solver.Value(x[p])]
        analysis = analyze_support(f"{args.mode}_L{args.threshold_L}_solution_{it}", A, records, T, contractions, masks, max_head=30)
        if args.mode in ("hybrid", "annihilator"):
            # Check solver's weight variables against recomputation for this support.
            recomputed = weight_counts(A)
            bad = [q for q in ALL_POINTS if solver.Value(w[q]) != recomputed[q]]
            analysis["weight_link_mismatch_count"] = len(bad)
            analysis["weight_link_mismatch_head"] = bad[:10]
        solutions.append(analysis)
        print("  A=", A)
        print("  Wang", analysis["complete_wang_violations"], "byL", analysis["violations_by_L"], "zero", analysis["zero_domain_terms"], "lin", analysis["linear_pass"], "trans", analysis["transversal_failures"], "q2", analysis["quotient_rank_violations_size2"])
        model.Add(sum(x[p] for p in A) <= S - 1)

    return {
        "schema": "hybrid_annihilator_cpsat_v1",
        "field": "F2",
        "core": "E11",
        "rank_s": S,
        "mode": args.mode,
        "threshold_L": int(args.threshold_L),
        "annihilator_dim_min": int(args.annihilator_dim_min),
        "add_contraction_lower_bounds": bool(args.add_contraction_lower_bounds),
        "meaning": "Exact CP-SAT representation of the selected Wang rows: direct point rows for small subspaces and annihilator-weight lower bounds for large subspaces, with every w(q) linked to the same support variables. FEASIBLE gives only an A-support candidate; UNKNOWN is not a mathematical result.",
        "constraint_summary": {
            "x_bool_variables": len(ALL_POINTS),
            "weight_variables": len(w),
            "weight_equalities": weight_equalities,
            "wang_rows_encoded": wang_rows,
            "wang_rows_skipped": skipped_rows,
            "wang_row_representation": {str(k): int(v) for k, v in sorted(row_stats.items())},
            "wang_rows_by_dim8": {str(k): int(v) for k, v in sorted(row_stats_dim.items())},
            "wang_rows_by_L": {str(k): int(v) for k, v in sorted(row_stats_L.items())},
            "direct_point_terms_total": int(direct_point_terms),
            "annihilator_weight_terms_total": int(ann_weight_terms),
            "contraction_lower_bounds": clb,
        },
        "representation_examples": stored_examples,
        "model_stats": model.ModelStats(),
        "build_sec": round(build_sec, 3),
        "solver": "OR-Tools CP-SAT",
        "solver_time_limit": float(args.solver_time),
        "workers": int(args.workers),
        "seed": int(args.seed),
        "use_hint": bool(args.use_hint),
        "hint_added": hint_added,
        "statuses": statuses,
        "solutions": solutions,
        "response_stats_last": solver.ResponseStats() if statuses else None,
        "elapsed_sec": round(time.time() - t0, 3),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["direct", "hybrid", "annihilator"], default="hybrid")
    ap.add_argument("--threshold-L", type=int, default=14)
    ap.add_argument("--annihilator-dim-min", type=int, default=5)
    ap.add_argument("--solver-time", type=float, default=300.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=4901)
    ap.add_argument("--enumerate", type=int, default=1)
    ap.add_argument("--add-contraction-lower-bounds", action="store_true", default=True)
    ap.add_argument("--no-contraction-lower-bounds", dest="add_contraction_lower_bounds", action="store_false")
    ap.add_argument("--use-hint", action="store_true", default=True)
    ap.add_argument("--no-hint", dest="use_hint", action="store_false")
    ap.add_argument("--support", type=str, default=None, help="comma/space separated 19-point support for analysis")
    ap.add_argument("--support-json", type=Path, default=None)
    ap.add_argument("--support-index", type=int, default=0)
    ap.add_argument("--analyze-only", action="store_true")
    ap.add_argument("--out", type=Path, default=OUTDIR / "hybrid_L14_300s.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

    t0 = time.time()
    lut, _ = load_lut(ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl")
    core = CoreQuotient(1)
    records, meta = build_core_constraints(core, lut)
    T = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
    contractions = build_contractions(T)
    masks = {q: point_mask_for_q(q) for q in contractions}
    load_sec = time.time() - t0

    support = support_from_args(args)
    if args.analyze_only or support is not None:
        if support is None:
            support = choose_hint(records)
            if support is None:
                raise RuntimeError("no support supplied and no hint available")
        scan = analyze_support("annihilator_analysis_support", support, records, T, contractions, masks, max_head=80)
        ann = analyze_annihilator_identity(support, records, contractions, max_store=80)
        out = {
            "schema": "hybrid_annihilator_analysis_bundle_v1",
            "load_sec": round(load_sec, 3),
            "complete_core_table_meta": meta,
            "support_analysis": scan,
            "annihilator_identity_analysis": ann,
        }
    else:
        out = build_and_solve(args, records, T, contractions, masks)
        out["load_sec"] = round(load_sec, 3)
        out["complete_core_table_meta"] = meta

    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(args.out),
        "schema": out.get("schema"),
        "mode": out.get("mode"),
        "threshold_L": out.get("threshold_L"),
        "statuses": out.get("statuses"),
        "support_violations": out.get("support_analysis", {}).get("complete_wang_violations"),
        "identity_failures": out.get("annihilator_identity_analysis", {}).get("identity_failure_count"),
        "elapsed_sec": out.get("elapsed_sec", round(time.time() - t0, 3)),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
