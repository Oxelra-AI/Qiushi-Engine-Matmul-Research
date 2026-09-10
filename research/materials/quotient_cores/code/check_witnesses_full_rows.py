#!/usr/bin/env python3
"""analysis: check analysis integer pair witnesses against the full analysis rows.

analysis's pooled-square script omitted triangle/Fortet rows in Phase 3--5.
This script loads the stored Phase-3 integer m vectors and checks them exactly
against:
  (i) base Wang RLT rows,
  (ii) triangle/Fortet rows,
  (iii) the union used in analysis,
  (iv) fixed-n block-total equations.

It is a scope audit, not a tensor-rank proof.
"""
from __future__ import annotations

import ast
import json
import sys
import time
from collections import defaultdict
from pathlib import Path

import numpy as np
from scipy import sparse

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import build_core_constraints  # noqa: E402
from rlt_pair_lift import (  # noqa: E402
    LUT_PATH,
    build_lp,
    build_stabilizer,
    compute_pair_orbits,
    compute_point_orbits,
)
from rlt_triangle_integrality import (  # noqa: E402
    build_triangle_constraints,
    dense_rows_to_csr,
    exact_fraction_check,
)

OUT = ROOT / "workspace/data/scope_audit"


def block_total_check(n_vec, m_vec, pair_ep, K):
    by_block = defaultdict(list)
    for j, (a, b) in enumerate(pair_ep):
        by_block[(int(a), int(b))].append(j)
    rows = []
    max_abs = 0
    bad = []
    for a in range(K):
        lhs = sum(int(m_vec[j]) for j in by_block[(a, a)])
        rhs = int(n_vec[a] * (n_vec[a] - 1) // 2)
        diff = lhs - rhs
        rows.append({"block": [a, a], "lhs": lhs, "rhs": rhs, "diff": diff})
        max_abs = max(max_abs, abs(diff))
        if diff and len(bad) < 5:
            bad.append(rows[-1])
    for a in range(K):
        for b in range(a + 1, K):
            lhs = sum(int(m_vec[j]) for j in by_block[(a, b)])
            rhs = int(n_vec[a] * n_vec[b])
            diff = lhs - rhs
            rows.append({"block": [a, b], "lhs": lhs, "rhs": rhs, "diff": diff})
            max_abs = max(max_abs, abs(diff))
            if diff and len(bad) < 5:
                bad.append(rows[-1])
    return {"checked": True, "max_abs_diff": max_abs, "first_bad": bad[0] if bad else None, "bad_count": sum(1 for r in rows if r["diff"] != 0)}


def main():
    t0 = time.time()
    OUT.mkdir(parents=True, exist_ok=True)
    print("analysis: audit analysis Phase-3 witnesses against full analysis rows", flush=True)

    # Build the same orbit/RLT/triangle infrastructure used by earlier analysis.
    perms = build_stabilizer()
    pt_orb, point_orbits = compute_point_orbits(perms)
    pair_orb, pair_sizes, pair_ep, Mpair = compute_pair_orbits(perms, pt_orb)
    K = len(point_orbits)
    N = K + Mpair
    point_sizes = [len(o) for o in point_orbits]
    print(f"  orbits: K={K}, pair_orbits={Mpair}, point_sizes={point_sizes}", flush=True)

    lut, lut_meta = load_lut(LUT_PATH)
    records, wmeta = build_core_constraints(CoreQuotient(1), lut)
    eq_rows, eq_b, ub_rows, ub_b, K2, M2, N2, _ = build_lp(
        records, pt_orb, point_orbits, pair_orb, Mpair, pair_ep
    )
    assert (K2, M2, N2) == (K, Mpair, N)
    Aeq = dense_rows_to_csr(eq_rows, N)
    Aub = dense_rows_to_csr(ub_rows, N)
    beq = np.array(eq_b, dtype=float)
    bub = np.array(ub_b, dtype=float)
    Atri, btri, tri_meta = build_triangle_constraints(pt_orb, pair_orb, K, Mpair)
    Aub_all = sparse.vstack([Aub, Atri], format="csr")
    bub_all = np.concatenate([bub, btri])
    empty_eq = sparse.csr_matrix((0, N), dtype=float)
    empty_b = np.zeros(0, dtype=float)
    print(f"  rows: eq={Aeq.shape[0]}, RLT_ub={Aub.shape[0]}, tri={Atri.shape[0]}, all_ub={Aub_all.shape[0]}", flush=True)

    src = ROOT / "workspace/data/pooled_square_cuts/pooled_square_cuts_results.json"
    data = json.loads(src.read_text())
    phase3 = data.get("phase3_untested_results", {})
    results = []
    for key, rec in phase3.items():
        n_vec = list(ast.literal_eval(key))
        m_vec = rec.get("m_vec")
        if m_vec is None:
            continue
        print(f"  checking n={n_vec}", flush=True)
        base = exact_fraction_check(Aeq, beq, Aub, bub, n_vec, m_vec, point_sizes, [int(x) for x in pair_sizes], K, Mpair)
        tri = exact_fraction_check(empty_eq, empty_b, Atri, btri, n_vec, m_vec, point_sizes, [int(x) for x in pair_sizes], K, Mpair)
        full = exact_fraction_check(Aeq, beq, Aub_all, bub_all, n_vec, m_vec, point_sizes, [int(x) for x in pair_sizes], K, Mpair)
        block = block_total_check(n_vec, m_vec, pair_ep, K)
        out_rec = {
            "n": n_vec,
            "m_total": int(sum(m_vec)),
            "reported_status": rec.get("status"),
            "reported_min_eig": rec.get("min_eig"),
            "base_wang_rlt_exact": base,
            "triangle_exact": tri,
            "full_linear_exact": full,
            "block_totals_exact": block,
        }
        results.append(out_rec)
        print(
            "    base_ok={}; tri_viol={}; full_viol={}; block_bad={}".format(
                base.get("is_exact_feasible"), tri.get("violated_ub_count"), full.get("violated_ub_count"), block.get("bad_count")
            ),
            flush=True,
        )

    payload = {
        "schema": "scope_audit_v1",
        "meaning": "Exact audit of analysis stored Phase-3 integer pair-count witnesses. analysis omitted triangle/Fortet rows in its later CP-SAT phases; this file records whether the stored m-vectors satisfy the full analysis linear formulation.",
        "source_result": str(src),
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "wang_records": len(records),
        "linear_model": {"n_eq": int(Aeq.shape[0]), "n_ub_rlt": int(Aub.shape[0]), "n_ub_triangle": int(Atri.shape[0]), "n_ub_total": int(Aub_all.shape[0])},
        "triangle_meta": tri_meta,
        "results": results,
        "summary": {
            "checked_witnesses": len(results),
            "base_rlt_exact_feasible": sum(1 for r in results if r["base_wang_rlt_exact"].get("is_exact_feasible")),
            "triangle_exact_feasible": sum(1 for r in results if r["triangle_exact"].get("is_exact_feasible")),
            "full_exact_feasible": sum(1 for r in results if r["full_linear_exact"].get("is_exact_feasible")),
            "block_total_exact_feasible": sum(1 for r in results if r["block_totals_exact"].get("max_abs_diff") == 0),
        },
        "elapsed_sec": round(time.time() - t0, 3),
    }
    out_path = OUT / "phase3_full_audit.json"
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(out_path), **payload["summary"], "elapsed_sec": payload["elapsed_sec"]}, indent=2), flush=True)


if __name__ == "__main__":
    main()
