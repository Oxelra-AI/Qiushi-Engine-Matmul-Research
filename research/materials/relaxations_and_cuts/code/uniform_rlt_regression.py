#!/usr/bin/env python3
"""analysis regression: uniform first moments with uniform distinct-pair moments.

The uniform extension x_p=19/255, y_pq=19*18/(255*254) is PSD and satisfies
ordinary first-order Wang occupation.  It need not satisfy Wang RLT; cap-one rows
containing both p and q imply y_pq=0 for corresponding pair orbits.  This script
checks the raw analysis RLT model on that extension and records the violated row
statistics.
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import build_core_constraints
from rlt_pair_lift import (
    LUT_PATH,
    build_lp,
    build_stabilizer,
    compute_pair_orbits,
    compute_point_orbits,
    cap1_diagnostic,
)
from rlt_triangle_integrality import dense_rows_to_csr, build_triangle_constraints

OUT = ROOT / "workspace/data/uniform_regression"


def main():
    t0 = time.time()
    OUT.mkdir(parents=True, exist_ok=True)
    perms = build_stabilizer()
    pt_orb, orbits = compute_point_orbits(perms)
    pair_orb, pair_sizes, pair_ep, Mpair = compute_pair_orbits(perms, pt_orb)
    K = len(orbits)
    lut, _ = load_lut(LUT_PATH)
    records, meta = build_core_constraints(CoreQuotient(1), lut)
    cap1 = cap1_diagnostic(records, pair_orb, pt_orb, orbits, Mpair, pair_ep)
    eq_A, eq_b, ub_A, ub_b, K2, M2, N, n_aj = build_lp(records, pt_orb, orbits, pair_orb, Mpair, pair_ep)
    assert (K2, M2) == (K, Mpair)
    Aeq = dense_rows_to_csr(eq_A, N)
    Aub = dense_rows_to_csr(ub_A, N)
    beq = np.array(eq_b, dtype=float)
    bub = np.array(ub_b, dtype=float)

    z = np.zeros(N, dtype=float)
    z[:K] = 19.0 / 255.0
    z[K:] = (19.0 * 18.0) / (255.0 * 254.0)
    eq_res = Aeq @ z - beq
    ub_res = Aub @ z - bub
    viol_idx = np.flatnonzero(ub_res > 1e-10)
    # First-order Wang rows are inserted before the two RLT rows for each orbit rep,
    # but exact row provenance is not retained by build_lp; here we record only row-level
    # violation statistics and cap-1 diagnostic, not a theorem about which source row.
    top = []
    for idx in viol_idx[np.argsort(-ub_res[viol_idx])[:20]]:
        row = Aub.getrow(int(idx))
        top.append({
            "row_index": int(idx),
            "violation": float(ub_res[idx]),
            "nnz": int(row.nnz),
            "cols": [int(c) for c in row.indices[:20]],
            "coefs": [float(c) for c in row.data[:20]],
            "truncated": bool(row.nnz > 20),
        })
    # Add triangle rows separately and verify uniform extension still satisfies pure triangle constraints.
    Atri, btri, tri_meta = build_triangle_constraints(pt_orb, pair_orb, K, Mpair)
    tri_res = Atri @ z - btri
    result = {
        "schema": "uniform_rlt_regression_v1",
        "meaning": "Uniform first moments plus uniform distinct-pair moments are PSD and satisfy cardinality, but violate the complete-Wang conditioned RLT model; therefore analysis's continuous RLT+PSD feasibility inference from the uniform extension is withdrawn.",
        "elapsed_sec": round(time.time() - t0, 3),
        "point_orbit_sizes": [len(o) for o in orbits],
        "point_orbit_reps": [o[0] for o in orbits],
        "n_pair_orbits": Mpair,
        "uniform_x": 19.0 / 255.0,
        "uniform_y": (19.0 * 18.0) / (255.0 * 254.0),
        "eq_max_abs": float(np.max(np.abs(eq_res))) if eq_res.size else 0.0,
        "rlt_ub_count": int(Aub.shape[0]),
        "rlt_max_violation": float(max(0.0, np.max(ub_res))) if ub_res.size else 0.0,
        "rlt_violated_count_1e_10": int(len(viol_idx)),
        "rlt_top_violations": top,
        "triangle_meta": tri_meta,
        "triangle_max_violation": float(max(0.0, np.max(tri_res))) if tri_res.size else 0.0,
        "triangle_violated_count_1e_10": int(np.sum(tri_res > 1e-10)) if tri_res.size else 0,
        "cap1_diagnostic": cap1,
    }
    (OUT / "uniform_rlt_regression.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "rlt_max_violation": result["rlt_max_violation"],
        "rlt_violated_count_1e_10": result["rlt_violated_count_1e_10"],
        "triangle_max_violation": result["triangle_max_violation"],
        "out": str(OUT / "uniform_rlt_regression.json"),
    }, indent=2))

if __name__ == "__main__":
    main()
