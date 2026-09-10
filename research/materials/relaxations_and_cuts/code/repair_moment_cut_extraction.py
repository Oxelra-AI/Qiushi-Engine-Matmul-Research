#!/usr/bin/env python3
"""Repair analysis moment-cut extraction on the saved analysis block witnesses.

This script is deliberately smaller than the global separation loop.  It checks
only the four exact integer count/pair witnesses from analysis and establishes:
  * their labelled moment matrices have negative spectra;
  * analysis's divided coefficient reconstruction is not the correct expression
    for normalized moment variables;
  * the undivided orbit-sum coefficients reconstruct v^T M v;
  * after rounding the negative eigenvector to an integer vector w, the square
    inequality w^T M w >= 0 evaluates to an exactly negative rational number on
    the saved witness.

The resulting JSON/JSONL are repair evidence, not a global lower-bound proof.
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

from rlt_pair_lift import build_stabilizer, compute_point_orbits, compute_pair_orbits
from global_psd_cut_loop import (
    make_pair_var_matrix,
    integerize_negative_direction,
    fixed_cut_for_float,
    old_divided_cut_for_float,
    exact_quad_for_counts,
    moment_kernel_residual,
)

OUT = ROOT / "workspace/data/moment_cut_repair"
WIT = ROOT / "workspace/data/invariant_pair_block/pair_block_triangles.json"


def build_matrix_from_counts(n_vec, m_vec, orbits, pair_var, pair_sizes, K, Mpair):
    sizes = [len(o) for o in orbits]
    z = np.zeros(K + Mpair, dtype=float)
    for a in range(K):
        z[a] = n_vec[a] / sizes[a]
    for j in range(Mpair):
        z[K+j] = m_vec[j] / pair_sizes[j]
    M = np.zeros((256, 256), dtype=float)
    M[0, 0] = 1.0
    for a, orb in enumerate(orbits):
        for p in orb:
            M[0, p] = M[p, 0] = z[a]
            M[p, p] = z[a]
    for p in range(1, 256):
        for q in range(p+1, 256):
            y = z[K + int(pair_var[p, q])]
            M[p, q] = M[q, p] = y
    return M, z


def main():
    t0 = time.time()
    OUT.mkdir(parents=True, exist_ok=True)
    print("analysis: repair moment-cut extraction")
    perms = build_stabilizer()
    pt_orb, orbits = compute_point_orbits(perms)
    pair_orb, pair_sizes, pair_ep, Mpair = compute_pair_orbits(perms, pt_orb)
    pair_var = make_pair_var_matrix(pair_orb)
    K = len(orbits)
    sizes = [len(o) for o in orbits]
    data = json.loads(WIT.read_text())
    records = []
    with (OUT / "integer_square_cuts.jsonl").open("w") as f:
        for rec in data["results"]:
            label = rec["label"]
            n_vec = rec["n_by_point_orbit"]
            m_vec = rec["m_by_pair_orbit"]
            M, z = build_matrix_from_counts(n_vec, m_vec, orbits, pair_var, pair_sizes, K, Mpair)
            eigvals, eigvecs = np.linalg.eigh(M)
            v = eigvecs[:, 0]
            c_old, x_old, y_old = old_divided_cut_for_float(v, orbits, pair_var, pair_sizes, K, Mpair)
            c_fix, x_fix, y_fix = fixed_cut_for_float(v, orbits, pair_var, K, Mpair)
            old_eval = float(c_old + x_old @ z[:K] + y_old @ z[K:])
            fix_eval = float(c_fix + x_fix @ z[:K] + y_fix @ z[K:])
            direct_eval = float(v @ M @ v)
            cut = integerize_negative_direction(v, z, orbits, pair_var, K, Mpair)
            exact = exact_quad_for_counts(cut["const"], np.array(cut["xcoef"], dtype=object),
                                          np.array(cut["ycoef"], dtype=object),
                                          n_vec, m_vec, sizes, pair_sizes)
            short = {
                "label": label,
                "n_by_point_orbit": n_vec,
                "m_total": rec.get("m_total"),
                "min_eigenvalue": float(eigvals[0]),
                "negative_eigenvalues_1e-10": int(np.sum(eigvals < -1e-10)),
                "direct_float_vMv": direct_eval,
                "old_divided_reconstruction_against_normalized_moments": old_eval,
                "correct_undivided_reconstruction": fix_eval,
                "abs_error_correct_vs_direct": abs(fix_eval - direct_eval),
                "abs_error_old_vs_direct": abs(old_eval - direct_eval),
                "integer_cut_float_quad": cut["float_quad_on_current_z"],
                "integer_cut_exact_quad": str(exact),
                "integer_cut_exact_quad_float": float(exact),
                "integer_cut_exact_negative": bool(exact < 0),
                "integer_cut_nonzero_w": cut["nonzero_w"],
                "integer_cut_max_abs_w": cut["max_abs_w"],
                "kernel_residual": moment_kernel_residual(M),
            }
            records.append(short)
            f.write(json.dumps({**short, "cut": cut}, sort_keys=True) + "\n")
            print(label, "min_eig", short["min_eigenvalue"], "old", old_eval, "fixed", fix_eval,
                  "exact integer", str(exact))
    summary = {
        "schema": "moment_cut_repair_v1",
        "meaning": "Repairs analysis PSD cut coefficient normalization for the four analysis block witnesses. Coefficients for normalized moment variables x_a,y_j are undivided orbit sums; divided coefficients belong to count variables.",
        "elapsed_sec": round(time.time() - t0, 3),
        "point_orbit_sizes": sizes,
        "n_pair_orbits": Mpair,
        "records": records,
        "all_exact_integer_cuts_negative": all(r["integer_cut_exact_negative"] for r in records),
        "full_integer_cuts_jsonl": str(OUT / "integer_square_cuts.jsonl"),
    }
    (OUT / "moment_cut_repair_summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "all_exact_integer_cuts_negative": summary["all_exact_integer_cuts_negative"],
        "out": str(OUT / "moment_cut_repair_summary.json"),
        "elapsed_sec": summary["elapsed_sec"],
    }, indent=2))


if __name__ == "__main__":
    main()
