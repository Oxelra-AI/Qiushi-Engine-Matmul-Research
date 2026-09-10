#!/usr/bin/env python3
"""analysis: preflight data for a conic-guided integer pair-count pilot.

This does not solve the mixed integer SDP. It checks the analysis block
separation on the actual coefficient matrices and records the fixed-count
face reduction data for n=[0,0,3,5,4,7].
"""
from __future__ import annotations

import json
import sys
import time
from collections import Counter, defaultdict
from math import comb
from pathlib import Path

import numpy as np
from scipy.linalg import eigh

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from rlt_pair_lift import build_stabilizer, compute_pair_orbits, compute_point_orbits  # noqa: E402
from block_sdp_v2 import (  # noqa: E402
    build_full_moment_matrix,
    build_orbit_coeff_matrices,
    cluster_eigenvalues,
    form_group_algebra_element,
)

OUT = ROOT / "workspace/data/conic_pilot_preflight"
COUNT = [0, 0, 3, 5, 4, 7]


def block_target(n, a, b):
    if a == b:
        return comb(int(n[a]), 2)
    return int(n[a]) * int(n[b])


def offblock_max_for_matrix(C, vecs, clusters, mask_off):
    dense = C.toarray() if hasattr(C, "toarray") else np.asarray(C)
    T = vecs.T @ dense @ vecs
    return float(np.max(np.abs(T[mask_off]))) if mask_off.any() else 0.0


def summarize_saved_continuous_witness(n, pair_sizes, pair_ep, K, Mpair, pt_orb, pair_orb):
    stem = "n_" + "_".join(str(v) for v in n)
    z_path = ROOT / f"workspace/data/fixed_count_block_psd/{stem}_z.npy"
    if not z_path.exists():
        return {"exists": False, "path": str(z_path)}
    z = np.load(z_path)
    y = z[K:]
    m_float = np.array(pair_sizes, dtype=float) * y
    Mfull = build_full_moment_matrix(z, pt_orb, pair_orb, K)
    eig = np.linalg.eigvalsh(Mfull)
    block_res = []
    for a in range(K):
        for b in range(a, K):
            idxs = [j for j, ep in enumerate(pair_ep) if tuple(map(int, ep)) == (a, b)]
            lhs = float(np.sum(m_float[idxs]))
            rhs = float(block_target(n, a, b))
            block_res.append({"block": [a, b], "lhs": lhs, "rhs": rhs, "residual": lhs - rhs, "pair_orbits": len(idxs)})
    return {
        "exists": True,
        "z_path": str(z_path),
        "m_integrality_max_distance": float(np.max(np.abs(m_float - np.rint(m_float)))),
        "m_integrality_sum_distance": float(np.sum(np.abs(m_float - np.rint(m_float)))),
        "m_total_float": float(np.sum(m_float)),
        "m_min": float(np.min(m_float)),
        "m_max": float(np.max(m_float)),
        "m_nonzero_abs_gt_1e_9": int(np.sum(np.abs(m_float) > 1e-9)),
        "full_moment_min_eig": float(eig[0]),
        "full_moment_nullity_lt_1e_8_abs": int(np.sum(np.abs(eig) < 1e-8)),
        "full_moment_negative_lt_1e_8": int(np.sum(eig < -1e-8)),
        "smallest_12_eigs": [float(x) for x in eig[:12]],
        "block_total_max_abs_residual": float(max(abs(r["residual"]) for r in block_res)),
        "block_totals": block_res,
    }


def summarize_integer_rounds(n):
    p = ROOT / "workspace/data/integer_pair_psd_loop/integer_pair_psd_loop.json"
    if not p.exists():
        return {"exists": False, "path": str(p)}
    data = json.loads(p.read_text())
    target = tuple(n)
    out = []
    for rec in data.get("results", []):
        if tuple(rec.get("n", [])) != target:
            continue
        for rd in rec.get("rounds", []):
            out.append({
                "iter": rd.get("iter"),
                "status": rd.get("status"),
                "min_eig": rd.get("min_eig"),
                "neg_eigs_1e_8": rd.get("neg_eigs_1e_8"),
                "m_nonzero_orbits": rd.get("m_nonzero_orbits"),
                "exact_fraction_feasible": rd.get("exact_fraction_feasible"),
                "exact_max_ub_violation": rd.get("exact_max_ub_violation"),
            })
    return {"exists": True, "rounds_for_count": out}


def main():
    t0 = time.time()
    OUT.mkdir(parents=True, exist_ok=True)
    print("analysis: conic-guided pilot preflight", flush=True)

    perms = build_stabilizer()
    pt_orb, point_orbits = compute_point_orbits(perms)
    pair_orb, pair_sizes, pair_ep, Mpair = compute_pair_orbits(perms, pt_orb)
    K = len(point_orbits)
    point_sizes = [len(o) for o in point_orbits]
    print(f"  |G|={len(perms)}, point_sizes={point_sizes}, pair_orbits={Mpair}", flush=True)

    C0, C_pt, C_pr = build_orbit_coeff_matrices(point_orbits, pair_orb, K, Mpair)
    H = form_group_algebra_element(perms, seed=69)
    vals, vecs = eigh(H)
    clusters = cluster_eigenvalues(vals, tol=1e-6)
    cluster_id = np.empty(256, dtype=int)
    for cidx, (_, indices) in enumerate(clusters):
        cluster_id[np.array(indices, dtype=int)] = cidx
    mask_off = cluster_id[:, None] != cluster_id[None, :]
    hist = Counter(len(idx) for _, idx in clusters)
    print(f"  clusters={len(clusters)}, hist={dict(sorted(hist.items()))}", flush=True)

    off_records = []
    mats = [("C0", -1, C0)] + [("C_pt", a, C_pt[a]) for a in range(K)] + [("C_pr", j, C_pr[j]) for j in range(Mpair)]
    for typ, idx, C in mats:
        off = offblock_max_for_matrix(C, vecs, clusters, mask_off)
        off_records.append({"type": typ, "index": int(idx), "max_abs_offblock": off})
    max_off = max(r["max_abs_offblock"] for r in off_records)
    worst = sorted(off_records, key=lambda r: r["max_abs_offblock"], reverse=True)[:10]
    print(f"  coefficient off-block max={max_off:.3e}", flush=True)

    # Fixed-count block/variable reduction.
    by_block = defaultdict(list)
    for j, ep in enumerate(pair_ep):
        by_block[tuple(map(int, ep))].append(j)
    block_summary = []
    forced_zero = set()
    for a in range(K):
        for b in range(a, K):
            js = by_block[(a, b)]
            tgt = block_target(COUNT, a, b)
            if tgt == 0:
                forced_zero.update(js)
            block_summary.append({
                "block": [a, b],
                "target": int(tgt),
                "pair_orbit_count": int(len(js)),
                "total_labelled_pairs_in_block": int(sum(pair_sizes[j] for j in js)),
                "forced_zero_block": bool(tgt == 0),
            })
    active = [j for j in range(Mpair) if j not in forced_zero]
    print(f"  count={COUNT}: forced_zero_pair_orbits={len(forced_zero)}, active_pair_orbits={len(active)}", flush=True)

    payload = {
        "schema": "conic_pilot_preflight_v1",
        "meaning": "Preflight checks for a bounded conic-guided integer pair-count pilot. It validates analysis coefficient block separation and records fixed-count reductions for n=[0,0,3,5,4,7].",
        "count": COUNT,
        "group_size": len(perms),
        "point_orbit_sizes": point_sizes,
        "pair_orbit_count": int(Mpair),
        "block_decomposition": {
            "n_clusters": len(clusters),
            "histogram": {str(k): int(v) for k, v in sorted(hist.items())},
            "coefficient_max_abs_offblock": max_off,
            "worst_offblock_coefficients": worst,
            "validation_pass_1e_8": bool(max_off < 1e-8),
        },
        "fixed_count_reduction": {
            "forced_zero_point_orbits": [int(i) for i, v in enumerate(COUNT) if v == 0],
            "forced_zero_pair_orbits": sorted(int(j) for j in forced_zero),
            "forced_zero_pair_orbit_count": int(len(forced_zero)),
            "active_pair_orbits": [int(j) for j in active],
            "active_pair_orbit_count": int(len(active)),
            "block_summary": block_summary,
            "total_pair_target": int(sum(block_target(COUNT, a, b) for a in range(K) for b in range(a, K))),
        },
        "saved_continuous_witness": summarize_saved_continuous_witness(COUNT, pair_sizes, pair_ep, K, Mpair, pt_orb, pair_orb),
        "integer_rounds": summarize_integer_rounds(COUNT),
        "elapsed_sec": round(time.time() - t0, 3),
    }
    out = OUT / "n_0_0_3_5_4_7_preflight.json"
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "block_validation_pass_1e_8": payload["block_decomposition"]["validation_pass_1e_8"],
        "coefficient_max_abs_offblock": max_off,
        "active_pair_orbits": len(active),
        "forced_zero_pair_orbits": len(forced_zero),
        "continuous_witness_integrality_sum_distance": payload["saved_continuous_witness"].get("m_integrality_sum_distance"),
        "elapsed_sec": payload["elapsed_sec"],
    }, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
