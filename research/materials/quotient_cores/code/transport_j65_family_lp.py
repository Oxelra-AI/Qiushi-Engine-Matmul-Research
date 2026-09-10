#!/usr/bin/env python3
"""analysis: transport the analysis J65 face cut and test LP effect.

analysis proved, with a DRAT-verified CNF over the 65-point face J, that no
complete-Wang distinct 19-support is contained in J.  Since analysis verified
that the E11 stabilizer preserves the complete core Wang table, every whole-set
image gJ has the same consequence

    sum_{p in gJ} x_p <= 18.

This script deduplicates that orbit and solves a few complete-Wang LPs with all
transported J65 cuts added.  LP solutions remain fractional targets only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np
from scipy import sparse
from scipy.optimize import linprog

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import ROOT, build_core_constraints  # noqa: E402
from distinct_trace_cut_cpsat import generate_stabilizer_permutations  # noqa: E402

CUT_RECORD = ROOT / "workspace/data/global_J_face/J65_cut_record.json"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
OUTDIR = ROOT / "workspace/data/j65_transport"


def mask_from_points(points: Iterable[int]) -> int:
    m = 0
    for p in points:
        p = int(p)
        if not (1 <= p <= 255):
            raise ValueError(p)
        m |= 1 << (p - 1)
    return m


def points_from_mask(mask: int) -> list[int]:
    out = []
    bs = int(mask)
    while bs:
        bit = bs & -bs
        out.append(bit.bit_length())
        bs ^= bit
    return out


def sha_payload(obj) -> str:
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def build_sparse(records):
    rows = []
    cols = []
    vals = []
    b = []
    for i, rec in enumerate(records):
        b.append(19 - int(rec["L"]))
        bs = int(rec["point_bitset"])
        while bs:
            bit = bs & -bs
            rows.append(i)
            cols.append(bit.bit_length() - 1)
            vals.append(1.0)
            bs ^= bit
    A = sparse.csr_matrix((np.asarray(vals), (np.asarray(rows), np.asarray(cols))), shape=(len(records), 255))
    return A, np.asarray(b, dtype=float)


def add_transported_cut_matrix(A, b, image_masks: Sequence[int]):
    rows = []
    cols = []
    vals = []
    for i, mask in enumerate(image_masks):
        bs = int(mask)
        while bs:
            bit = bs & -bs
            rows.append(i)
            cols.append(bit.bit_length() - 1)
            vals.append(1.0)
            bs ^= bit
    C = sparse.csr_matrix((np.asarray(vals), (np.asarray(rows), np.asarray(cols))), shape=(len(image_masks), 255))
    A2 = sparse.vstack([A, C], format="csr")
    b2 = np.concatenate([b, np.full(len(image_masks), 18.0)])
    return A2, b2


def solve_lp(A2, b2, image_masks: Sequence[int], objective_kind: str, seed: int, time_limit: int):
    rng = np.random.default_rng(seed)
    if objective_kind == "random":
        c = rng.normal(size=255)
    elif objective_kind == "maximize_base_J":
        base = image_masks[0]
        c = np.zeros(255)
        for p in points_from_mask(base):
            c[p - 1] = -1.0
    elif objective_kind == "maximize_orbit_average":
        # This is constant over feasible sum=19 if the group is point-transitive; kept as a check.
        freq = np.zeros(255)
        for m in image_masks:
            for p in points_from_mask(m):
                freq[p - 1] += 1.0
        c = -freq
    else:
        raise ValueError(objective_kind)
    t0 = time.time()
    res = linprog(
        c,
        A_ub=A2,
        b_ub=b2,
        A_eq=sparse.csr_matrix(np.ones((1, 255))),
        b_eq=np.array([19.0]),
        bounds=[(0.0, 1.0)] * 255,
        method="highs",
        options={"time_limit": int(time_limit)},
    )
    info = {
        "objective_kind": objective_kind,
        "seed": int(seed),
        "success": bool(res.success),
        "message": str(res.message),
        "elapsed_sec": round(time.time() - t0, 3),
    }
    if res.success:
        x = np.asarray(res.x, dtype=float)
        rounded = np.rint(x)
        image_masses = []
        for m in image_masks:
            s = 0.0
            bs = int(m)
            while bs:
                bit = bs & -bs
                s += float(x[bit.bit_length() - 1])
                bs ^= bit
            image_masses.append(s)
        slacks = b2 - A2.dot(x)
        nonzero = [(i + 1, float(v)) for i, v in enumerate(x) if v > 1e-9]
        fractional = [(i + 1, float(v)) for i, v in enumerate(x) if abs(v - rounded[i]) > 1e-7]
        info.update({
            "objective_value": float(res.fun),
            "sum_x": float(x.sum()),
            "n_nonzero_coordinates_tol_1e-9": len(nonzero),
            "n_fractional_coordinates": len(fractional),
            "max_round_distance": float(np.max(np.abs(x - rounded))),
            "max_transported_J_mass": float(max(image_masses)),
            "min_transported_J_mass": float(min(image_masses)),
            "number_tight_transported_cuts_tol_1e-7": int(sum(abs(v - 18.0) < 1e-7 for v in image_masses)),
            "active_complete_wang_constraints_tol_1e-7": int(np.sum(np.abs(slacks[: len(slacks) - len(image_masks)]) < 1e-7)),
            "active_transported_J_cuts_tol_1e-7": int(np.sum(np.abs(slacks[len(slacks) - len(image_masks):]) < 1e-7)),
            "nonzero_coordinates": nonzero,
            "fractional_coordinates": fractional,
        })
    return info


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--solve", action="store_true")
    ap.add_argument("--lp-time", type=int, default=180)
    ap.add_argument("--random-runs", type=int, default=2)
    args = ap.parse_args()
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    cut = json.loads(CUT_RECORD.read_text())
    J = [int(p) for p in cut["J_points"]]
    base_mask = mask_from_points(J)
    perms = generate_stabilizer_permutations(include_transpose=True)
    image_masks = sorted({mask_from_points(int(perm[p]) for p in J) for perm in perms})
    images = [points_from_mask(m) for m in image_masks]
    image_index = {m: i for i, m in enumerate(image_masks)}
    base_image_index = image_index.get(base_mask)
    if base_image_index is not None and base_image_index != 0:
        # Put the original J first for objective naming and easier comparison.
        image_masks[0], image_masks[base_image_index] = image_masks[base_image_index], image_masks[0]
        images[0], images[base_image_index] = images[base_image_index], images[0]
    point_frequency = Counter()
    for img in images:
        point_frequency.update(img)
    overlap_with_base = Counter(len(set(J).intersection(img)) for img in images)
    pair_overlap_hist = Counter()
    for i in range(len(image_masks)):
        mi = image_masks[i]
        for j in range(i, len(image_masks)):
            pair_overlap_hist[(mi & image_masks[j]).bit_count()] += 1
    manifest = {
        "schema": "transported_J65_family_v1",
        "meaning": "Orbit of the analysis DRAT-supported J65 cut under the E11 stabilizer previously checked to preserve all complete E11 Wang rows. Each image gives sum_{p in gJ} x_p <= 18 for complete-Wang distinct 19-supports.",
        "source_cut_record": str(CUT_RECORD),
        "source_cut_cnf_sha256": cut.get("proof_artifacts", {}).get("cnf_sha256"),
        "source_cut_drat_sha256": cut.get("proof_artifacts", {}).get("drat_sha256"),
        "source_cut_drat_trim_verified": cut.get("proof_artifacts", {}).get("drat_trim_verified"),
        "group_permutation_count": len(perms),
        "unique_image_count": len(images),
        "base_J_size": len(J),
        "all_image_sizes": sorted(set(len(img) for img in images)),
        "image_family_sha256": sha_payload(images),
        "base_image_index_after_reorder": 0,
        "point_frequency_histogram": {str(k): int(v) for k, v in sorted(Counter(point_frequency.values()).items())},
        "point_frequencies": {str(p): int(point_frequency[p]) for p in range(1, 256)},
        "overlap_with_base_histogram": {str(k): int(v) for k, v in sorted(overlap_with_base.items())},
        "pair_overlap_histogram_i_le_j": {str(k): int(v) for k, v in sorted(pair_overlap_hist.items())},
        "cuts": [{"index": i, "points": img, "mask_hex": hex(image_masks[i])} for i, img in enumerate(images)],
        "elapsed_family_sec": round(time.time() - t0, 3),
    }
    (OUTDIR / "transported_J65_family.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    lp_runs = []
    if args.solve:
        lut, _ = load_lut(LUT_PATH)
        records, meta = build_core_constraints(CoreQuotient(1), lut)
        A, b = build_sparse(records)
        A2, b2 = add_transported_cut_matrix(A, b, image_masks)
        for kind, seed in [("maximize_base_J", 630630), ("random", 630631), ("random", 630632)][: 1 + args.random_runs]:
            print("solve", kind, seed, flush=True)
            r = solve_lp(A2, b2, image_masks, kind, seed, args.lp_time)
            print({k: r.get(k) for k in ["success", "objective_kind", "sum_x", "max_transported_J_mass", "n_nonzero_coordinates_tol_1e-9", "n_fractional_coordinates", "active_transported_J_cuts_tol_1e-7"]}, flush=True)
            lp_runs.append(r)
        lp_payload = {
            "schema": "transported_J65_lp_v1",
            "meaning": "Complete E11 Wang LP with all transported analysis J65 cuts. Solutions are fractional search targets only, not supports or rank evidence.",
            "family_file": str(OUTDIR / "transported_J65_family.json"),
            "complete_meta": meta,
            "transported_cut_count": len(image_masks),
            "runs": lp_runs,
            "elapsed_sec": round(time.time() - t0, 3),
        }
        (OUTDIR / "lp_with_transported_J65_cuts.json").write_text(json.dumps(lp_payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "family_file": str(OUTDIR / "transported_J65_family.json"),
        "unique_image_count": len(images),
        "image_family_sha256": manifest["image_family_sha256"],
        "overlap_with_base_histogram": manifest["overlap_with_base_histogram"],
        "point_frequency_histogram": manifest["point_frequency_histogram"],
        "lp_file": str(OUTDIR / "lp_with_transported_J65_cuts.json") if args.solve else None,
        "lp_run_count": len(lp_runs),
        "elapsed_sec": round(time.time() - t0, 3),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
