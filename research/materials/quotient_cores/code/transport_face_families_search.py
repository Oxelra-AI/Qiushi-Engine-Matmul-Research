#!/usr/bin/env python3
"""analysis: transport all verified face cuts and test their integer-search effect.

Inputs are support-face UNSAT proofs.  If a face J has a verified complete-Wang
CNF/DRAT proof, then every complete-Wang distinct support satisfies
    sum_{p in gJ} x_p <= 18
for every E11 stabilizer image gJ.  This script deduplicates the union of the
transported families for the analysis J65 face and the two analysis replayed
faces, records incidence/coverage statistics, and optionally runs a CP-SAT
support search with the primitive-reduced Wang rows plus these learned cuts and
other already sound support cuts.

The CP-SAT result is search evidence only; only the base face CNF/DRAT proofs
and symmetry transport give certified support cuts.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import ROOT, build_core_constraints, complete_core_wang_scan  # noqa: E402
from distinct_trace_cut_cpsat import generate_stabilizer_permutations  # noqa: E402
from cert_trace_separator import full_violation_scan  # noqa: E402

LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
REDUCED_ROWS = ROOT / "workspace/data/reduced_wang/primitive_reduced_rows.pkl"
OVERLAP_FAMILY = ROOT / "workspace/data/transported_overlap/transported_overlap_analysis.json"
TRACE_CUTS = ROOT / "workspace/data/trace_dependency_cuts/trace_dependency_cuts_size5.pkl"
CERT_CUTS = ROOT / "workspace/data/neighborhood_repair/guarded_trace_certificate_coverage.json"
OUTDIR = ROOT / "workspace/data/transported_faces"

BASE_FACES = [
    {
        "name": "J65_original",
        "J_points_file": ROOT / "workspace/data/global_J_face/J65_cut_record.json",
        "status_file": ROOT / "workspace/data/global_J_face/cnf/J65_complete_wang.status.json",
        "expected_cnf_sha256": "5c1a701574b028f217a2ebaafae4a2e092720f41c477de3e73d000007c2228a7",
    },
    {
        "name": "transJ65_random630631",
        "J_points_file": ROOT / "workspace/data/face_loop/face_cpsat_transJ65_random630631.json",
        "status_file": ROOT / "workspace/data/face_cnf/transJ65_random630631.status.json",
        "expected_cnf_sha256": "d9e83ca246234cfa6f3c10b7c51a0154d5c7bf15244aaa5e9c6245c61635ca54",
    },
    {
        "name": "transJ65_random630632",
        "J_points_file": ROOT / "workspace/data/face_loop/face_cpsat_transJ65_random630632.json",
        "status_file": ROOT / "workspace/data/face_cnf/transJ65_random630632.status.json",
        "expected_cnf_sha256": "48116be693e379ac772ec7f8cd3e2dfedb3018c25bde69c90b865f280c0c88d6",
    },
]


def sha_payload(obj) -> str:
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def mask_from_points(points: Iterable[int]) -> int:
    m = 0
    for p in points:
        m |= 1 << (int(p) - 1)
    return m


def points_from_mask(mask: int) -> list[int]:
    pts = []
    bs = int(mask)
    while bs:
        bit = bs & -bs
        pts.append(bit.bit_length())
        bs ^= bit
    return pts


def load_verified_face(spec: dict) -> dict:
    status = json.loads(spec["status_file"].read_text())
    d = json.loads(spec["J_points_file"].read_text())
    J = [int(p) for p in d["J_points"]]
    drat_ok = bool(status.get("drat_trim_log_parse", {}).get("contains_verified")) and status.get("cadical_exit") == 20 and status.get("drat_trim_exit") == 0
    cnf_sha = status.get("hashes", {}).get(str(status.get("cnf"))) or status.get("hashes", {}).get(str(Path(status.get("cnf", ""))))
    # Path keys in status are strings; fall back to any .cnf hash.
    if cnf_sha is None:
        for k, v in status.get("hashes", {}).items():
            if k.endswith(".cnf"):
                cnf_sha = v
                break
    return {
        "name": spec["name"],
        "J_points": J,
        "J_size": len(J),
        "J_mask": mask_from_points(J),
        "status_file": str(spec["status_file"]),
        "J_points_file": str(spec["J_points_file"]),
        "drat_verified": drat_ok,
        "cnf_sha256": cnf_sha,
        "drat_sha256": next((v for k, v in status.get("hashes", {}).items() if k.endswith(".drat")), None),
        "cadical_sec": status.get("cadical_elapsed_sec"),
        "drat_trim_sec": status.get("drat_trim_elapsed_sec"),
        "expected_cnf_sha256": spec.get("expected_cnf_sha256"),
        "expected_cnf_sha256_matches": (cnf_sha == spec.get("expected_cnf_sha256")),
    }


def build_families(faces: list[dict]):
    perms = generate_stabilizer_permutations(include_transpose=True)
    cut_owner = defaultdict(list)
    families = []
    for face in faces:
        masks = sorted({mask_from_points(int(perm[p]) for p in face["J_points"]) for perm in perms})
        images = [points_from_mask(m) for m in masks]
        for m in masks:
            cut_owner[m].append(face["name"])
        families.append({
            "name": face["name"],
            "base_J_size": face["J_size"],
            "unique_image_count": len(masks),
            "image_sizes": sorted({len(img) for img in images}),
            "image_masks": masks,
            "image_family_sha256": sha_payload(images),
            "overlap_with_base_histogram": {str(k): int(v) for k, v in sorted(Counter((m & face["J_mask"]).bit_count() for m in masks).items())},
        })
    union_masks = sorted(cut_owner)
    union_images = [points_from_mask(m) for m in union_masks]
    point_frequency = Counter()
    for img in union_images:
        point_frequency.update(img)
    origin_hist = Counter(tuple(sorted(v)) for v in cut_owner.values())
    return perms, families, union_masks, union_images, cut_owner, point_frequency, origin_hist


def load_reduced_records():
    if not REDUCED_ROWS.exists():
        return None, None
    with REDUCED_ROWS.open("rb") as f:
        d = pickle.load(f)
    rows = d.get("retained_records") or d.get("records") or d.get("retained")
    if rows is None and isinstance(d, list):
        rows = d
    return d, rows


def row_points(rec: dict) -> list[int]:
    pts = []
    bs = int(rec["point_bitset"])
    while bs:
        bit = bs & -bs
        pts.append(bit.bit_length())
        bs ^= bit
    return pts


def load_overlap_masks():
    if not OVERLAP_FAMILY.exists():
        return []
    d = json.loads(OVERLAP_FAMILY.read_text())
    cuts = d.get("global_cuts") or d.get("transported_cuts") or d.get("cut_images")
    masks = []
    if cuts:
        for c in cuts:
            pts = c.get("points") if isinstance(c, dict) else c
            if pts:
                masks.append(mask_from_points(pts))
    else:
        base = d.get("base_support")
        if base:
            perms = generate_stabilizer_permutations(include_transpose=True)
            masks = sorted({mask_from_points(int(perm[p]) for p in base) for perm in perms})
    return sorted(set(masks))


def load_trace_minimal_cuts():
    if not TRACE_CUTS.exists():
        return []
    with TRACE_CUTS.open("rb") as f:
        data = pickle.load(f)
    cuts = []
    for p, hs in data.get("cuts_by_p", {}).items():
        for h in hs:
            cuts.append((int(p), [int(q) for q in h]))
    return cuts


def load_cert_cuts():
    # The guarded trace certificate file is heterogeneous across steps; only use it if it exposes explicit linear cuts.
    if not CERT_CUTS.exists():
        return []
    try:
        d = json.loads(CERT_CUTS.read_text())
    except Exception:
        return []
    out = []
    for key in ["cuts", "guarded_cuts", "valid_cuts"]:
        for c in d.get(key, []) or []:
            pts = c.get("points") or c.get("support") or c.get("lhs_points")
            cap = c.get("cap") or c.get("rhs")
            if pts is not None and cap is not None:
                out.append((mask_from_points(pts), int(cap)))
    return out


def solve_search(union_masks, args):
    from ortools.sat.python import cp_model
    t0 = time.time()
    lut, lut_meta = load_lut(LUT_PATH)
    all_records, all_meta = build_core_constraints(CoreQuotient(1), lut)
    if args.rows == "complete":
        records = all_records
        complete_meta = all_meta
        row_source = "complete_417199"
    else:
        d, rows = load_reduced_records()
        if isinstance(d, dict) and "kept_key8" in d:
            kept = set(int(k) for k in d["kept_key8"])
            records = [rec for rec in all_records if int(rec["key8"]) in kept]
            complete_meta = {
                "row_source": str(REDUCED_ROWS),
                "loaded_count": len(records),
                "reduced_file_info": {k: d.get(k) for k in ["rank_s", "description"]},
                "reduced_counts": {"kept_key8": len(d.get("kept_key8", [])), "dropped_key8": len(d.get("dropped_key8", []))},
                "complete_meta_for_reconstruction": all_meta,
            }
            row_source = "primitive_reduced_key_filter"
        elif rows is not None:
            records = rows
            complete_meta = {"row_source": str(REDUCED_ROWS), "loaded_count": len(rows), "manifest_head": {k: v for k, v in d.items() if k != "retained_records"} if isinstance(d, dict) else None}
            row_source = "primitive_reduced_records"
        else:
            records = all_records
            complete_meta = all_meta | {"warning": "primitive_reduced_rows.pkl did not expose kept_key8 or retained records; used complete fallback"}
            row_source = "complete_fallback_reduced_missing"
    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in range(1, 256)}
    model.Add(sum(x.values()) == 19)
    row_count = 0
    row_by_dim = Counter()
    row_by_L = Counter()
    for rec in records:
        cap = 19 - int(rec["L"])
        pts = row_points(rec)
        if len(pts) <= cap:
            continue
        model.Add(sum(x[p] for p in pts) <= cap)
        row_count += 1
        row_by_dim[int(rec.get("dim8", -1))] += 1
        row_by_L[int(rec["L"])] += 1
    face_cut_count = 0
    for m in union_masks:
        pts = points_from_mask(m)
        model.Add(sum(x[p] for p in pts) <= 18)
        face_cut_count += 1
    overlap_cut_count = 0
    if args.include_overlap:
        for m in load_overlap_masks():
            pts = points_from_mask(m)
            model.Add(sum(x[p] for p in pts) <= 15)
            overlap_cut_count += 1
    # Add minimal trace dependency cuts only if requested and if the exact original semantics are available.
    trace_cut_count = 0
    # In analysis these are guarded cuts over q masks, not simple point cuts; omit unless future script reconstructs them exactly.
    model.Minimize(sum((p % 257) * x[p] for p in range(1, 256)))
    build_sec = time.time() - t0
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(args.solver_time)
    solver.parameters.num_search_workers = int(args.workers)
    solver.parameters.random_seed = int(args.seed)
    ts = time.time()
    st = solver.Solve(model)
    solve_sec = time.time() - ts
    status_name = solver.StatusName(st)
    result = {
        "schema": "transported_faces_cpsat_search_v1",
        "meaning": "CP-SAT support search with Wang rows and transported verified face cuts. This is search evidence only; any infeasibility proof requires replayable CNF/PB.",
        "row_source": row_source,
        "complete_or_reduced_meta": complete_meta,
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "parameters": {"rows": args.rows, "solver_time": args.solver_time, "workers": args.workers, "seed": args.seed, "include_overlap": args.include_overlap},
        "constraints": {
            "wang_rows_added": row_count,
            "wang_rows_by_dim": {str(k): int(v) for k, v in sorted(row_by_dim.items())},
            "wang_rows_by_L": {str(k): int(v) for k, v in sorted(row_by_L.items())},
            "transported_face_cuts_added": face_cut_count,
            "transported_overlap_cuts_added": overlap_cut_count,
            "trace_dependency_cuts_added": trace_cut_count,
        },
        "build_sec": round(build_sec, 3),
        "status": status_name,
        "solve_sec": round(solve_sec, 3),
    }
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        support = [p for p in range(1, 256) if solver.Value(x[p])]
        complete_records, full_meta = build_core_constraints(CoreQuotient(1), lut)
        scan = complete_core_wang_scan("transported_faces_solution", support, 19, complete_records, max_head=20)
        fullscan = full_violation_scan(support, complete_records, 19)
        face_overlaps = [(i, (m & mask_from_points(support)).bit_count()) for i, m in enumerate(union_masks)]
        result["solution"] = {
            "A_cols": support,
            "objective_value": solver.ObjectiveValue(),
            "complete_wang_violation_count": scan["complete_violation_count"],
            "complete_wang_scan_head": scan,
            "complete_wang_violation_count_with_points": fullscan["complete_violation_count"],
            "max_transported_face_overlap": max(v for _, v in face_overlaps),
            "tight_transported_face_cuts": sum(1 for _, v in face_overlaps if v == 18),
            "top_face_overlaps": sorted(face_overlaps, key=lambda kv: -kv[1])[:20],
            "full_complete_meta": full_meta,
        }
    result["elapsed_sec"] = round(time.time() - t0, 3)
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--solve", action="store_true")
    ap.add_argument("--rows", choices=["reduced", "complete"], default="reduced")
    ap.add_argument("--include-overlap", action="store_true")
    ap.add_argument("--solver-time", type=float, default=300.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=640064)
    args = ap.parse_args()
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    faces = [load_verified_face(s) for s in BASE_FACES]
    if not all(f["drat_verified"] for f in faces):
        raise RuntimeError("Not all base faces have verified DRAT status")
    perms, families, union_masks, union_images, cut_owner, point_frequency, origin_hist = build_families(faces)
    pair_overlap_hist = Counter()
    for i in range(len(union_masks)):
        mi = union_masks[i]
        for j in range(i, len(union_masks)):
            pair_overlap_hist[(mi & union_masks[j]).bit_count()] += 1
    # Interactions with known stored near-misses/candidates.
    stored = []
    analysis_path = ROOT / "workspace/data/transported_overlap/transported_overlap_analysis.json"
    if analysis_path.exists():
        d = json.loads(analysis_path.read_text())
        for rec in d.get("all_records", [])[:1000]:
            support = [int(p) for p in rec.get("A_cols", [])]
            if support:
                sm = mask_from_points(support)
                overlaps = [(sm & m).bit_count() for m in union_masks]
                stored.append({
                    "name": rec.get("name"),
                    "source": rec.get("source"),
                    "complete_wang_violations": rec.get("complete_wang_violations"),
                    "max_overlap_with_transported_face_cuts": max(overlaps) if overlaps else None,
                    "number_face_cuts_violated_if_admissible": sum(1 for v in overlaps if v >= 19),
                    "top_overlaps_hist": {str(k): int(v) for k, v in sorted(Counter(overlaps).items()) if k >= 15},
                })
    manifest = {
        "schema": "transported_face_families_v1",
        "meaning": "Union of transported complete-Wang support-face cuts from three DRAT-verified faces. Each cut is valid for distinct length-19 E11 supports; the family is intended for integer search, not LP convergence.",
        "base_faces": faces,
        "group_permutation_count": len(perms),
        "families": [{k: v for k, v in fam.items() if k != "image_masks"} for fam in families],
        "union_cut_count": len(union_masks),
        "union_image_sizes": sorted({len(img) for img in union_images}),
        "union_family_sha256": sha_payload(union_images),
        "origin_combination_histogram": {" & ".join(k): int(v) for k, v in sorted(origin_hist.items(), key=lambda kv: (len(kv[0]), kv[0]))},
        "point_frequency_histogram": {str(k): int(v) for k, v in sorted(Counter(point_frequency.values()).items())},
        "point_frequencies": {str(p): int(point_frequency[p]) for p in range(1, 256)},
        "pair_overlap_histogram_i_le_j_head": {str(k): int(v) for k, v in sorted(pair_overlap_hist.items())},
        "cuts": [{"index": i, "points": union_images[i], "size": len(union_images[i]), "mask_hex": hex(union_masks[i]), "source_faces": cut_owner[union_masks[i]]} for i in range(len(union_masks))],
        "stored_support_overlap_records": stored,
        "elapsed_family_sec": round(time.time() - t0, 3),
    }
    (OUTDIR / "transported_face_families.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    result = None
    if args.solve:
        result = solve_search(union_masks, args)
        suffix = f"{args.rows}_faces"
        if args.include_overlap:
            suffix += "_overlap"
        suffix += f"_{int(args.solver_time)}s"
        (OUTDIR / f"cpsat_{suffix}.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "family_file": str(OUTDIR / "transported_face_families.json"),
        "union_cut_count": len(union_masks),
        "family_counts": {fam["name"]: fam["unique_image_count"] for fam in families},
        "origin_combination_histogram": manifest["origin_combination_histogram"],
        "point_frequency_histogram": manifest["point_frequency_histogram"],
        "search_status": None if result is None else result["status"],
        "solution_complete_violations": None if result is None else result.get("solution", {}).get("complete_wang_violation_count"),
        "elapsed_sec": round(time.time() - t0, 3),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
