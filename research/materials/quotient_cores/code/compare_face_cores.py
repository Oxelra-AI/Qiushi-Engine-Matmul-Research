#!/usr/bin/env python3
"""analysis: compare proof-core Wang rows across three verified face cuts.

The point is to ask whether the face-cut proofs are just arbitrary LP-face
exclusions or whether they repeatedly use related complete-Wang rows.  The
script compares the analysis J65 proof core and the two analysis replayed face
proof cores by representative full E11 Wang row id / key-L pair, face-set
intersections, and recurring row incidence.
"""
from __future__ import annotations

import json
import pickle
import hashlib
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path("research/research_record")
INPUTS = [
    ("J65_original", ROOT / "workspace/data/jface_core/J65_core_used_constraints.pkl", ROOT / "workspace/data/jface_core/J65_core_clause_analysis.json"),
    ("transJ65_random630631", ROOT / "workspace/data/face_core/transJ65_random630631_used_constraints.pkl", ROOT / "workspace/data/face_core/transJ65_random630631_core_clause_analysis.json"),
    ("transJ65_random630632", ROOT / "workspace/data/face_core/transJ65_random630632_used_constraints.pkl", ROOT / "workspace/data/face_core/transJ65_random630632_core_clause_analysis.json"),
]
OUTDIR = ROOT / "workspace/data/face_core"


def sha_payload(obj) -> str:
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def points_from_bitset(mask: int) -> list[int]:
    pts = []
    bs = int(mask)
    while bs:
        bit = bs & -bs
        pts.append(bit.bit_length())
        bs ^= bit
    return pts


def slim_row(rec: dict) -> dict:
    src = rec["representative_full_source"]
    return {
        "row_index": int(src["row_index"]),
        "key8": int(src["key8"]),
        "dim8": int(src["dim8"]),
        "L": int(src["L"]),
        "cap": int(src["cap"]),
        "full_size": int(src.get("full_size", (1 << int(src["dim8"])) - 1)),
        "full_point_bitset": int(src["full_point_bitset"]),
        "restricted_size": int(rec["restricted_size"]),
        "core_clause_count": int(rec["core_clause_count"]),
        "source_count_same_restriction_all_caps": int(rec.get("source_count_same_restriction_all_caps", 1)),
        "source_count_min_cap": int(rec.get("source_count_min_cap", 1)),
    }


def main() -> None:
    OUTDIR.mkdir(parents=True, exist_ok=True)
    faces = []
    for name, pkl_path, summary_path in INPUTS:
        with pkl_path.open("rb") as f:
            d = pickle.load(f)
        summary = json.loads(summary_path.read_text())
        rows = [slim_row(r) for r in d["used_constraints"]]
        row_by_id = {r["row_index"]: r for r in rows}
        keyL_by_id = {r["row_index"]: (r["key8"], r["L"]) for r in rows}
        faces.append({
            "name": name,
            "J": set(map(int, d["J"])),
            "outside": set(map(int, d.get("outside", []))),
            "rows": rows,
            "row_by_id": row_by_id,
            "keyL_by_id": keyL_by_id,
            "summary": summary,
        })
    face_summaries = {}
    for f in faces:
        rows = f["rows"]
        face_summaries[f["name"]] = {
            "J_size": len(f["J"]),
            "outside_size": len(f["outside"]),
            "core_clause_count": f["summary"]["matching"]["core_clause_total"],
            "used_row_count": len(rows),
            "used_row_ids_sha256": sha_payload(sorted(f["row_by_id"])),
            "by_dim8": {str(k): int(v) for k, v in sorted(Counter(r["dim8"] for r in rows).items())},
            "by_L": {str(k): int(v) for k, v in sorted(Counter(r["L"] for r in rows).items())},
            "by_restricted_size": {str(k): int(v) for k, v in sorted(Counter(r["restricted_size"] for r in rows).items())},
            "top_core_clause_rows": [
                {k: r[k] for k in ["row_index", "key8", "dim8", "L", "cap", "restricted_size", "core_clause_count"]}
                for r in sorted(rows, key=lambda rr: (-rr["core_clause_count"], rr["row_index"]))[:20]
            ],
        }
    pair_summaries = {}
    for i in range(len(faces)):
        for j in range(i + 1, len(faces)):
            a, b = faces[i], faces[j]
            interJ = a["J"] & b["J"]
            unionJ = a["J"] | b["J"]
            inter_rows = set(a["row_by_id"]) & set(b["row_by_id"])
            union_rows = set(a["row_by_id"]) | set(b["row_by_id"])
            # same key-L can collapse different representative row IDs only if row indexing differs; keep as robustness check.
            keyL_a = set(a["keyL_by_id"].values())
            keyL_b = set(b["keyL_by_id"].values())
            pair_summaries[f"{a['name']}__{b['name']}"] = {
                "J_intersection_size": len(interJ),
                "J_union_size": len(unionJ),
                "J_intersection_points": sorted(interJ),
                "used_row_intersection_count": len(inter_rows),
                "used_row_union_count": len(union_rows),
                "used_row_jaccard": float(len(inter_rows) / len(union_rows)) if union_rows else None,
                "used_keyL_intersection_count": len(keyL_a & keyL_b),
                "used_keyL_union_count": len(keyL_a | keyL_b),
                "intersection_by_dim8": {str(k): int(v) for k, v in sorted(Counter(a["row_by_id"][rid]["dim8"] for rid in inter_rows).items())},
                "intersection_by_L": {str(k): int(v) for k, v in sorted(Counter(a["row_by_id"][rid]["L"] for rid in inter_rows).items())},
                "intersection_examples": [
                    {k: a["row_by_id"][rid][k] for k in ["row_index", "key8", "dim8", "L", "cap", "restricted_size", "core_clause_count"]}
                    for rid in sorted(inter_rows)[:30]
                ],
            }
    row_occ = defaultdict(list)
    for f in faces:
        for rid, rec in f["row_by_id"].items():
            row_occ[rid].append(f["name"])
    occ_hist = Counter(len(v) for v in row_occ.values())
    recurring_ids = sorted([rid for rid, ns in row_occ.items() if len(ns) >= 2])
    triple_ids = sorted([rid for rid, ns in row_occ.items() if len(ns) == 3])
    # Use first face containing each row for metadata.
    row_lookup = {}
    for f in faces:
        row_lookup.update({rid: rec for rid, rec in f["row_by_id"].items() if rid not in row_lookup})
    recurring_examples = []
    for rid in recurring_ids[:200]:
        base = row_lookup[rid]
        per_face = {}
        fullset = set(points_from_bitset(base["full_point_bitset"]))
        for f in faces:
            if rid in f["row_by_id"]:
                r = f["row_by_id"][rid]
                per_face[f["name"]] = {
                    "used": True,
                    "restricted_size_in_core_record": r["restricted_size"],
                    "full_row_intersection_with_face_J": len(fullset & f["J"]),
                    "core_clause_count": r["core_clause_count"],
                }
            else:
                per_face[f["name"]] = {"used": False, "full_row_intersection_with_face_J": len(fullset & f["J"])}
        recurring_examples.append({
            "row_index": rid,
            "key8": base["key8"],
            "dim8": base["dim8"],
            "L": base["L"],
            "cap": base["cap"],
            "full_size": base["full_size"],
            "appears_in": row_occ[rid],
            "per_face": per_face,
            "full_points_head": sorted(fullset)[:80],
        })
    # Point-level participation in faces and in recurring rows.
    point_face_count = Counter()
    for f in faces:
        point_face_count.update(f["J"])
    point_recurring_row_incidence = Counter()
    point_triple_row_incidence = Counter()
    for rid in recurring_ids:
        point_recurring_row_incidence.update(points_from_bitset(row_lookup[rid]["full_point_bitset"]))
    for rid in triple_ids:
        point_triple_row_incidence.update(points_from_bitset(row_lookup[rid]["full_point_bitset"]))
    payload = {
        "schema": "face_core_recurrence_v1",
        "meaning": "Comparison of representative full Wang rows used in three verified support-face proofs. Recurrence suggests which occupation constraints repeatedly participate, but the row sets themselves are proof/encoding dependent and not by themselves new cuts.",
        "faces": face_summaries,
        "pairwise": pair_summaries,
        "row_occurrence_histogram": {str(k): int(v) for k, v in sorted(occ_hist.items())},
        "unique_used_row_union_count": int(len(row_occ)),
        "rows_used_in_at_least_two_faces": int(len(recurring_ids)),
        "rows_used_in_all_three_faces": int(len(triple_ids)),
        "recurring_by_dim8": {str(k): int(v) for k, v in sorted(Counter(row_lookup[rid]["dim8"] for rid in recurring_ids).items())},
        "recurring_by_L": {str(k): int(v) for k, v in sorted(Counter(row_lookup[rid]["L"] for rid in recurring_ids).items())},
        "triple_by_dim8": {str(k): int(v) for k, v in sorted(Counter(row_lookup[rid]["dim8"] for rid in triple_ids).items())},
        "triple_by_L": {str(k): int(v) for k, v in sorted(Counter(row_lookup[rid]["L"] for rid in triple_ids).items())},
        "recurring_row_ids_sha256": sha_payload(recurring_ids),
        "triple_row_ids_sha256": sha_payload(triple_ids),
        "recurring_examples_head": recurring_examples,
        "point_face_count_histogram": {str(k): int(v) for k, v in sorted(Counter(point_face_count.values()).items())},
        "top_points_by_recurring_row_incidence": [[int(p), int(c), int(point_face_count[p])] for p, c in point_recurring_row_incidence.most_common(30)],
        "top_points_by_triple_row_incidence": [[int(p), int(c), int(point_face_count[p])] for p, c in point_triple_row_incidence.most_common(30)],
    }
    out = OUTDIR / "face_core_recurrence_summary.json"
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    # Also write compact row-id files for subsequent exact tests.
    (OUTDIR / "face_core_recurring_row_ids.json").write_text(json.dumps({"rows_used_in_at_least_two_faces": recurring_ids, "rows_used_in_all_three_faces": triple_ids}, indent=2) + "\n")
    print(json.dumps({
        "out": str(out),
        "faces": {k: {kk: vv for kk, vv in v.items() if kk in ("J_size", "used_row_count", "core_clause_count")} for k, v in face_summaries.items()},
        "row_occurrence_histogram": payload["row_occurrence_histogram"],
        "rows_used_in_at_least_two_faces": len(recurring_ids),
        "rows_used_in_all_three_faces": len(triple_ids),
        "recurring_by_L": payload["recurring_by_L"],
        "triple_by_L": payload["triple_by_L"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
