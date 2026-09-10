#!/usr/bin/env python3
"""analysis: make compact records for newly verified support-face cuts."""
from __future__ import annotations

import json
from pathlib import Path

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/face_cnf"
FACES = [
    ("transJ65_random630631", ROOT / "workspace/data/face_loop/face_cpsat_transJ65_random630631.json", OUTDIR / "transJ65_random630631.status.json", OUTDIR / "transJ65_random630631.meta.json"),
    ("transJ65_random630632", ROOT / "workspace/data/face_loop/face_cpsat_transJ65_random630632.json", OUTDIR / "transJ65_random630632.status.json", OUTDIR / "transJ65_random630632.meta.json"),
]


def choose_hash(status: dict, suffix: str):
    for k, v in status.get("hashes", {}).items():
        if k.endswith(suffix):
            return v
    return None


def main():
    records = []
    for name, face_file, status_file, meta_file in FACES:
        face = json.loads(face_file.read_text())
        status = json.loads(status_file.read_text())
        meta = json.loads(meta_file.read_text())
        drat_ok = status.get("cadical_exit") == 20 and status.get("drat_trim_exit") == 0 and bool(status.get("drat_trim_log_parse", {}).get("contains_verified"))
        rec = {
            "schema": "complete_wang_face_cut_v1",
            "name": name,
            "field": "F2",
            "core": "E11 quotient core",
            "rank_s": 19,
            "meaning": "DRAT-verified support-face consequence: no distinct 19-point complete-Wang E11 support is contained in J; hence every complete-Wang distinct support satisfies sum_{p in J} x_p <= 18.",
            "J_size": int(meta["J_size"]),
            "J_points": meta["J_points"],
            "cut": {"lhs_points": meta["J_points"], "rhs": 18, "equivalent_escape_statement": "sum_{p outside J} x_p >= 1"},
            "source_fractional_target": {
                "target_file": meta["target_file"],
                "target_label": meta["target_label"],
                "target_total_mass": meta["target_total_mass"],
                "target_mass_on_J": meta["target_mass_on_J"],
                "cp_sat_face_status_before_replay": face.get("status"),
            },
            "proof_artifacts": {
                "cnf": status.get("cnf"),
                "drat": status.get("drat"),
                "status": str(status_file),
                "meta": str(meta_file),
                "input_core_cnf": status.get("input_core_cnf"),
                "cadical_exit": status.get("cadical_exit"),
                "cadical_elapsed_sec": status.get("cadical_elapsed_sec"),
                "drat_trim_exit": status.get("drat_trim_exit"),
                "drat_trim_elapsed_sec": status.get("drat_trim_elapsed_sec"),
                "drat_trim_verified": drat_ok,
                "cnf_sha256": choose_hash(status, ".cnf"),
                "drat_sha256": choose_hash(status, ".drat"),
                "input_core_cnf_sha256": choose_hash(status, ".input_core.cnf"),
            },
            "encoding_summary": {
                "primary_variables": meta["encoding"]["primary_variables"],
                "final_num_vars": meta["encoding"]["final_num_vars"],
                "num_clauses": meta["encoding"]["num_clauses"],
                "raw_relevant_rows_on_J": meta["row_filtering"]["raw_relevant_rows_on_J"],
                "unique_restricted_constraints": meta["row_filtering"]["unique_restricted_constraints"],
                "constraint_payload_sha256": meta["row_filtering"]["constraint_payload_sha256"],
            },
            "scope_warning": "This is a complete-Wang A-support cut only. It does not prove global distinct-branch infeasibility and does not establish B/C factor completion or characteristic-zero rank information.",
        }
        out = OUTDIR / f"{name}_cut_record.json"
        out.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n")
        records.append({"name": name, "record": str(out), "J_size": rec["J_size"], "cnf_sha256": rec["proof_artifacts"]["cnf_sha256"], "drat_sha256": rec["proof_artifacts"]["drat_sha256"], "drat_trim_verified": drat_ok})
    manifest = {"schema": "face_cut_records_manifest_v1", "records": records}
    (OUTDIR / "face_cut_records_manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
