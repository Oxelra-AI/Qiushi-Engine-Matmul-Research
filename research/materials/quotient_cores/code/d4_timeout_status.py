#!/usr/bin/env python3
"""Summarize the timed-out analysis d=4 local CNF proof attempt.

The managed task timed out after writing CaDiCaL and DRAT artifacts but before a
verified replay status was produced.  This records exactly what exists: CaDiCaL
log contains UNSAT, DRAT exists, but drat-trim did not write VERIFIED.  Therefore
this is not a replayed certificate at analysis.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path("research/research_record")
CNFDIR = ROOT / "workspace/data/neighborhood_repair/cnf"
TASK_RESULT = ROOT / "workspace/tasks/s54_t23_tool1/result.json"
OUT = ROOT / "workspace/data/transported_overlap/d4_partial_status_from_timeout.json"


def sha256(path: Path) -> str | None:
    if not path.exists() or not path.is_file():
        return None
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def tail_text(path: Path, n: int = 6000) -> str:
    if not path.exists() or not path.is_file() or path.stat().st_size == 0:
        return ""
    data = path.read_bytes()
    return data[-n:].decode(errors="replace")


def main() -> None:
    paths = {
        "meta": CNFDIR / "current_support_repair_d4.meta.json",
        "cnf": CNFDIR / "current_support_repair_d4.cnf",
        "cadical_log": CNFDIR / "current_support_repair_d4.cadical.log",
        "drat": CNFDIR / "current_support_repair_d4.drat",
        "drat_trim_log": CNFDIR / "current_support_repair_d4.drat_trim.log",
    }
    task = json.loads(TASK_RESULT.read_text()) if TASK_RESULT.exists() else None
    meta = json.loads(paths["meta"].read_text()) if paths["meta"].exists() else None
    cad_tail = tail_text(paths["cadical_log"], 9000)
    trim_tail = tail_text(paths["drat_trim_log"], 2000)
    result = {
        "schema": "d4_timeout_status_v1",
        "source_task": str(TASK_RESULT),
        "managed_task_state": None if task is None else task.get("state"),
        "managed_task_error": None if task is None else task.get("error"),
        "meaning": "The d=4 CaDiCaL log reached UNSAT and wrote a DRAT trace, but the managed task timed out before drat-trim verification. Treat d=4 as solver-UNSAT with unverified proof artifact until replay succeeds.",
        "artifacts": {name: {"path": str(path), "exists": path.exists(), "size": path.stat().st_size if path.exists() else None, "sha256": sha256(path)} for name, path in paths.items()},
        "meta_summary": None if meta is None else {
            "d": meta.get("d"),
            "row_count": meta.get("selected_neighborhood_row_summary", {}).get("row_count"),
            "cnf_sha256": meta.get("cnf_sha256"),
            "num_vars": meta.get("encoding", {}).get("final_num_vars"),
            "num_clauses": meta.get("encoding", {}).get("num_clauses"),
            "base_violations": meta.get("base_slack_profile_summary", {}).get("violation_count"),
        },
        "cadical_log_contains_unsat": "UNSATISFIABLE" in cad_tail,
        "cadical_log_contains_exit20": "exit 20" in cad_tail,
        "drat_trim_contains_verified": "VERIFIED" in trim_tail,
        "cadical_log_tail": cad_tail,
        "drat_trim_log_tail": trim_tail,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(OUT),
        "task_state": result["managed_task_state"],
        "cadical_unsat": result["cadical_log_contains_unsat"],
        "drat_trim_verified": result["drat_trim_contains_verified"],
        "cnf_sha256": result["artifacts"]["cnf"]["sha256"],
        "drat_sha256": result["artifacts"]["drat"]["sha256"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
