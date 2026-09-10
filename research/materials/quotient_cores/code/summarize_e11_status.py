#!/usr/bin/env python3
"""Summarize proof/support status for analysis Wang fixed-E11 branches.

This is a review aid: it does not decide tensor rank.  It records which branch
CNFs are DRAT-verified UNSAT, which are SAT only for the current cut set, and
which need further solver work.  It also hashes key files so the status can be
cross-checked by research_record or later further research.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Dict, Optional

ROOT = Path("research/research_record/workspace")


def sha256(path: Path) -> Optional[str]:
    if not path.exists() or not path.is_file():
        return None
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(4 * 1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def parse_solver_log(path: Path) -> Dict[str, object]:
    out: Dict[str, object] = {"exists": path.exists()}
    if not path.exists():
        return out
    text = path.read_text(errors="replace")
    m = re.findall(r"^s (\S+)", text, re.M)
    if m:
        out["sat_status"] = m[-1]
    m = re.findall(r"c exit ([-0-9]+)", text)
    if m:
        out["exit_line"] = int(m[-1])
    m = re.search(r"found 'p cnf (\d+) (\d+)' header", text)
    if m:
        out["parsed_header"] = {"vars": int(m.group(1)), "clauses": int(m.group(2))}
    m = re.search(r"setting time limit to ([0-9]+) seconds", text)
    if m:
        out["time_limit_sec"] = int(m.group(1))
    return out


def parse_trim_log(path: Path) -> Dict[str, object]:
    out: Dict[str, object] = {"exists": path.exists()}
    if not path.exists():
        return out
    text = path.read_text(errors="replace")
    out["verified"] = "s VERIFIED" in text
    m = re.search(r"parsing input formula with (\d+) variables and (\d+) clauses", text)
    if m:
        out["parsed_header"] = {"vars": int(m.group(1)), "clauses": int(m.group(2))}
    m = re.search(r"verification time:\s*([0-9.]+) seconds", text)
    if m:
        out["verification_time_sec"] = float(m.group(1))
    return out


def load_json(path: Path) -> Optional[dict]:
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text())
    except Exception as e:
        return {"json_error": str(e)}


def fixed_branch(rep: int, subdir: str, stem: str, model_check_stem: Optional[str] = None) -> Dict[str, object]:
    d = ROOT / "data/wang_capacity_e11_fixed" / subdir
    cnf = d / f"{stem}.cnf"
    meta = d / f"{stem}.meta.json"
    drat = d / f"{stem}.drat"
    cad = d / f"{stem}.cadical.log"
    trim = d / f"{stem}.drat_trim.log"
    status = d / f"{stem}.status.json"
    payload: Dict[str, object] = {
        "rep": rep,
        "dir": str(d),
        "stem": stem,
        "files": {p.name: {"exists": p.exists(), "size": p.stat().st_size if p.exists() else None, "sha256": sha256(p) if p.exists() else None} for p in [cnf, meta, drat, cad, trim, status]},
        "meta": load_json(meta),
        "cadical_log": parse_solver_log(cad),
        "drat_trim_log": parse_trim_log(trim),
        "status_json": load_json(status),
    }
    if model_check_stem:
        mc = d / f"{model_check_stem}.full_capacity_check.json"
        payload["model_full_capacity_check"] = load_json(mc)
    return payload


def simple_proof_branch(label: str, dir_rel: str, stem: str) -> Dict[str, object]:
    d = ROOT / dir_rel
    paths = [d / f"{stem}.cnf", d / f"{stem}.meta.json", d / f"{stem}.drat", d / f"{stem}.cadical.log", d / f"{stem}.cadical2.log", d / f"{stem}.drat_trim.log", d / f"{stem}.kissat.log", d / f"{stem}.status.json"]
    return {
        "label": label,
        "dir": str(d),
        "stem": stem,
        "files": {p.name: {"exists": p.exists(), "size": p.stat().st_size if p.exists() else None, "sha256": sha256(p) if p.exists() else None} for p in paths if p.exists()},
        "meta": load_json(d / f"{stem}.meta.json"),
        "cadical_log": parse_solver_log(d / f"{stem}.cadical.log"),
        "cadical2_log": parse_solver_log(d / f"{stem}.cadical2.log"),
        "drat_trim_log": parse_trim_log(d / f"{stem}.drat_trim.log"),
        "status_json": load_json(d / f"{stem}.status.json"),
    }


def main() -> None:
    out = {
        "meaning": "Status of Wang occupation necessary-condition branch proofs over F2 for T-level s=20. Only DRAT-verified UNSAT branches are proof objects; SAT branches are cut-set witnesses and their decoded supports must pass full LUT scans before any admissibility claim.",
        "no_rank1_branches": [
            simple_proof_branch("rank3_only", "data/wang_capacity_cnf", "t_s20_dim123_branch_rank3"),
            simple_proof_branch("rank2_or_3_no_rank1", "data/wang_capacity_cnf_rank2", "t_s20_dim123_branch_rank2"),
        ],
        "fixed_E11_second_orbit_order": [2, 10, 16, 17, 20, 84, 160, 161],
        "fixed_E11_branches": [
            fixed_branch(2, "rep_002", "t_s20_e11_rep002_dim123_seed", "t_s20_e11_rep002_dim123_seed.model"),
            fixed_branch(2, "rep_002_iter2", "t_s20_e11_rep002_iter2", "t_s20_e11_rep002_iter2.model"),
            fixed_branch(2, "rep_002_iter3", "t_s20_e11_rep002_iter3", None),
            fixed_branch(10, "rep_010", "t_s20_e11_rep010_dim123_seed", "t_s20_e11_rep010_dim123_seed.model"),
            fixed_branch(16, "rep_016", "t_s20_e11_rep016_dim123_seed", None),
            fixed_branch(16, "rep_016_retry", "t_s20_e11_rep016_dim123_seed_retry", "t_s20_e11_rep016_dim123_seed_retry.model"),
            fixed_branch(17, "rep_017", "t_s20_e11_rep017_dim123_seed", None),
            fixed_branch(20, "rep_020", "t_s20_e11_rep020_dim123_seed", None),
            fixed_branch(84, "rep_084", "t_s20_e11_rep084_dim123_seed", None),
            fixed_branch(160, "rep_160", "t_s20_e11_rep160_dim123_seed", None),
            fixed_branch(161, "rep_161", "t_s20_e11_rep161_dim123_seed", None),
        ],
        "unresolved_background_tasks": [
            {"task_ref": "s9_t61_tool1", "purpose": "drat-trim verification for rep017 existing UNSAT proof"}
        ],
    }
    outpath = ROOT / "data/wang_capacity_e11_fixed/e11_fixed_status_summary.json"
    outpath.parent.mkdir(parents=True, exist_ok=True)
    outpath.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"saved": str(outpath), "fixed_branch_records": len(out["fixed_E11_branches"])}, indent=2))


if __name__ == "__main__":
    main()
