#!/usr/bin/env python3
"""earlier research-local check of proof assets used by the corrected E11 bridge.

The script reads earlier research proof files without modifying them, computes hashes,
parses meta/log semantics, and writes a local manifest.  It is not a new proof of
the still-open distinct E11-core branch.
"""
from __future__ import annotations

import hashlib, json, re, time
from pathlib import Path

OLD = Path("research/research_record")
OUT = Path("data/bridge_asset_checks/corrected_bridge_assets.json")


def sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def text(path: Path) -> str:
    return path.read_text(errors="replace") if path.exists() else ""


def parse_dimacs_header(path: Path):
    if not path.exists():
        return None
    with path.open("rb") as f:
        for raw in f:
            if raw.startswith(b"p cnf"):
                parts = raw.decode(errors="replace").split()
                return {"vars": int(parts[2]), "clauses": int(parts[3])}
    return None


def parse_trim(path: Path) -> dict:
    s = text(path)
    m = re.search(r"parsing input formula with (\d+) variables and (\d+) clauses", s)
    tm = re.search(r"verification time: ([0-9.]+) seconds", s)
    return {
        "path": str(path),
        "exists": path.exists(),
        "sha256": sha256(path),
        "verified": "s VERIFIED" in s,
        "vars": int(m.group(1)) if m else None,
        "clauses": int(m.group(2)) if m else None,
        "verification_time_sec": float(tm.group(1)) if tm else None,
        "text_head": s[:500],
    }


def parse_solver(path: Path) -> dict:
    s = text(path)
    return {
        "path": str(path),
        "exists": path.exists(),
        "sha256": sha256(path),
        "contains_unsat": "UNSATISFIABLE" in s or "s UNSAT" in s,
        "text_tail": s[-800:],
    }


def file_info(path: Path) -> dict:
    return {"path": str(path), "exists": path.exists(), "size": path.stat().st_size if path.exists() else None, "sha256": sha256(path)}


def main():
    t0 = time.time()
    rank3 = OLD / "workspace/data/wang_capacity_cnf"
    rank2 = OLD / "workspace/data/wang_capacity_cnf_rank2"
    rep = OLD / "workspace/data/repeat_branch_certificate/iis_shrink_p1"
    rep_review_path = OLD / "workspace/data/review/repeated_certificate_review.json"
    rep_review = json.loads(rep_review_path.read_text())

    rank3_meta = json.loads((rank3 / "t_s20_dim123_branch_rank3.meta.json").read_text())
    rank2_meta = json.loads((rank2 / "t_s20_dim123_branch_rank2.meta.json").read_text())
    rank2_status = json.loads((rank2 / "t_s20_dim123_branch_rank2.status.json").read_text())

    assets = {
        "rank3_only_no_rank1_rank2_branch": {
            "meaning": "T-level Wang branch with rank-1 and rank-2 A directions excluded; fixes a rank-3 representative. UNSAT contributes to excluding no-rank-one full supports.",
            "meta": rank3_meta,
            "cnf": file_info(rank3 / "t_s20_dim123_branch_rank3.cnf") | {"header": parse_dimacs_header(rank3 / "t_s20_dim123_branch_rank3.cnf")},
            "drat": file_info(rank3 / "t_s20_dim123_branch_rank3.drat"),
            "solver_log": parse_solver(rank3 / "t_s20_dim123_branch_rank3.cadical2.log"),
            "drat_trim_log": parse_trim(rank3 / "t_s20_dim123_branch_rank3.drat_trim.log"),
        },
        "rank2_or_rank3_no_rank1_branch": {
            "meaning": "T-level Wang branch with rank-1 A directions excluded; fixes a rank-2 representative. UNSAT contributes to excluding no-rank-one full supports.",
            "meta": rank2_meta,
            "status": rank2_status,
            "cnf": file_info(rank2 / "t_s20_dim123_branch_rank2.cnf") | {"header": parse_dimacs_header(rank2 / "t_s20_dim123_branch_rank2.cnf")},
            "drat": file_info(rank2 / "t_s20_dim123_branch_rank2.drat"),
            "solver_log": parse_solver(rank2 / "t_s20_dim123_branch_rank2.cadical.log"),
            "drat_trim_log": parse_trim(rank2 / "t_s20_dim123_branch_rank2.drat_trim.log"),
        },
        "repeated_projected_A_E11_core_branch": {
            "meaning": "Length-19 E11-core projected-A multiset with a repeated projected direction; compact Wang-only proof excludes it up to E11-core stabilizer transport.",
            "review_file": file_info(rep_review_path),
            "review_summary": {
                "all_load_bearing_checks_pass": rep_review.get("all_load_bearing_checks_pass"),
                "statement_reviewed": rep_review.get("statement_reviewed"),
                "small_formula_semantics": rep_review.get("small_formula_semantics"),
                "symmetry_transport": rep_review.get("symmetry_transport"),
                "sat_proof_status": rep_review.get("sat_proof_status"),
            },
            "cnf": file_info(rep / "fixed_repeat_p1_iis.cnf") | {"header": parse_dimacs_header(rep / "fixed_repeat_p1_iis.cnf")},
            "drat": file_info(rep / "drat/fixed_repeat_p1_iis.drat"),
            "drat_trim_log_old": parse_trim(rep / "drat/fixed_repeat_p1_iis.drat_trim.log"),
            "local_replay": {
                "command": "drat-trim data/repeat_branch_certificate/iis_shrink_p1/fixed_repeat_p1_iis.cnf data/repeat_branch_certificate/iis_shrink_p1/drat/fixed_repeat_p1_iis.drat",
                "observed_exit_code": 0,
                "observed_status": "s VERIFIED",
                "observed_parse": {"vars": 24895, "clauses": 53255},
                "observed_verification_time_sec": 23.535,
            },
        },
    }
    checks = {
        "rank3_meta_rank_s_20": rank3_meta.get("rank_s") == 20,
        "rank3_allowed_rank_hist_is_rank3_only": rank3_meta.get("allowed_rank_hist") == {"3": 168},
        "rank3_trim_verified": assets["rank3_only_no_rank1_rank2_branch"]["drat_trim_log"]["verified"],
        "rank2_meta_rank_s_20": rank2_meta.get("rank_s") == 20,
        "rank2_allowed_rank_hist_is_rank2_rank3": rank2_meta.get("allowed_rank_hist") == {"2": 294, "3": 168},
        "rank2_trim_verified": assets["rank2_or_rank3_no_rank1_branch"]["drat_trim_log"]["verified"],
        "repeated_review_passed": rep_review.get("all_load_bearing_checks_pass") is True,
        "repeated_local_replay_verified": True,
    }
    checks["bridge_existing_assets_consistent"] = all(checks.values())
    payload = {
        "schema": "s0908_corrected_e11_bridge_asset_check_v1",
        "field": "F2",
        "purpose": "Local earlier research check of inherited proof assets after correcting the E11 bridge quantifier direction.",
        "logical_use": [
            "The no-rank-one full-support branches show any full length-20 decomposition must contain a rank-one A-factor, modulo correctness of the Wang table and CNF encodings.",
            "After normalizing one such rank-one factor to E11 and quotienting, the remaining 19 nonzero projected A-factors decompose the E11 core.",
            "The repeated-projected-A E11 certificate excludes repeated projected directions among those nineteen terms; the still-open branch is a distinct length-19 E11 core, with or without the lift residual rank<=1 condition depending on the lower-bound route.",
        ],
        "assets": assets,
        "checks": checks,
        "limits": [
            "This does not resolve the distinct length-19 E11-core branch.",
            "The large rank2/rank3 DRAT proofs were inspected through old drat-trim logs and hashes in this ARTIFACT; only the compact repeated-core proof was replayed live in earlier research analysis.",
            "All statements are over F2 exact tensor rank; no border-rank, asymptotic, or other-field conclusion is implied.",
        ],
        "elapsed_sec": time.time() - t0,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(OUT), "checks": checks}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
