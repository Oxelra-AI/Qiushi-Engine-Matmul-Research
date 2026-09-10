#!/usr/bin/env python3
"""analysis: lift the J65 proof core to 255 variables and recover outside assumptions.

analysis proved no complete-Wang support is contained in the 65-point LP support
J.  analysis first mapped the DRAT input core to 9,469 restricted Wang
constraints.  This script lifts those restricted constraints back to their
representative full 255-point E11 Wang rows, adds exact cardinality 19 and
outside-zero assumptions, and obtains a new DRAT-verified proof.  The primary
purpose is to inspect which outside-zero assumptions enter an input core.  If
only K subset of outside directions is needed, then the verified formula with
units {not x_p : p in K} proves the stronger occupation consequence

    sum_{p in K} x_p >= 1

for every binary distinct 19-support satisfying the complete E11 Wang table
(since the proof uses only valid Wang rows plus cardinality).

The K obtained here is proof-dependent and not claimed minimal.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import shutil
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

from pysat.card import CardEnc, EncType

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from complete_core_and_transversal import ROOT  # noqa: E402

USED_PKL = ROOT / "workspace/data/jface_core/J65_core_used_constraints.pkl"
OUTDIR = ROOT / "workspace/data/lifted_jcore"


def sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


class CnfWriter:
    def __init__(self, path: Path):
        self.path = path
        self.body = path.with_suffix(path.suffix + ".body")
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.fh = self.body.open("w")
        self.nclauses = 0
        self.empty_clause_count = 0

    def add_clause(self, lits: Sequence[int]):
        lits = [int(x) for x in lits if int(x) != 0]
        if not lits:
            self.empty_clause_count += 1
        self.fh.write(" ".join(str(x) for x in lits) + " 0\n")
        self.nclauses += 1

    def add_clauses(self, clauses: Iterable[Sequence[int]]) -> int:
        n = 0
        for cl in clauses:
            self.add_clause(cl)
            n += 1
        return n

    def close(self, nv: int):
        self.fh.close()
        with self.path.open("w") as out:
            out.write(f"p cnf {int(nv)} {int(self.nclauses)}\n")
            with self.body.open("r") as f:
                shutil.copyfileobj(f, out, length=16 * 1024 * 1024)
        try:
            self.body.unlink()
        except FileNotFoundError:
            pass


def add_card(writer: CnfWriter, lits: Sequence[int], relation: str, bound: int, top: int):
    lits = list(map(int, lits))
    if relation == "atmost":
        if bound < 0:
            writer.add_clause([])
            return top, 1, 0
        if len(lits) <= bound:
            return top, 0, 0
        if bound == 0:
            for lit in lits:
                writer.add_clause([-lit])
            return top, len(lits), 0
        enc = CardEnc.atmost(lits=lits, bound=int(bound), top_id=int(top), encoding=EncType.seqcounter)
    elif relation == "atleast":
        if bound <= 0:
            return top, 0, 0
        if len(lits) < bound:
            writer.add_clause([])
            return top, 1, 0
        if len(lits) == bound:
            for lit in lits:
                writer.add_clause([lit])
            return top, len(lits), 0
        enc = CardEnc.atleast(lits=lits, bound=int(bound), top_id=int(top), encoding=EncType.seqcounter)
    elif relation == "equals":
        if bound < 0 or bound > len(lits):
            writer.add_clause([])
            return top, 1, 0
        enc = CardEnc.equals(lits=lits, bound=int(bound), top_id=int(top), encoding=EncType.seqcounter)
    else:
        raise ValueError(relation)
    ncl = writer.add_clauses(enc.clauses)
    ntop = max(int(top), int(enc.nv))
    return ntop, ncl, max(0, ntop - int(top))


def full_points_from_bitset(bs: int) -> list[int]:
    pts = []
    bs = int(bs)
    while bs:
        bit = bs & -bs
        pts.append(bit.bit_length())
        bs ^= bit
    return pts


def parse_log(path: Path) -> dict:
    if not path.exists():
        return {}
    txt = path.read_text(errors="replace")
    return {
        "contains_unsat": "UNSATISFIABLE" in txt,
        "contains_sat": ("SATISFIABLE" in txt and "UNSATISFIABLE" not in txt),
        "contains_verified": "VERIFIED" in txt,
        "tail": txt[-3000:],
    }


def run_cadical_and_trim(cnf: Path, timeout: int, extract_core: bool) -> dict:
    drat = cnf.with_suffix(".drat")
    cadlog = cnf.with_suffix(".cadical.log")
    trimlog = cnf.with_suffix(".drat_trim.log")
    core_path = cnf.with_suffix(".input_core.cnf")
    cmd = ["cadical", "--unsat", "--binary=false", "-n"]
    if timeout and timeout > 0:
        cmd += ["-t", str(int(timeout))]
    cmd += [str(cnf), str(drat)]
    t0 = time.time()
    with cadlog.open("w") as f:
        proc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, text=True)
    result = {
        "cnf": str(cnf),
        "drat": str(drat),
        "cadical_log": str(cadlog),
        "drat_trim_log": str(trimlog),
        "input_core_cnf": str(core_path) if extract_core else None,
        "cadical_exit": proc.returncode,
        "cadical_elapsed_sec": round(time.time() - t0, 3),
    }
    if proc.returncode == 20:
        t1 = time.time()
        trim_cmd = ["drat-trim", str(cnf), str(drat)]
        if extract_core:
            trim_cmd += ["-c", str(core_path)]
        with trimlog.open("w") as f:
            trim = subprocess.run(trim_cmd, stdout=f, stderr=subprocess.STDOUT, text=True)
        result["drat_trim_exit"] = trim.returncode
        result["drat_trim_elapsed_sec"] = round(time.time() - t1, 3)
    else:
        result["drat_trim_exit"] = None
        result["drat_trim_elapsed_sec"] = None
    result["cadical_log_parse"] = parse_log(cadlog)
    result["drat_trim_log_parse"] = parse_log(trimlog)
    hashes = {}
    for p in [cnf, drat, cadlog, trimlog, core_path]:
        if p.exists():
            hashes[str(p)] = sha256(p)
    result["hashes"] = hashes
    cnf.with_suffix(".status.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


def parse_input_core_units(path: Path, outside: Sequence[int]):
    outside_set = set(map(int, outside))
    primary_neg_units = []
    primary_pos_units = []
    all_primary_units = []
    unit_count = 0
    clause_count = 0
    with path.open("r") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("c") or line.startswith("p"):
                continue
            lits = []
            for tok in line.split():
                lit = int(tok)
                if lit == 0:
                    break
                lits.append(lit)
            clause_count += 1
            if len(lits) == 1:
                unit_count += 1
                lit = lits[0]
                if abs(lit) <= 255:
                    all_primary_units.append(lit)
                    if lit < 0 and -lit in outside_set:
                        primary_neg_units.append(-lit)
                    elif lit > 0:
                        primary_pos_units.append(lit)
    return {
        "input_core_clause_count": clause_count,
        "unit_clause_count": unit_count,
        "primary_unit_count": len(all_primary_units),
        "primary_units": sorted(all_primary_units, key=lambda z: (abs(z), z)),
        "outside_negative_unit_count": len(set(primary_neg_units)),
        "outside_negative_units_K": sorted(set(primary_neg_units)),
        "primary_positive_units": sorted(primary_pos_units),
    }


def load_used():
    with USED_PKL.open("rb") as f:
        payload = pickle.load(f)
    return payload


def build_formula(cnf: Path, unit_zero_points: Sequence[int], row_mode: str = "used") -> dict:
    t0 = time.time()
    payload = load_used()
    J = [int(p) for p in payload["J"]]
    outside = [int(p) for p in payload["outside"]]
    used = list(payload["used_constraints"])
    # Deduplicate representative full Wang rows by exact full point set and cap.
    full_rows = {}
    for rec in used:
        src = rec["representative_full_source"]
        bs = int(src["full_point_bitset"])
        cap = int(src["cap"])
        key = (bs, cap)
        if key not in full_rows:
            full_rows[key] = {
                "full_point_bitset": bs,
                "cap": cap,
                "row_index": int(src["row_index"]),
                "key8": int(src["key8"]),
                "dim8": int(src["dim8"]),
                "L": int(src["L"]),
                "restricted_size": int(rec["restricted_size"]),
                "source_core_clause_count": int(rec["core_clause_count"]),
            }
        else:
            full_rows[key]["source_core_clause_count"] += int(rec["core_clause_count"])
    row_list = sorted(full_rows.values(), key=lambda r: (r["cap"], r["full_point_bitset"].bit_count(), r["full_point_bitset"]))
    writer = CnfWriter(cnf)
    top = 255
    top, exact_ncl, exact_naux = add_card(writer, list(range(1, 256)), "equals", 19, top)
    for p in sorted(set(map(int, unit_zero_points))):
        writer.add_clause([-int(p)])
    row_ncl = 0
    row_naux = 0
    cap_hist = Counter()
    dim_hist = Counter()
    full_size_hist = Counter()
    for r in row_list:
        pts = full_points_from_bitset(r["full_point_bitset"])
        old_top = top
        top, ncl, naux = add_card(writer, pts, "atmost", int(r["cap"]), top)
        if top < old_top:
            raise RuntimeError("top decreased")
        row_ncl += ncl
        row_naux += naux
        cap_hist[int(r["cap"])] += 1
        dim_hist[int(r["dim8"])] += 1
        full_size_hist[len(pts)] += 1
    writer.close(top)
    row_payload_hash = hashlib.sha256(json.dumps([
        {"full_mask_hex": hex(r["full_point_bitset"]), "cap": r["cap"], "row_index": r["row_index"], "key8": r["key8"]}
        for r in row_list
    ], sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    unit_hash = hashlib.sha256(json.dumps(sorted(set(map(int, unit_zero_points))), separators=(",", ":")).encode()).hexdigest()
    meta = {
        "schema": "lifted_jcore_formula_meta_v1",
        "meaning": "Full-255-variable CNF using exact cardinality 19, selected full E11 Wang rows that generated the J65 input proof core, and a specified set of outside-zero unit assumptions. UNSAT+DRAT proves every complete-Wang support uses at least one point from the unit-zero set.",
        "J_size": len(J),
        "J_points": J,
        "outside_size": len(outside),
        "unit_zero_count": len(set(map(int, unit_zero_points))),
        "unit_zero_points": sorted(set(map(int, unit_zero_points))),
        "used_restricted_constraint_count": len(used),
        "deduplicated_full_wang_row_count": len(row_list),
        "row_payload_sha256": row_payload_hash,
        "unit_zero_points_sha256": unit_hash,
        "encoding": {
            "primary_variables": 255,
            "exact19_clauses": exact_ncl,
            "exact19_aux_vars": exact_naux,
            "unit_zero_clauses": len(set(map(int, unit_zero_points))),
            "wang_row_clauses": row_ncl,
            "wang_row_aux_vars": row_naux,
            "num_clauses": writer.nclauses,
            "final_num_vars": top,
            "empty_clause_count": writer.empty_clause_count,
            "cardinality_encoding": "pysat CardEnc seqcounter with monotonically increasing top_id",
        },
        "row_histograms": {
            "by_cap": {str(k): int(v) for k, v in sorted(cap_hist.items())},
            "by_dim8": {str(k): int(v) for k, v in sorted(dim_hist.items())},
            "by_full_row_size": {str(k): int(v) for k, v in sorted(full_size_hist.items())},
        },
        "cnf_path": str(cnf),
        "cnf_sha256": sha256(cnf),
        "build_elapsed_sec": round(time.time() - t0, 3),
    }
    cnf.with_suffix(".meta.json").write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n")
    return meta


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--solver-time", type=int, default=600)
    ap.add_argument("--skip-reduced", action="store_true")
    args = ap.parse_args()
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    payload = load_used()
    outside = [int(p) for p in payload["outside"]]

    all_cnf = OUTDIR / "lifted_used_rows_all190_units.cnf"
    print("building all-unit lifted formula", flush=True)
    all_meta = build_formula(all_cnf, outside)
    print(json.dumps({"cnf": str(all_cnf), "clauses": all_meta["encoding"]["num_clauses"], "vars": all_meta["encoding"]["final_num_vars"], "rows": all_meta["deduplicated_full_wang_row_count"]}, indent=2), flush=True)
    all_status = run_cadical_and_trim(all_cnf, args.solver_time, extract_core=True)
    print(json.dumps({"all_units_cadical_exit": all_status["cadical_exit"], "trim_verified": all_status.get("drat_trim_log_parse", {}).get("contains_verified"), "trim_sec": all_status.get("drat_trim_elapsed_sec")}, indent=2), flush=True)
    unit_core = None
    reduced_meta = None
    reduced_status = None
    if all_status.get("drat_trim_exit") == 0 and all_status.get("input_core_cnf"):
        unit_core = parse_input_core_units(Path(all_status["input_core_cnf"]), outside)
        K = unit_core["outside_negative_units_K"]
        (OUTDIR / "lifted_used_rows_all190_units_core_units.json").write_text(json.dumps(unit_core, indent=2, sort_keys=True) + "\n")
        print(json.dumps({"K_size_from_input_core": len(K), "K_head": K[:40], "primary_positive_units": unit_core["primary_positive_units"][:20]}, indent=2), flush=True)
        if (not args.skip_reduced) and len(K) < len(outside):
            red_cnf = OUTDIR / f"lifted_used_rows_K{len(K)}_units.cnf"
            print("building reduced-K formula", flush=True)
            reduced_meta = build_formula(red_cnf, K)
            print(json.dumps({"cnf": str(red_cnf), "clauses": reduced_meta["encoding"]["num_clauses"], "vars": reduced_meta["encoding"]["final_num_vars"], "K": len(K)}, indent=2), flush=True)
            reduced_status = run_cadical_and_trim(red_cnf, args.solver_time, extract_core=False)
            print(json.dumps({"reduced_cadical_exit": reduced_status["cadical_exit"], "trim_verified": reduced_status.get("drat_trim_log_parse", {}).get("contains_verified"), "trim_sec": reduced_status.get("drat_trim_elapsed_sec")}, indent=2), flush=True)
    summary = {
        "schema": "lifted_jcore_assumption_min_summary_v1",
        "meaning": "Lifts the J-face proof-core rows to valid 255-point Wang rows and checks whether fewer outside-zero assumptions suffice for UNSAT. Any DRAT-verified reduced-K formula proves sum_{p in K} x_p >= 1 for complete-Wang distinct 19-supports; K is proof-dependent and not minimal.",
        "input_used_constraints": str(USED_PKL),
        "all_units_formula_meta": str(all_cnf.with_suffix(".meta.json")),
        "all_units_status": str(all_cnf.with_suffix(".status.json")),
        "all_units_cadical_exit": all_status.get("cadical_exit"),
        "all_units_drat_verified": all_status.get("drat_trim_log_parse", {}).get("contains_verified"),
        "unit_core_file": str(OUTDIR / "lifted_used_rows_all190_units_core_units.json") if unit_core else None,
        "K_size_from_input_core": None if unit_core is None else len(unit_core["outside_negative_units_K"]),
        "K_points_from_input_core": None if unit_core is None else unit_core["outside_negative_units_K"],
        "reduced_formula_meta": None if reduced_meta is None else str(Path(reduced_meta["cnf_path"]).with_suffix(".meta.json")),
        "reduced_status": None if reduced_status is None else str(Path(reduced_status["cnf"]).with_suffix(".status.json")),
        "reduced_cadical_exit": None if reduced_status is None else reduced_status.get("cadical_exit"),
        "reduced_drat_verified": None if reduced_status is None else reduced_status.get("drat_trim_log_parse", {}).get("contains_verified"),
        "elapsed_sec": round(time.time() - t0, 3),
    }
    (OUTDIR / "lifted_jcore_assumption_min_summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
