#!/usr/bin/env python3
"""analysis: proof-producing CNF for lifted J65 proof-core rows with outside budget.

Input row set: the 9,469 representative full 255-point E11 Wang rows extracted
from the analysis J65 proof input core.  For an integer k, encode

  * x_p in {0,1} for all 255 E11 quotient points,
  * sum_p x_p = 19,
  * all extracted full Wang occupation rows,
  * sum_{p outside J} x_p <= k.

If UNSAT with DRAT, this proves the valid complete-Wang consequence

    sum_{p outside J} x_p >= k+1,

because every complete-Wang distinct support satisfies the extracted Wang rows.
This is not a B/C-completion result and not global E11 infeasibility unless k is
large enough to cover all possible supports.
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
OUTDIR = ROOT / "workspace/data/lifted_jcore/cnf"


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
        "tail": txt[-4000:],
    }


def load_rows():
    with USED_PKL.open("rb") as f:
        payload = pickle.load(f)
    J = [int(p) for p in payload["J"]]
    outside = [int(p) for p in payload["outside"]]
    used = list(payload["used_constraints"])
    rows = {}
    for rec in used:
        src = rec["representative_full_source"]
        bs = int(src["full_point_bitset"])
        cap = int(src["cap"])
        key = (bs, cap)
        if key not in rows:
            rows[key] = {
                "full_point_bitset": bs,
                "cap": cap,
                "row_index": int(src["row_index"]),
                "key8": int(src["key8"]),
                "dim8": int(src["dim8"]),
                "L": int(src["L"]),
                "source_core_clause_count": int(rec.get("core_clause_count", 0)),
            }
        else:
            rows[key]["source_core_clause_count"] += int(rec.get("core_clause_count", 0))
    row_list = sorted(rows.values(), key=lambda r: (r["cap"], r["full_point_bitset"].bit_count(), r["full_point_bitset"]))
    return J, outside, row_list


def run_solver(cnf: Path, timeout: int, extract_core: bool):
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
        trim_cmd = ["drat-trim", str(cnf), str(drat)]
        if extract_core:
            trim_cmd += ["-c", str(core_path)]
        t1 = time.time()
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
    for p in [cnf, cnf.with_suffix(".meta.json"), drat, cadlog, trimlog, core_path]:
        if p.exists():
            hashes[str(p)] = sha256(p)
    result["hashes"] = hashes
    cnf.with_suffix(".status.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


def parse_core_assumptions(core_path: Path, outside: Sequence[int]) -> dict:
    if not core_path.exists():
        return {}
    outside_set = set(map(int, outside))
    outside_units = []
    primary_units = []
    clause_count = 0
    unit_count = 0
    with core_path.open("r") as f:
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
                    primary_units.append(lit)
                    if lit < 0 and -lit in outside_set:
                        outside_units.append(-lit)
    return {
        "input_core_clause_count": clause_count,
        "unit_clause_count": unit_count,
        "primary_unit_count": len(primary_units),
        "primary_units": sorted(primary_units, key=lambda z: (abs(z), z)),
        "outside_negative_units_count": len(set(outside_units)),
        "outside_negative_units": sorted(set(outside_units)),
    }


def build_cnf(cnf: Path, max_outside: int) -> dict:
    t0 = time.time()
    J, outside, rows = load_rows()
    writer = CnfWriter(cnf)
    top = 255
    top, exact_ncl, exact_naux = add_card(writer, range(1, 256), "equals", 19, top)
    top, outside_ncl, outside_naux = add_card(writer, outside, "atmost", int(max_outside), top)
    row_ncl = 0
    row_naux = 0
    cap_hist = Counter()
    dim_hist = Counter()
    full_size_hist = Counter()
    for r in rows:
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
        {"mask_hex": hex(r["full_point_bitset"]), "cap": r["cap"], "row_index": r["row_index"], "key8": r["key8"]}
        for r in rows
    ], sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    meta = {
        "schema": "lifted_core_outside_cnf_meta_v1",
        "meaning": "CNF for the 9,469 lifted full Wang rows extracted from the J65 proof input core, exact support size 19, and at most k outside-J points. UNSAT+DRAT proves every complete-Wang support has at least k+1 outside-J points.",
        "rank_s": 19,
        "J_size": len(J),
        "J_points": J,
        "outside_size": len(outside),
        "outside_points": outside,
        "max_outside": int(max_outside),
        "proved_consequence_if_unsat": f"sum_{{p outside J}} x_p >= {int(max_outside) + 1}",
        "input_used_constraints": str(USED_PKL),
        "deduplicated_full_wang_row_count": len(rows),
        "row_payload_sha256": row_payload_hash,
        "row_histograms": {
            "by_cap": {str(k): int(v) for k, v in sorted(cap_hist.items())},
            "by_dim8": {str(k): int(v) for k, v in sorted(dim_hist.items())},
            "by_full_row_size": {str(k): int(v) for k, v in sorted(full_size_hist.items())},
        },
        "encoding": {
            "primary_variables": 255,
            "exact19_clauses": exact_ncl,
            "exact19_aux_vars": exact_naux,
            "outside_atmost_clauses": outside_ncl,
            "outside_atmost_aux_vars": outside_naux,
            "wang_row_clauses": row_ncl,
            "wang_row_aux_vars": row_naux,
            "num_clauses": writer.nclauses,
            "final_num_vars": top,
            "empty_clause_count": writer.empty_clause_count,
            "cardinality_encoding": "pysat CardEnc seqcounter with monotonically increasing top_id",
        },
        "cnf_path": str(cnf),
        "cnf_sha256": sha256(cnf),
        "build_elapsed_sec": round(time.time() - t0, 3),
    }
    cnf.with_suffix(".meta.json").write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n")
    return meta


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-outside", type=int, required=True)
    ap.add_argument("--solve", action="store_true")
    ap.add_argument("--solver-time", type=int, default=900)
    ap.add_argument("--extract-core", action="store_true")
    ap.add_argument("--cnf", type=Path, default=None)
    args = ap.parse_args()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    cnf = args.cnf or (OUTDIR / f"lifted_core_outside_le_{args.max_outside}.cnf")
    meta = build_cnf(cnf, args.max_outside)
    solver = None
    core_assumptions = None
    if args.solve:
        solver = run_solver(cnf, args.solver_time, args.extract_core)
        if args.extract_core and solver.get("input_core_cnf"):
            _, outside, _ = load_rows()
            core_assumptions = parse_core_assumptions(Path(solver["input_core_cnf"]), outside)
            cnf.with_suffix(".input_core_units.json").write_text(json.dumps(core_assumptions, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "cnf": str(cnf),
        "max_outside": args.max_outside,
        "rows": meta["deduplicated_full_wang_row_count"],
        "vars": meta["encoding"]["final_num_vars"],
        "clauses": meta["encoding"]["num_clauses"],
        "cnf_sha256": meta["cnf_sha256"],
        "solver": None if solver is None else {
            "cadical_exit": solver.get("cadical_exit"),
            "cadical_elapsed_sec": solver.get("cadical_elapsed_sec"),
            "drat_trim_exit": solver.get("drat_trim_exit"),
            "drat_trim_elapsed_sec": solver.get("drat_trim_elapsed_sec"),
            "drat_verified": solver.get("drat_trim_log_parse", {}).get("contains_verified"),
            "hashes": solver.get("hashes", {}),
        },
        "core_assumptions": core_assumptions,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
