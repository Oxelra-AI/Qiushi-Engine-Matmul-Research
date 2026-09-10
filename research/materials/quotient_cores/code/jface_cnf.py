#!/usr/bin/env python3
"""Proof-producing CNF for the analysis LP-support J face.

Let J be the set of the 65 nonzero coordinates of the saved fractional complete
E11-Wang LP solution.  This CNF asks whether there is a distinct 19-point
support contained in J satisfying the complete E11 quotient Wang occupation
rows.  UNSAT with DRAT proves the valid Wang-support consequence

    sum_{p outside J} x_p >= 1.

This does not prove global E11 infeasibility; it only separates the saved
fractional point and records a replayable integer cut for future models.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np
from pysat.card import CardEnc, EncType

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import ROOT, build_core_constraints

OUTDIR = ROOT / "workspace/data/global_J_face/cnf"
GLOBAL_PATH = ROOT / "workspace/data/local_hull/global_fractional_solution.json"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"


def sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


class CnfWriter:
    def __init__(self, final_path: Path):
        self.final_path = final_path
        self.body_path = final_path.with_suffix(final_path.suffix + ".body")
        self.body_path.parent.mkdir(parents=True, exist_ok=True)
        self.fh = self.body_path.open("w")
        self.nclauses = 0
        self.empty_clause_count = 0

    def add_clause(self, lits: Sequence[int]) -> None:
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

    def close_with_header(self, nv: int) -> None:
        self.fh.close()
        with self.final_path.open("w") as out:
            out.write(f"p cnf {int(nv)} {int(self.nclauses)}\n")
            with self.body_path.open("r") as body:
                shutil.copyfileobj(body, out, length=16 * 1024 * 1024)
        try:
            self.body_path.unlink()
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
    new_top = max(int(top), int(enc.nv))
    return new_top, ncl, max(0, new_top - int(top))


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


def run_solver(cnf: Path, timeout: int) -> dict:
    drat = cnf.with_suffix(".drat")
    cadlog = cnf.with_suffix(".cadical.log")
    trimlog = cnf.with_suffix(".drat_trim.log")
    status_path = cnf.with_suffix(".status.json")
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
        "cadical_exit": proc.returncode,
        "cadical_elapsed_sec": round(time.time() - t0, 3),
    }
    if proc.returncode == 20:
        t1 = time.time()
        with trimlog.open("w") as f:
            trim = subprocess.run(["drat-trim", str(cnf), str(drat)], stdout=f, stderr=subprocess.STDOUT, text=True)
        result["drat_trim_exit"] = trim.returncode
        result["drat_trim_elapsed_sec"] = round(time.time() - t1, 3)
    else:
        result["drat_trim_exit"] = None
        result["drat_trim_elapsed_sec"] = None
    result["cadical_log_parse"] = parse_log(cadlog)
    result["drat_trim_log_parse"] = parse_log(trimlog)
    for p in [cnf, cnf.with_suffix(".meta.json"), drat, cadlog, trimlog]:
        if p.exists():
            result.setdefault("hashes", {})[str(p)] = sha256(p)
    status_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


def load_J(tol: float = 1e-10):
    data = json.loads(GLOBAL_PATH.read_text())
    x = np.array(data["global_lp"]["x_full"], dtype=float)
    J = [p for p in range(1, 256) if x[p - 1] > tol]
    outside = [p for p in range(1, 256) if x[p - 1] <= tol]
    return x, J, outside, data


def restrict_mask_to_J(point_bitset: int, full_to_local_bit: Dict[int, int], J_full_mask: int) -> int:
    bs = int(point_bitset) & J_full_mask
    out = 0
    while bs:
        bit = bs & -bs
        p = bit.bit_length()  # bit for point p is at p-1, so bit_length gives p
        out |= 1 << full_to_local_bit[p]
        bs ^= bit
    return out


def mask_lits(mask: int, var_for_local_bit: Dict[int, int]) -> List[int]:
    lits = []
    while mask:
        bit = mask & -mask
        lits.append(var_for_local_bit[bit.bit_length() - 1])
        mask ^= bit
    return lits


def build_cnf(cnf: Path, deduplicate: bool = True) -> dict:
    t0 = time.time()
    x, J, outside, global_data = load_J()
    lut, lut_meta = load_lut(LUT_PATH)
    records, meta = build_core_constraints(CoreQuotient(1), lut)
    full_to_local_bit = {p: i for i, p in enumerate(J)}
    var_for_local_bit = {i: i + 1 for i in range(len(J))}
    J_full_mask = 0
    for p in J:
        J_full_mask |= 1 << (p - 1)

    raw_relevant = 0
    raw_by_dim = Counter()
    raw_by_L = Counter()
    raw_restricted_size = Counter()
    skipped_pop_le_cap = 0
    zero_intersection = 0
    # constraints_by_mask[mask] = strongest cap for this restricted point set.
    constraints_by_mask: Dict[int, int] = {}
    source_count_by_mask = Counter()
    strongest_source_by_mask: Dict[int, dict] = {}
    for idx, rec in enumerate(records):
        L = int(rec["L"])
        cap = 19 - L
        if cap >= 19:
            continue
        mask = restrict_mask_to_J(int(rec["point_bitset"]), full_to_local_bit, J_full_mask)
        pop = mask.bit_count()
        if pop == 0:
            zero_intersection += 1
            continue
        if pop <= cap:
            skipped_pop_le_cap += 1
            continue
        raw_relevant += 1
        raw_by_dim[int(rec["dim8"])] += 1
        raw_by_L[L] += 1
        raw_restricted_size[pop] += 1
        source_count_by_mask[mask] += 1
        if (mask not in constraints_by_mask) or (cap < constraints_by_mask[mask]):
            constraints_by_mask[mask] = cap
            strongest_source_by_mask[mask] = {"row_index": idx, "key8": int(rec["key8"]), "dim8": int(rec["dim8"]), "L": L, "cap": cap, "restricted_size": pop}

    constraints = [(mask, cap) for mask, cap in constraints_by_mask.items()]
    # Sort for stable hash and independent reproducibility.
    constraints.sort(key=lambda mc: (mc[1], mc[0].bit_count(), mc[0]))

    writer = CnfWriter(cnf)
    top = len(J)
    top, ncl_exact, naux_exact = add_card(writer, list(range(1, len(J) + 1)), "equals", 19, top)
    row_clause_count = 0
    row_aux_count = 0
    row_cap_hist = Counter()
    row_size_hist = Counter()
    row_source_multiplicity_hist = Counter()
    for mask, cap in constraints:
        lits = mask_lits(mask, var_for_local_bit)
        old_top = top
        top, ncl, naux = add_card(writer, lits, "atmost", int(cap), top)
        if top < old_top:
            raise RuntimeError("top variable id decreased")
        row_clause_count += ncl
        row_aux_count += naux
        row_cap_hist[int(cap)] += 1
        row_size_hist[len(lits)] += 1
        row_source_multiplicity_hist[source_count_by_mask[mask]] += 1
    writer.close_with_header(top)

    constraint_hash_payload = [
        {"mask_hex": hex(mask), "cap": int(cap), "source_count": int(source_count_by_mask[mask]), "source": strongest_source_by_mask[mask]}
        for mask, cap in constraints
    ]
    h = hashlib.sha256(json.dumps(constraint_hash_payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    meta_payload = {
        "schema": "jface_cnf_meta_v1",
        "meaning": "CNF for existence of a 19-point support contained in J satisfying the complete E11-core Wang occupation rows. UNSAT+DRAT proves every complete-Wang support has at least one point outside J.",
        "field": "F2",
        "core": "E11 quotient core",
        "rank_s": 19,
        "global_solution_file": str(GLOBAL_PATH),
        "J_size": len(J),
        "J_points": J,
        "outside_size": len(outside),
        "outside_points": outside,
        "complete_core_table_meta": meta,
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "row_filtering": {
            "raw_relevant_rows_on_J": raw_relevant,
            "zero_intersection_rows": zero_intersection,
            "skipped_because_restricted_size_le_cap": skipped_pop_le_cap,
            "unique_restricted_constraints": len(constraints),
            "deduplication_rule": "same restricted J-mask replaced by the minimum cap among complete Wang rows with that restriction; equivalent for the J-face model",
            "raw_relevant_by_dim": {str(k): int(v) for k, v in sorted(raw_by_dim.items())},
            "raw_relevant_by_L": {str(k): int(v) for k, v in sorted(raw_by_L.items())},
            "raw_relevant_restricted_size_hist": {str(k): int(v) for k, v in sorted(raw_restricted_size.items())},
            "unique_constraint_cap_hist": {str(k): int(v) for k, v in sorted(row_cap_hist.items())},
            "unique_constraint_size_hist": {str(k): int(v) for k, v in sorted(row_size_hist.items())},
            "source_multiplicity_hist_for_unique_masks": {str(k): int(v) for k, v in sorted(row_source_multiplicity_hist.items())[:200]},
            "constraint_payload_sha256": h,
        },
        "encoding": {
            "primary_variables": len(J),
            "var_to_point": {str(i + 1): int(p) for i, p in enumerate(J)},
            "exact19_clauses": ncl_exact,
            "exact19_aux_vars": naux_exact,
            "wang_row_clauses": row_clause_count,
            "wang_row_aux_vars": row_aux_count,
            "num_clauses": writer.nclauses,
            "final_num_vars": top,
            "empty_clause_count": writer.empty_clause_count,
            "cardinality_encoding": "pysat CardEnc seqcounter with monotonically increasing top_id; at-most rows encoded only when |row∩J| > cap",
        },
        "cnf_path": str(cnf),
        "cnf_sha256": sha256(cnf),
        "build_elapsed_sec": round(time.time() - t0, 3),
    }
    cnf.with_suffix(".meta.json").write_text(json.dumps(meta_payload, indent=2, sort_keys=True) + "\n")
    return meta_payload


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cnf", type=Path, default=OUTDIR / "J65_complete_wang.cnf")
    ap.add_argument("--solve", action="store_true")
    ap.add_argument("--solver-time", type=int, default=600)
    args = ap.parse_args()
    args.cnf.parent.mkdir(parents=True, exist_ok=True)
    meta = build_cnf(args.cnf)
    solver = None
    if args.solve:
        solver = run_solver(args.cnf, args.solver_time)
    print(json.dumps({
        "cnf": str(args.cnf),
        "J_size": meta["J_size"],
        "raw_relevant_rows_on_J": meta["row_filtering"]["raw_relevant_rows_on_J"],
        "unique_restricted_constraints": meta["row_filtering"]["unique_restricted_constraints"],
        "num_vars": meta["encoding"]["final_num_vars"],
        "num_clauses": meta["encoding"]["num_clauses"],
        "cnf_sha256": meta["cnf_sha256"],
        "solver": None if solver is None else {
            "cadical_exit": solver["cadical_exit"],
            "cadical_elapsed_sec": solver["cadical_elapsed_sec"],
            "drat_trim_exit": solver.get("drat_trim_exit"),
            "drat_trim_elapsed_sec": solver.get("drat_trim_elapsed_sec"),
            "drat_verified": solver.get("drat_trim_log_parse", {}).get("contains_verified"),
            "hashes": solver.get("hashes", {}),
        },
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
