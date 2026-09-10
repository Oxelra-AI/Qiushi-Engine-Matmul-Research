#!/usr/bin/env python3
"""analysis: proof-producing complete-Wang CNF for a general LP support face.

Given a saved fractional vector, let J be its positive support.  The CNF asks
whether there is a distinct 19-point E11 quotient A-support contained in J and
satisfying all complete Wang occupation inequalities.  UNSAT with DRAT proves
that every complete-Wang distinct support has at least one point outside J,
equivalently
    sum_{p in J} x_p <= 18.

This is a support-level finite-field consequence only.  It is not a rank-22
algorithm, not a complete F2 lower bound, and not a B/C completion statement.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, Sequence

import numpy as np
from pysat.card import CardEnc, EncType

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import ROOT, build_core_constraints  # noqa: E402

DEFAULT_TARGET = ROOT / "workspace/data/j65_transport/lp_with_transported_J65_cuts.json"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
OUTDIR = ROOT / "workspace/data/face_cnf"


def sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def sha_payload(obj) -> str:
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


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


def run_solver(cnf: Path, timeout: int, extract_core: bool = False) -> dict:
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
        trim_cmd = ["drat-trim", str(cnf), str(drat)]
        if extract_core:
            core_path = cnf.with_suffix(".input_core.cnf")
            trim_cmd += ["-c", str(core_path)]
            result["input_core_cnf"] = str(core_path)
        with trimlog.open("w") as f:
            trim = subprocess.run(trim_cmd, stdout=f, stderr=subprocess.STDOUT, text=True)
        result["drat_trim_exit"] = trim.returncode
        result["drat_trim_elapsed_sec"] = round(time.time() - t1, 3)
    else:
        result["drat_trim_exit"] = None
        result["drat_trim_elapsed_sec"] = None
    result["cadical_log_parse"] = parse_log(cadlog)
    result["drat_trim_log_parse"] = parse_log(trimlog)
    for p in [cnf, cnf.with_suffix(".meta.json"), drat, cadlog, trimlog, cnf.with_suffix(".input_core.cnf")]:
        if p.exists():
            result.setdefault("hashes", {})[str(p)] = sha256(p)
    status_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


def load_x_and_label(path: Path, run_index: int, tol: float):
    d = json.loads(path.read_text())
    if "runs" in d:
        run = d["runs"][run_index]
        coords = run.get("nonzero_coordinates")
        if coords is not None:
            x = np.zeros(255, dtype=float)
            for p, v in coords:
                x[int(p) - 1] = float(v)
        elif "x_full" in run:
            x = np.array(run["x_full"], dtype=float)
        else:
            raise ValueError(f"run {run_index} has no coordinate data")
        label = f"{path.stem}_run{run_index}_{run.get('objective_kind', 'unknown')}_{run.get('seed', 'noseed')}"
        source_meta = {"run_index": run_index, "objective_kind": run.get("objective_kind"), "seed": run.get("seed"), "sum_x": run.get("sum_x")}
    elif "global_lp" in d and "x_full" in d["global_lp"]:
        x = np.array(d["global_lp"]["x_full"], dtype=float)
        label = f"{path.stem}_global_lp"
        source_meta = {"source_kind": "global_lp"}
    elif "x_full" in d:
        x = np.array(d["x_full"], dtype=float)
        label = f"{path.stem}_xfull"
        source_meta = {"source_kind": "x_full"}
    elif "J_points" in d:
        x = np.zeros(255, dtype=float)
        for p in d["J_points"]:
            x[int(p) - 1] = 1.0
        label = f"{path.stem}_Jpoints"
        source_meta = {"source_kind": "J_points"}
    else:
        raise ValueError(f"Unsupported target JSON: {path}")
    J = [p for p in range(1, 256) if x[p - 1] > tol]
    outside = [p for p in range(1, 256) if x[p - 1] <= tol]
    return d, x, J, outside, label, source_meta


def restrict_mask_to_J(point_bitset: int, full_to_local_bit: Dict[int, int], J_full_mask: int) -> int:
    bs = int(point_bitset) & J_full_mask
    out = 0
    while bs:
        bit = bs & -bs
        p = bit.bit_length()
        out |= 1 << full_to_local_bit[p]
        bs ^= bit
    return out


def mask_lits(mask: int, var_for_local_bit: Dict[int, int]) -> list[int]:
    lits = []
    while mask:
        bit = mask & -mask
        lits.append(var_for_local_bit[bit.bit_length() - 1])
        mask ^= bit
    return lits


def build_cnf(cnf: Path, target: Path, run_index: int, tol: float) -> dict:
    t0 = time.time()
    source, x, J, outside, label, source_meta = load_x_and_label(target, run_index, tol)
    if len(J) < 19:
        raise ValueError(f"J has only {len(J)} points")
    lut, lut_meta = load_lut(LUT_PATH)
    records, complete_meta = build_core_constraints(CoreQuotient(1), lut)
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
    constraints_by_mask: Dict[int, int] = {}
    source_count_by_mask = Counter()
    strongest_source_by_mask: Dict[int, dict] = {}
    strongest_source_examples_by_cap = defaultdict(list)
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
        src = {"row_index": idx, "key8": int(rec["key8"]), "dim8": int(rec["dim8"]), "L": L, "cap": cap, "restricted_size": pop, "full_size": int(rec["point_bitset"]).bit_count()}
        if (mask not in constraints_by_mask) or (cap < constraints_by_mask[mask]):
            constraints_by_mask[mask] = cap
            strongest_source_by_mask[mask] = src
        if len(strongest_source_examples_by_cap[cap]) < 10:
            strongest_source_examples_by_cap[cap].append(src)
    constraints = [(mask, cap) for mask, cap in constraints_by_mask.items()]
    constraints.sort(key=lambda mc: (mc[1], mc[0].bit_count(), mc[0]))

    writer = CnfWriter(cnf)
    top = len(J)
    top, ncl_exact, naux_exact = add_card(writer, list(range(1, len(J) + 1)), "equals", 19, top)
    row_clause_count = 0
    row_aux_count = 0
    row_cap_hist = Counter()
    row_size_hist = Counter()
    row_source_mult_hist = Counter()
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
        row_source_mult_hist[int(source_count_by_mask[mask])] += 1
    writer.close_with_header(top)

    constraint_payload = [
        {"mask_hex": hex(mask), "cap": int(cap), "source_count": int(source_count_by_mask[mask]), "source": strongest_source_by_mask[mask]}
        for mask, cap in constraints
    ]
    meta = {
        "schema": "general_face_cnf_meta_v1",
        "meaning": "CNF for existence of a distinct 19-point support contained in the target positive support J and satisfying all complete E11-core Wang rows. UNSAT+DRAT proves the valid support cut sum_{p in J} x_p <= 18.",
        "field": "F2",
        "core": "E11 quotient core",
        "rank_s": 19,
        "target_file": str(target),
        "target_label": label,
        "source_meta": source_meta,
        "tol": tol,
        "J_size": len(J),
        "J_points": J,
        "outside_size": len(outside),
        "outside_points": outside,
        "target_mass_on_J": float(sum(x[p - 1] for p in J)),
        "target_total_mass": float(x.sum()),
        "complete_core_table_meta": complete_meta,
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "row_filtering": {
            "raw_relevant_rows_on_J": int(raw_relevant),
            "zero_intersection_rows": int(zero_intersection),
            "skipped_because_restricted_size_le_cap": int(skipped_pop_le_cap),
            "unique_restricted_constraints": int(len(constraints)),
            "deduplication_rule": "same restricted J-mask replaced by the minimum cap among complete Wang rows with that restriction; equivalent for the J-face model",
            "raw_relevant_by_dim": {str(k): int(v) for k, v in sorted(raw_by_dim.items())},
            "raw_relevant_by_L": {str(k): int(v) for k, v in sorted(raw_by_L.items())},
            "raw_relevant_restricted_size_hist": {str(k): int(v) for k, v in sorted(raw_restricted_size.items())},
            "unique_constraint_cap_hist": {str(k): int(v) for k, v in sorted(row_cap_hist.items())},
            "unique_constraint_size_hist": {str(k): int(v) for k, v in sorted(row_size_hist.items())},
            "source_multiplicity_hist_for_unique_masks_head": {str(k): int(v) for k, v in sorted(row_source_mult_hist.items())[:250]},
            "source_examples_by_cap": {str(k): v for k, v in sorted(strongest_source_examples_by_cap.items())},
            "constraint_payload_sha256": sha_payload(constraint_payload),
        },
        "encoding": {
            "primary_variables": len(J),
            "var_to_point": {str(i + 1): int(p) for i, p in enumerate(J)},
            "exact19_clauses": int(ncl_exact),
            "exact19_aux_vars": int(naux_exact),
            "wang_row_clauses": int(row_clause_count),
            "wang_row_aux_vars": int(row_aux_count),
            "num_clauses": int(writer.nclauses),
            "final_num_vars": int(top),
            "empty_clause_count": int(writer.empty_clause_count),
            "cardinality_encoding": "pysat CardEnc seqcounter with monotonically increasing top_id; at-most rows encoded only when |row cap.",
        },
        "cnf_path": str(cnf),
        "cnf_sha256": sha256(cnf),
        "build_elapsed_sec": round(time.time() - t0, 3),
    }
    cnf.with_suffix(".meta.json").write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n")
    return meta


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--target", type=Path, default=DEFAULT_TARGET)
    ap.add_argument("--run-index", type=int, default=1)
    ap.add_argument("--tol", type=float, default=1e-9)
    ap.add_argument("--name", type=str, default=None)
    ap.add_argument("--cnf", type=Path, default=None)
    ap.add_argument("--solve", action="store_true")
    ap.add_argument("--solver-time", type=int, default=900)
    ap.add_argument("--extract-core", action="store_true")
    args = ap.parse_args()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    if args.cnf is None:
        name = args.name
        if name is None:
            # Build a readable name after peeking at target label.
            _, _, J, _, label, _ = load_x_and_label(args.target, args.run_index, args.tol)
            name = f"{label}_J{len(J)}"
        args.cnf = OUTDIR / f"{name}.cnf"
    args.cnf.parent.mkdir(parents=True, exist_ok=True)
    meta = build_cnf(args.cnf, args.target, args.run_index, args.tol)
    solver = None
    if args.solve:
        solver = run_solver(args.cnf, args.solver_time, extract_core=args.extract_core)
    summary = {
        "cnf": str(args.cnf),
        "J_size": meta["J_size"],
        "target_label": meta["target_label"],
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
            "input_core_cnf": solver.get("input_core_cnf"),
            "hashes": solver.get("hashes", {}),
        },
    }
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
