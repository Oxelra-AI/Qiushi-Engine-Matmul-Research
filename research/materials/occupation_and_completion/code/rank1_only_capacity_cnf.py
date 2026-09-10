#!/usr/bin/env python3
"""Proof-producing CNF for the pure rank-1 Wang occupation branch.

The branch is the T-level s=20 necessary-condition problem over F2 in which all
20 A-side projective factors are rank-1 3x3 matrices.  There are 49 such points.
We recompute the exact compression of the full 8,283,458-row Wang LUT by
intersection with those 49 points, keep the tightest capacity for each
intersection, and encode every nonvacuous compressed row.

Unlike the older rank1_only_capacity.py CNF writer, this script uses a hybrid of
small direct forbidden-subset clauses and sequential-counter cardinality rows, so
large intersections such as (33,17) or (21,11) do not expand combinatorially.
If CaDiCaL proves UNSAT, drat-trim is run on the produced DRAT trace and the
status plus hashes are recorded.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import pickle
import shutil
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import unpack_basis, in_rowspace, matrix_rank_of_mask  # noqa: E402


def sha256(path: Path) -> str | None:
    if not path.exists() or not path.is_file():
        return None
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(4 * 1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def load_lut(path: Path):
    with path.open("rb") as f:
        payload = pickle.load(f)
    return payload["lut"], payload.get("meta", {})


def compress_rank1(lut: Dict[int, int], rank_s: int = 20):
    t0 = time.time()
    pts = [p for p in range(1, 512) if matrix_rank_of_mask(p) == 1]
    if len(pts) != 49:
        raise RuntimeError(f"expected 49 rank-1 points, got {len(pts)}")
    tight: Dict[int, int] = {}
    witness: Dict[int, int] = {}
    raw_by_dim = Counter()
    raw_by_lb = Counter()
    inter_size_raw = Counter()
    for idx, (key, lb) in enumerate(lut.items(), 1):
        basis = unpack_basis(key)
        mask = 0
        for i, p in enumerate(pts):
            if in_rowspace(p, basis, n=9):
                mask |= 1 << i
        cap = rank_s - int(lb)
        old = tight.get(mask)
        if old is None or cap < old:
            tight[mask] = cap
            witness[mask] = key
        raw_by_dim[key & 0xF] += 1
        raw_by_lb[int(lb)] += 1
        inter_size_raw[mask.bit_count()] += 1
        if idx % 1_000_000 == 0:
            print(f"compressed {idx:,}/{len(lut):,}; distinct={len(tight):,}; elapsed={time.time()-t0:.1f}s", flush=True)
    cons = [(mask, cap, witness[mask]) for mask, cap in tight.items() if mask.bit_count() > cap]
    cons.sort(key=lambda x: (x[0].bit_count(), x[1], x[0]))
    hist = Counter((m.bit_count(), cap) for m, cap, _ in cons)
    meta = {
        "rank1_points": pts,
        "raw_subspaces": len(lut),
        "compressed_intersections": len(tight),
        "nonvacuous_constraints": len(cons),
        "raw_by_dim": dict(sorted(raw_by_dim.items())),
        "raw_by_lb": dict(sorted(raw_by_lb.items())),
        "intersection_size_hist_raw": dict(sorted(inter_size_raw.items())),
        "constraint_size_cap_hist": {f"{a},{b}": c for (a, b), c in sorted(hist.items())},
        "elapsed_sec": time.time() - t0,
    }
    return pts, cons, meta


class DimacsWriter:
    def __init__(self, final_path: Path):
        self.final_path = final_path
        self.body_path = final_path.with_suffix(final_path.suffix + ".body.tmp")
        self.final_path.parent.mkdir(parents=True, exist_ok=True)
        self.fh = self.body_path.open("w")
        self.nclauses = 0
        self.empty_clause_count = 0

    def add_clause(self, clause: Sequence[int]):
        self.fh.write(" ".join(map(str, clause)) + " 0\n")
        self.nclauses += 1
        if not clause:
            self.empty_clause_count += 1

    def close_with_header(self, nv: int):
        self.fh.close()
        with self.final_path.open("w") as out:
            out.write(f"p cnf {nv} {self.nclauses}\n")
            with self.body_path.open("r") as body:
                shutil.copyfileobj(body, out, length=16 * 1024 * 1024)
        self.body_path.unlink(missing_ok=True)


def add_atmost(writer: DimacsWriter, lits: List[int], bound: int, top_id: int):
    from pysat.card import CardEnc, EncType

    if bound < 0:
        writer.add_clause([])
        return top_id, 1, 0
    if len(lits) <= bound:
        return top_id, 0, 0
    enc = CardEnc.atmost(lits=lits, bound=bound, top_id=top_id, encoding=EncType.seqcounter)
    for cl in enc.clauses:
        writer.add_clause(cl)
    return enc.nv, len(enc.clauses), max(0, enc.nv - top_id)


def encode_cnf(pts: List[int], cons: List[Tuple[int, int, int]], rank_s: int, fixed_point: int,
               cnf_path: Path, meta_path: Path, compression_meta: dict,
               direct_comb_limit: int = 2000) -> dict:
    from pysat.card import CardEnc, EncType

    t0 = time.time()
    writer = DimacsWriter(cnf_path)
    var = {p: i + 1 for i, p in enumerate(pts)}
    top_id = len(pts)
    enc = CardEnc.equals(lits=list(var.values()), bound=rank_s, top_id=top_id, encoding=EncType.seqcounter)
    for cl in enc.clauses:
        writer.add_clause(cl)
    top_id = enc.nv
    global_cardinality_clauses = len(enc.clauses)
    if fixed_point in var:
        writer.add_clause([var[fixed_point]])
    else:
        writer.add_clause([])

    direct_rows = 0
    direct_clauses = 0
    card_rows = 0
    card_clauses = 0
    aux_vars = 0
    row_size_cap_hist = Counter()
    witness_keys = []
    for mask, cap, key in cons:
        lits = [i + 1 for i in range(len(pts)) if (mask >> i) & 1]
        row_size_cap_hist[(len(lits), cap)] += 1
        combs = math.comb(len(lits), cap + 1) if 0 <= cap < len(lits) else 0
        if combs <= direct_comb_limit:
            for comb in itertools.combinations(lits, cap + 1):
                writer.add_clause([-v for v in comb])
            direct_rows += 1
            direct_clauses += combs
        else:
            old = top_id
            top_id, ncl, naux = add_atmost(writer, lits, cap, top_id)
            card_rows += 1
            card_clauses += ncl
            aux_vars += naux
            if top_id < old:
                raise RuntimeError("top_id decreased")
        if len(witness_keys) < 200:
            witness_keys.append({"intersection_size": len(lits), "cap": cap, "key": key, "dim": key & 0xF})

    writer.close_with_header(top_id)
    payload = {
        "problem": "pure rank-1 T-level Wang occupation branch CNF",
        "field": "F2",
        "rank_s": rank_s,
        "meaning": "UNSAT excludes T-level rank-20 A-supports whose twenty A-factors are all rank-1. This is a necessary-condition branch, not a tensor decomposition statement.",
        "cnf_path": str(cnf_path),
        "fixed_point": fixed_point,
        "rank1_points": pts,
        "compression": compression_meta,
        "num_vars": top_id,
        "num_clauses": writer.nclauses,
        "empty_clause_count": writer.empty_clause_count,
        "global_cardinality_clauses": global_cardinality_clauses,
        "fixed_unit_clauses": 1,
        "direct_rows": direct_rows,
        "direct_capacity_clauses": direct_clauses,
        "cardinality_capacity_rows": card_rows,
        "cardinality_capacity_clauses": card_clauses,
        "capacity_aux_vars": aux_vars,
        "direct_comb_limit": direct_comb_limit,
        "constraint_size_cap_hist": {f"{a},{b}": c for (a, b), c in sorted(row_size_cap_hist.items())},
        "witness_keys_head": witness_keys,
        "elapsed_sec": time.time() - t0,
    }
    meta_path.parent.mkdir(parents=True, exist_ok=True)
    meta_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: payload[k] for k in ["num_vars", "num_clauses", "direct_rows", "cardinality_capacity_rows", "elapsed_sec"]}, indent=2, sort_keys=True))
    return payload


def run_solver(cnf: Path, outdir: Path, time_limit: int) -> dict:
    outdir.mkdir(parents=True, exist_ok=True)
    stem = cnf.stem
    drat = outdir / f"{stem}.drat"
    cad_log = outdir / f"{stem}.cadical.log"
    trim_log = outdir / f"{stem}.drat_trim.log"
    status = {"cnf": str(cnf), "drat": str(drat), "cadical_log": str(cad_log), "drat_trim_log": str(trim_log)}
    cmd = ["cadical", "--unsat", "--binary=false", "-n"]
    if time_limit > 0:
        cmd.extend(["-t", str(time_limit)])
    cmd.extend([str(cnf), str(drat)])
    t0 = time.time()
    with cad_log.open("w") as log:
        proc = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, text=True)
    status["cadical_exit"] = proc.returncode
    status["cadical_elapsed_sec"] = time.time() - t0
    if proc.returncode == 20:
        t1 = time.time()
        with trim_log.open("w") as log:
            trim = subprocess.run(["drat-trim", str(cnf), str(drat)], stdout=log, stderr=subprocess.STDOUT, text=True)
        status["drat_trim_exit"] = trim.returncode
        status["drat_trim_elapsed_sec"] = time.time() - t1
    else:
        status["drat_trim_exit"] = None
    status["hashes"] = {p.name: sha256(p) for p in [cnf, cnf.with_suffix(cnf.suffix.replace('.cnf','') + '.meta.json') if False else cnf, drat, cad_log, trim_log] if p.exists()}
    status_path = outdir / f"{stem}.status.json"
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps(status, indent=2, sort_keys=True))
    return status


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--rank", type=int, default=20)
    ap.add_argument("--fixed-point", type=int, default=1)
    ap.add_argument("--cnf", type=Path, required=True)
    ap.add_argument("--meta", type=Path, required=True)
    ap.add_argument("--out", type=Path, default=None)
    ap.add_argument("--direct-comb-limit", type=int, default=2000)
    ap.add_argument("--solve", action="store_true")
    ap.add_argument("--solver-time", type=int, default=0)
    args = ap.parse_args()

    lut, lut_meta = load_lut(args.lut)
    print(f"loaded LUT {len(lut):,} coverage={lut_meta.get('coverage_ok')} conflicts={lut_meta.get('conflict_count')}")
    pts, cons, compression_meta = compress_rank1(lut, args.rank)
    payload = encode_cnf(pts, cons, args.rank, args.fixed_point, args.cnf, args.meta, compression_meta, args.direct_comb_limit)
    payload["lut_meta_brief"] = {"coverage_ok": lut_meta.get("coverage_ok"), "conflict_count": lut_meta.get("conflict_count"), "subspace_count": lut_meta.get("subspace_count")}
    if args.solve:
        status = run_solver(args.cnf, args.cnf.parent, args.solver_time)
        payload["solver_status"] = status
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
