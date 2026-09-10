#!/usr/bin/env python3
"""Generate compact DRAT-checkable CNF certificates for dim-2 occupation raises.

The integer occupation system for a fixed dim-2 W at target L=18 is:
  x_q >= 0 integer, sum_q x_q = 18,
  sum_{q in V} x_q <= 18 - LB(W+V) for every nonzero proper quotient subspace V.

Singleton rows give small upper bounds for each q.  We encode an integer variable
x_q with upper bound u_q by u_q Boolean copies.  A row sums all copies belonging
to q in its mask.  This is equisatisfiable with the integer model because all
constraints depend only on counts and all coefficients are 0/1.

Rows and caps are rebuilt through dim2_independent_semantics, not the
older node-local builder.  The emitted DIMACS plus a checked DRAT proof is a
machine-checkable certificate for the raise for that W.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import pickle
import shutil
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from dim2_independent_semantics import (  # type: ignore
    LUT_PATH, CACHE_PATH, rref_ind, independent_rows, popcount, file_sha256
)

OUTDIR = Path("data/dim2_cnf_cert")

try:
    from pysat.card import CardEnc, EncType  # type: ignore
    from pysat.formula import IDPool  # type: ignore
except Exception as e:  # pragma: no cover
    CardEnc = None
    EncType = None
    IDPool = None


def load_lut_orbits():
    with LUT_PATH.open("rb") as f:
        data = pickle.load(f)
    lut = data["lut"] if isinstance(data, dict) and "lut" in data else data
    with CACHE_PATH.open("rb") as f:
        cache = pickle.load(f)
    return lut, {int(o["cert_index"]): o for o in cache["orbits"]}


def atmost_clauses(lits: Sequence[int], bound: int, pool) -> List[List[int]]:
    lits = list(dict.fromkeys(int(x) for x in lits))
    if bound < 0:
        return [[]]
    if len(lits) <= bound:
        return []
    if bound == 0:
        return [[-x] for x in lits]
    enc = CardEnc.atmost(lits=lits, bound=int(bound), vpool=pool, encoding=EncType.seqcounter)
    return [list(map(int, c)) for c in enc.clauses]


def atleast_clauses(lits: Sequence[int], bound: int, pool) -> List[List[int]]:
    lits = list(dict.fromkeys(int(x) for x in lits))
    # sum lits >= bound  <=> sum not(lits) <= len(lits)-bound
    if bound <= 0:
        return []
    if bound > len(lits):
        return [[]]
    return atmost_clauses([-x for x in lits], len(lits) - int(bound), pool)


def build_cnf_for_orbit(idx: int, target: int, outdir: Path, run_solver: bool, cadical_timeout: int, drat_trim_timeout: int) -> Dict:
    if CardEnc is None:
        raise RuntimeError("python-sat/pysat CardEnc unavailable")
    lut, orbit_by_idx = load_lut_orbits()
    orb = orbit_by_idx[idx]
    W = rref_ind([int(x) for x in orb["basis"]], 9)
    raw_lb = int(orb["raw_lb"])
    rows, row_meta = independent_rows(W, lut, target)
    k = row_meta["quotient_dim"]
    npts = (1 << k) - 1

    # Singleton caps give exact finite domains; keep strongest cap per q.
    ub = [target] * (npts + 1)
    singleton_sources = {}
    for row_i, (mask, cap) in enumerate(rows):
        if popcount(mask) == 1:
            q = int(mask).bit_length()  # mask has bit q-1 set, so q=bit_length
            if int(cap) < ub[q]:
                ub[q] = int(cap)
                singleton_sources[q] = row_i
    # No variable can exceed target anyway; negative caps make immediate UNSAT.
    active_q = [q for q in range(1, npts + 1) if ub[q] > 0]
    upper_hist = Counter(ub[q] for q in range(1, npts + 1))

    pool = IDPool()
    copies: Dict[int, List[int]] = {}
    for q in range(1, npts + 1):
        copies[q] = [pool.id(f"x_{q}_{j}") for j in range(1, max(0, min(ub[q], target)) + 1)]

    clauses: List[List[int]] = []
    row_clause_counts = []
    row_copy_pop_hist = Counter()
    active_rows = 0
    immediate_empty = 0

    all_lits = [lit for q in range(1, npts + 1) for lit in copies[q]]
    # Cardinality equality sum copies = target.
    c1 = atmost_clauses(all_lits, target, pool)
    c2 = atleast_clauses(all_lits, target, pool)
    clauses.extend(c1); clauses.extend(c2)

    # Encode all row upper bounds after expanding integer variables to copies.
    seen_row_constraints = set()
    for mask, cap in rows:
        lits = []
        m = int(mask)
        while m:
            low = m & -m
            q = low.bit_length()  # q in 1..npts
            lits.extend(copies[q])
            m ^= low
        lits = sorted(set(lits))
        row_copy_pop_hist[len(lits)] += 1
        # If all variable copies in this row are at most cap, it is tautological
        # in the finite domain.  Otherwise encode.  Deduplicate identical rows.
        if cap < 0:
            clauses.append([])
            immediate_empty += 1
            continue
        if len(lits) <= int(cap):
            continue
        key = (tuple(lits), int(cap))
        if key in seen_row_constraints:
            continue
        seen_row_constraints.add(key)
        before = len(clauses)
        clauses.extend(atmost_clauses(lits, int(cap), pool))
        row_clause_counts.append(len(clauses) - before)
        active_rows += 1

    nvars = pool.top
    cnf_path = outdir / f"orbit_{idx}_target_{target}.cnf"
    proof_path = outdir / f"orbit_{idx}_target_{target}.drat"
    trim_log_path = outdir / f"orbit_{idx}_target_{target}_drat_trim.log"
    solver_log_path = outdir / f"orbit_{idx}_target_{target}_cadical.log"
    outdir.mkdir(parents=True, exist_ok=True)
    with cnf_path.open("w") as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(str(int(x)) for x in c) + " 0\n")

    rec = {
        "schema": "dim2_cnf_cert_orbit_v1",
        "cert_index": idx,
        "target": target,
        "W_basis": [int(x) for x in orb["basis"]],
        "W_rref": list(W),
        "raw_lb": raw_lb,
        "quotient_dim": k,
        "integer_system_rows": len(rows),
        "row_meta": row_meta,
        "singleton_upper_bound_hist": {str(k): int(v) for k, v in sorted(upper_hist.items())},
        "active_quotient_directions": len(active_q),
        "copy_variables": len(all_lits),
        "cnf_variables": nvars,
        "cnf_clauses": len(clauses),
        "encoded_nontrivial_wang_rows": active_rows,
        "immediate_empty_rows": immediate_empty,
        "row_copy_pop_hist": {str(k): int(v) for k, v in sorted(row_copy_pop_hist.items())},
        "row_constraint_clause_hist": {str(k): int(v) for k, v in sorted(Counter(row_clause_counts).items())},
        "cnf_path": str(cnf_path),
        "cnf_sha256": file_sha256(cnf_path),
        "lut_path": str(LUT_PATH),
        "lut_sha256": file_sha256(LUT_PATH),
        "cache_path": str(CACHE_PATH),
        "cache_sha256": file_sha256(CACHE_PATH),
        "equisatisfiable_encoding": "x_q with singleton upper bound u_q is represented by u_q Boolean copies; each Wang row counts all copies whose q lies in the quotient subspace; sum copies = target.",
    }

    if run_solver:
        cadical = shutil.which("cadical")
        drat_trim = shutil.which("drat-trim")
        if cadical is None or drat_trim is None:
            rec["solver_error"] = {"cadical": cadical, "drat_trim": drat_trim}
        else:
            cmd = [cadical, "-q", "--binary=false", "-t", str(cadical_timeout), str(cnf_path), str(proof_path)]
            t0 = time.time()
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=cadical_timeout + 30)
            cad_elapsed = time.time() - t0
            solver_log_path.write_text("CMD: " + " ".join(cmd) + "\n\nSTDOUT:\n" + proc.stdout + "\nSTDERR:\n" + proc.stderr)
            rec["cadical"] = {
                "command": cmd,
                "returncode": proc.returncode,
                "elapsed_sec": cad_elapsed,
                "stdout_tail": proc.stdout[-2000:],
                "stderr_tail": proc.stderr[-2000:],
                "proof_path": str(proof_path),
                "proof_exists": proof_path.exists(),
                "proof_size_bytes": proof_path.stat().st_size if proof_path.exists() else 0,
                "proof_sha256": file_sha256(proof_path) if proof_path.exists() else None,
                "log_path": str(solver_log_path),
            }
            # CaDiCaL returns 20 for UNSAT.  Check proof only then.
            if proc.returncode == 20 and proof_path.exists() and proof_path.stat().st_size > 0:
                trim_cmd = [drat_trim, str(cnf_path), str(proof_path)]
                t1 = time.time()
                trim = subprocess.run(trim_cmd, capture_output=True, text=True, timeout=drat_trim_timeout)
                trim_elapsed = time.time() - t1
                trim_log_path.write_text("CMD: " + " ".join(trim_cmd) + "\n\nSTDOUT:\n" + trim.stdout + "\nSTDERR:\n" + trim.stderr)
                ok = (trim.returncode == 0 and ("s VERIFIED" in trim.stdout or "s VERIFIED" in trim.stderr or "VERIFIED" in trim.stdout or "VERIFIED" in trim.stderr))
                rec["drat_trim"] = {
                    "command": trim_cmd,
                    "returncode": trim.returncode,
                    "elapsed_sec": trim_elapsed,
                    "verified": ok,
                    "stdout_tail": trim.stdout[-2000:],
                    "stderr_tail": trim.stderr[-2000:],
                    "log_path": str(trim_log_path),
                }
    rec_path = outdir / f"orbit_{idx}_target_{target}_certificate.json"
    rec["record_path"] = str(rec_path)
    rec_path.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n")
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--indices", default="484", help="comma-separated orbit indices")
    ap.add_argument("--target", type=int, default=18)
    ap.add_argument("--outdir", type=Path, default=OUTDIR)
    ap.add_argument("--run-solver", action="store_true")
    ap.add_argument("--cadical-timeout", type=int, default=600)
    ap.add_argument("--drat-trim-timeout", type=int, default=600)
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    results = []
    for idx in [int(x) for x in args.indices.split(',') if x.strip()]:
        print(f"=== CNF certificate orbit {idx} target {args.target} ===", flush=True)
        rec = build_cnf_for_orbit(idx, args.target, args.outdir / f"orbit_{idx}", args.run_solver, args.cadical_timeout, args.drat_trim_timeout)
        results.append(rec)
        print(json.dumps({
            "idx": idx,
            "cnf_vars": rec["cnf_variables"],
            "cnf_clauses": rec["cnf_clauses"],
            "cnf_sha256": rec["cnf_sha256"],
            "cadical_rc": rec.get("cadical", {}).get("returncode"),
            "proof_size": rec.get("cadical", {}).get("proof_size_bytes"),
            "drat_verified": rec.get("drat_trim", {}).get("verified"),
        }, indent=2), flush=True)
    summary = {
        "schema": "dim2_cnf_cert_summary_v1",
        "indices": [r["cert_index"] for r in results],
        "target": args.target,
        "results": [r["record_path"] for r in results],
        "all_cadical_unsat": all(r.get("cadical", {}).get("returncode") == 20 for r in results) if args.run_solver else None,
        "all_drat_verified": all(r.get("drat_trim", {}).get("verified") is True for r in results) if args.run_solver else None,
    }
    out = args.outdir / "summary.json"
    out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print("SUMMARY")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
