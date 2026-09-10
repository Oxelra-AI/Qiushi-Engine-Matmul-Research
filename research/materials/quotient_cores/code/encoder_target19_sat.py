#!/usr/bin/env python3
"""Positive-control SAT replay for the analysis Boolean-copy cardinality encoder.

For each load-bearing dim-2 orbit 484--491, rebuild the same Boolean-copy
CNF used for the target-18 DRAT certificates, but at target 19.  Solve the CNF,
decode the model back to integer multiplicities x_q, and independently scan the
quotient occupation rows regenerated from the LUT.  This detects the dangerous
failure mode where the sequential-counter/CardEnc layer is accidentally too
strong: the same encoder that proves UNSAT at target 18 must admit an explicit
witness at the next length, and the decoded witness must satisfy the mathematical
row inequalities.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))

from dim2_independent_semantics import (  # type: ignore
    LUT_PATH, CACHE_PATH, rref_ind, independent_rows, popcount,
    canonical_rows_digest, file_sha256,
)
from dim2_cnf_cert import atmost_clauses, atleast_clauses  # type: ignore

try:
    from pysat.formula import CNF, IDPool  # type: ignore
    from pysat.solvers import Solver  # type: ignore
except Exception as e:  # pragma: no cover
    CNF = None
    IDPool = None
    Solver = None

INDICES = [484, 485, 486, 487, 488, 489, 490, 491]
OUTDIR = Path("data/encoder_target19")


def load_lut_orbits():
    with LUT_PATH.open("rb") as f:
        data = pickle.load(f)
    lut = data["lut"] if isinstance(data, dict) and "lut" in data else data
    with CACHE_PATH.open("rb") as f:
        cache = pickle.load(f)
    return lut, {int(o["cert_index"]): o for o in cache["orbits"]}


def build_cnf_with_maps(idx: int, target: int, outdir: Path) -> Dict:
    if CNF is None or IDPool is None:
        raise RuntimeError("python-sat is unavailable")
    lut, orbit_by_idx = load_lut_orbits()
    orb = orbit_by_idx[idx]
    W = rref_ind([int(x) for x in orb["basis"]], 9)
    rows, meta = independent_rows(W, lut, target)
    k = meta["quotient_dim"]
    npts = (1 << k) - 1

    # Singleton caps produce the finite copy domain.  This intentionally mirrors
    # dim2_cnf_cert.py; the decoded witness is then checked separately.
    ub = [target] * (npts + 1)
    for mask, cap in rows:
        if popcount(mask) == 1:
            q = int(mask).bit_length()
            if int(cap) < ub[q]:
                ub[q] = int(cap)
    pool = IDPool()
    copies: Dict[int, List[int]] = {}
    var_to_q: Dict[int, int] = {}
    for q in range(1, npts + 1):
        cq = []
        for j in range(1, max(0, min(ub[q], target)) + 1):
            v = pool.id(f"x_{q}_{j}")
            cq.append(v); var_to_q[v] = q
        copies[q] = cq

    clauses: List[List[int]] = []
    all_lits = [lit for q in range(1, npts + 1) for lit in copies[q]]
    clauses.extend(atmost_clauses(all_lits, target, pool))
    clauses.extend(atleast_clauses(all_lits, target, pool))

    seen = set(); active_rows = 0; tautological_rows = 0; empty_rows = 0
    row_copy_pop_hist = Counter(); row_clause_counts = Counter()
    for mask, cap in rows:
        lits = []
        m = int(mask)
        while m:
            low = m & -m
            q = low.bit_length()
            lits.extend(copies[q])
            m ^= low
        lits = sorted(set(lits))
        row_copy_pop_hist[len(lits)] += 1
        if cap < 0:
            clauses.append([]); empty_rows += 1; continue
        if len(lits) <= int(cap):
            tautological_rows += 1; continue
        key = (tuple(lits), int(cap))
        if key in seen:
            continue
        seen.add(key)
        before = len(clauses)
        clauses.extend(atmost_clauses(lits, int(cap), pool))
        row_clause_counts[len(clauses)-before] += 1
        active_rows += 1

    outdir.mkdir(parents=True, exist_ok=True)
    cnf_path = outdir / f"orbit_{idx}_target_{target}.cnf"
    with cnf_path.open("w") as f:
        f.write(f"p cnf {pool.top} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(str(int(x)) for x in c) + " 0\n")
    return {
        "idx": idx,
        "target": target,
        "W_basis": [int(x) for x in orb["basis"]],
        "W_rref": list(W),
        "raw_lb": int(orb["raw_lb"]),
        "rows": rows,
        "row_meta": meta,
        "row_digest": canonical_rows_digest(rows),
        "ub_hist": {str(k): int(v) for k, v in sorted(Counter(ub[1:]).items())},
        "copies": copies,
        "var_to_q": var_to_q,
        "clauses": clauses,
        "nvars": pool.top,
        "nclauses": len(clauses),
        "cnf_path": str(cnf_path),
        "cnf_sha256": file_sha256(cnf_path),
        "copy_variables": len(all_lits),
        "active_rows": active_rows,
        "tautological_rows": tautological_rows,
        "empty_rows": empty_rows,
        "row_copy_pop_hist": {str(k): int(v) for k, v in sorted(row_copy_pop_hist.items())},
        "row_clause_count_hist": {str(k): int(v) for k, v in sorted(row_clause_counts.items())},
    }


def scan_counts(counts: Sequence[int], rows: Sequence[Tuple[int, int]]) -> Dict:
    violations = []
    tight = 0
    max_excess = -10**9
    for ri, (mask, cap) in enumerate(rows):
        lhs = 0
        m = int(mask)
        while m:
            low = m & -m
            i = low.bit_length() - 1
            lhs += int(counts[i])
            m ^= low
        excess = lhs - int(cap)
        if excess > 0:
            violations.append({"row_index": ri, "lhs": int(lhs), "cap": int(cap), "excess": int(excess), "mask_popcount": popcount(mask)})
        if excess == 0:
            tight += 1
        if excess > max_excess:
            max_excess = excess
    return {"violations": len(violations), "tight_rows": tight, "max_excess": int(max_excess), "violations_head": violations[:20]}


def solve_one(idx: int, target: int, outdir: Path, solver_names: Sequence[str], timeout: int) -> Dict:
    rec = build_cnf_with_maps(idx, target, outdir)
    cnf = CNF(from_clauses=rec["clauses"])
    chosen = None; model = None; elapsed = None; excs = []
    for name in solver_names:
        try:
            t0 = time.time()
            with Solver(name=name, bootstrap_with=cnf.clauses) as s:
                try:
                    s.conf_budget(timeout * 1000000)  # harmless for solvers supporting budgets; not a wall limit
                except Exception:
                    pass
                sat = s.solve()
                elapsed = time.time() - t0
                if sat:
                    model = s.get_model()
                    chosen = name
                    break
                else:
                    # A target-19 UNSAT here would be alarming; record it and try no other solver.
                    chosen = name
                    model = None
                    break
        except Exception as e:
            excs.append({"solver": name, "error": repr(e)})
            continue
    counts = None; scan = None; nz = []
    if model is not None:
        true_vars = {int(v) for v in model if int(v) > 0}
        counts = [0] * 127
        for v, q in rec["var_to_q"].items():
            if v in true_vars:
                counts[q-1] += 1
        nz = [(i+1, int(c)) for i, c in enumerate(counts) if c]
        scan = scan_counts(counts, rec["rows"])
    out = {
        "schema": "encoder_target19_orbit_v1",
        "cert_index": idx,
        "target": target,
        "solver": chosen,
        "solver_attempt_errors": excs,
        "sat": model is not None,
        "solve_elapsed_sec": elapsed,
        "cnf_path": rec["cnf_path"],
        "cnf_sha256": rec["cnf_sha256"],
        "nvars": rec["nvars"],
        "nclauses": rec["nclauses"],
        "copy_variables": rec["copy_variables"],
        "active_rows": rec["active_rows"],
        "row_digest": rec["row_digest"],
        "row_meta": rec["row_meta"],
        "ub_hist": rec["ub_hist"],
        "witness": {
            "weight": int(sum(counts)) if counts is not None else None,
            "nonzero_count": len(nz),
            "max_multiplicity": int(max(counts) if counts else 0) if counts is not None else None,
            "support": nz,
            "scan_against_independent_rows": scan,
        } if counts is not None else None,
        "lut_path": str(LUT_PATH),
        "lut_sha256": file_sha256(LUT_PATH),
        "cache_path": str(CACHE_PATH),
        "cache_sha256": file_sha256(CACHE_PATH),
    }
    rec_path = outdir / f"orbit_{idx}_target19_sat_witness.json"
    rec_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    # Avoid storing the huge raw clauses/model in the JSON object kept by caller.
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--indices", default=",".join(map(str, INDICES)))
    ap.add_argument("--target", type=int, default=19)
    ap.add_argument("--outdir", type=Path, default=OUTDIR)
    ap.add_argument("--solvers", default="cadical153,cadical195,glucose4,glucose3,minisat22")
    ap.add_argument("--timeout", type=int, default=120)
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    indices = [int(x) for x in args.indices.split(',') if x.strip()]
    solvers = [x.strip() for x in args.solvers.split(',') if x.strip()]
    results = []
    t0 = time.time()
    for idx in indices:
        print(f"=== target-19 encoder SAT orbit {idx} ===", flush=True)
        rec = solve_one(idx, args.target, args.outdir / f"orbit_{idx}", solvers, args.timeout)
        results.append(rec)
        print(json.dumps({
            "idx": idx, "sat": rec["sat"], "solver": rec["solver"],
            "nvars": rec["nvars"], "nclauses": rec["nclauses"],
            "weight": rec["witness"]["weight"] if rec["witness"] else None,
            "max_mult": rec["witness"]["max_multiplicity"] if rec["witness"] else None,
            "violations": rec["witness"]["scan_against_independent_rows"]["violations"] if rec["witness"] else None,
        }, indent=2), flush=True)
    summary = {
        "schema": "encoder_target19_summary_v1",
        "purpose": "SAT-side positive control for the same Boolean-copy sequential-counter encoder used by target-18 DRAT certificates",
        "indices": indices,
        "target": args.target,
        "all_sat": all(r["sat"] for r in results),
        "all_witnesses_weight_target": all((r.get("witness") or {}).get("weight") == args.target for r in results),
        "all_decoded_witnesses_pass_rows": all(((r.get("witness") or {}).get("scan_against_independent_rows") or {}).get("violations") == 0 for r in results),
        "max_multiplicities": {str(r["cert_index"]): (r.get("witness") or {}).get("max_multiplicity") for r in results},
        "result_paths": [str(args.outdir / f"orbit_{r['cert_index']}" / f"orbit_{r['cert_index']}_target19_sat_witness.json") for r in results],
        "elapsed_sec": time.time() - t0,
    }
    out = args.outdir / "summary.json"
    out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print("SUMMARY")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
