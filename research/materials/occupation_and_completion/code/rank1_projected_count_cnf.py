#!/usr/bin/env python3
"""Proof-producing CNF for cardinality bounds on rank-1 A-points.

For a hypothetical length-s decomposition over F2, every Wang occupation row
Phi gives |support_A ∩ Phi| <= s - L(Phi).  Restricting attention to the 49
rank-1 projective A-points gives a necessary projected system for the subset of
rank-1 factors in any full support: for each Phi, the rank-1 subset occupancy
is at most the full support occupancy, hence still <= s - L(Phi).

This script keeps capacities for full rank_s (default 20) but sets an independent
exact count K of rank-1 points.  UNSAT therefore proves that no admissible
full length-rank_s support can contain K rank-1 A-points (with optional E11
fixed), provided the selected row family is a subset of the projected Wang rows.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rank1_capacity_profile import load_or_build  # noqa: E402


def sha256(path: Path) -> str | None:
    if not path.exists() or not path.is_file():
        return None
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(4 * 1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def parse_groups(spec: str) -> set[tuple[int, int]] | None:
    spec = spec.strip()
    if not spec:
        return None
    out: set[tuple[int, int]] = set()
    for part in spec.split(','):
        part = part.strip()
        if not part:
            continue
        if ':' in part:
            a, b = part.split(':', 1)
        else:
            a, b = part.split('/', 1)
        out.add((int(a), int(b)))
    return out


def selected_rows(cons: Iterable[tuple[int, int, int]], max_intersection_size: int | None,
                  include_groups: set[tuple[int, int]] | None) -> list[tuple[int, int, int]]:
    rows = []
    for mask, cap, key in cons:
        size = int(mask).bit_count()
        if include_groups is not None:
            if (size, int(cap)) not in include_groups:
                continue
        elif max_intersection_size is not None:
            if size > max_intersection_size:
                continue
        if size <= int(cap):
            continue
        rows.append((int(mask), int(cap), int(key)))
    return rows


def write_cnf(pts: list[int], rows: list[tuple[int, int, int]], *, exact_count: int,
              rank_s: int, fixed_point: int | None, cnf: Path, meta: Path,
              max_intersection_size: int | None, include_groups: set[tuple[int, int]] | None,
              compression_meta: dict, lut_meta: dict) -> dict:
    from pysat.card import CardEnc, EncType

    t0 = time.time()
    cnf.parent.mkdir(parents=True, exist_ok=True)
    var = {p: i + 1 for i, p in enumerate(pts)}
    top = len(pts)
    clauses: list[list[int]] = []

    enc = CardEnc.equals(lits=list(var.values()), bound=exact_count, top_id=top, encoding=EncType.seqcounter)
    clauses.extend([list(cl) for cl in enc.clauses])
    top = enc.nv
    if fixed_point is not None:
        if fixed_point in var:
            clauses.append([var[fixed_point]])
        else:
            clauses.append([])

    hist = Counter()
    direct_clauses = 0
    witness = []
    for mask, cap, key in rows:
        lits = [i + 1 for i in range(len(pts)) if (mask >> i) & 1]
        if len(lits) <= cap:
            continue
        hist[(len(lits), cap)] += 1
        ncomb = math.comb(len(lits), cap + 1)
        direct_clauses += ncomb
        for comb in itertools.combinations(lits, cap + 1):
            clauses.append([-v for v in comb])
        if len(witness) < 200:
            witness.append({"intersection_size": len(lits), "cap": cap, "key": key, "dim": key & 0xF, "clauses": ncomb})

    with cnf.open("w") as f:
        f.write(f"p cnf {top} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")

    payload = {
        "problem": "rank-1 projected Wang cardinality-count CNF",
        "field": "F2",
        "rank_s_for_capacities": rank_s,
        "exact_rank1_count": exact_count,
        "fixed_point": fixed_point,
        "rank1_points": pts,
        "filter": {
            "max_intersection_size": max_intersection_size,
            "include_groups": None if include_groups is None else sorted([list(g) for g in include_groups]),
        },
        "selected_constraint_count": len(rows),
        "selected_constraint_hist": {f"{a},{b}": c for (a, b), c in sorted(hist.items())},
        "num_vars": top,
        "num_clauses": len(clauses),
        "global_exact_count_clauses": len(enc.clauses),
        "fixed_unit_clauses": 0 if fixed_point is None else 1,
        "direct_capacity_clauses": direct_clauses,
        "witness_keys_head": witness,
        "compression": compression_meta,
        "lut_meta_brief": {
            "coverage_ok": lut_meta.get("coverage_ok"),
            "conflict_count": lut_meta.get("conflict_count"),
            "subspace_count": lut_meta.get("subspace_count"),
        },
        "cnf_path": str(cnf),
        "meaning": (
            "UNSAT proves that the rank-1 subset of any full length-rank_s Wang-admissible "
            "A-support cannot have exact_rank1_count points satisfying the optional fixed point, "
            "because only necessary projected Wang rows are used. SAT/UNKNOWN is only about this "
            "projected necessary system."
        ),
        "elapsed_sec": time.time() - t0,
    }
    meta.parent.mkdir(parents=True, exist_ok=True)
    meta.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: payload[k] for k in ["selected_constraint_count", "selected_constraint_hist", "num_vars", "num_clauses", "direct_capacity_clauses", "elapsed_sec"]}, indent=2, sort_keys=True))
    return payload


def parse_solver_log(path: Path) -> dict:
    if not path.exists():
        return {"exists": False}
    text = path.read_text(errors="replace")
    return {
        "exists": True,
        "sat_status": (text.split("s ")[-1].split()[0] if "s " in text else None),
        "unsat": "s UNSATISFIABLE" in text,
        "verified": "s VERIFIED" in text,
    }


def run_solver(cnf: Path, meta: Path, timeout: int) -> dict:
    stem = cnf.stem
    drat = cnf.with_suffix(".drat")
    cadlog = cnf.with_suffix(".cadical.log")
    trimlog = cnf.with_suffix(".drat_trim.log")
    status = cnf.with_suffix(".status.json")
    cmd = ["cadical", "--unsat", "--binary=false", "-n"]
    if timeout > 0:
        cmd.extend(["-t", str(timeout)])
    cmd.extend([str(cnf), str(drat)])
    t0 = time.time()
    with cadlog.open("w") as f:
        proc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, text=True)
    res = {
        "cnf": str(cnf),
        "meta": str(meta),
        "drat": str(drat),
        "cadical_log": str(cadlog),
        "drat_trim_log": str(trimlog),
        "cadical_exit": proc.returncode,
        "cadical_elapsed_sec": time.time() - t0,
    }
    if proc.returncode == 20:
        t1 = time.time()
        with trimlog.open("w") as f:
            trim = subprocess.run(["drat-trim", str(cnf), str(drat)], stdout=f, stderr=subprocess.STDOUT, text=True)
        res["drat_trim_exit"] = trim.returncode
        res["drat_trim_elapsed_sec"] = time.time() - t1
    else:
        res["drat_trim_exit"] = None
        res["drat_trim_elapsed_sec"] = None
    res["hashes"] = {str(p): sha256(p) for p in [cnf, meta, drat, cadlog, trimlog] if p.exists()}
    res["cadical_log_parse"] = parse_solver_log(cadlog)
    res["drat_trim_log_parse"] = parse_solver_log(trimlog)
    status.write_text(json.dumps(res, indent=2, sort_keys=True) + "\n")
    print(json.dumps(res, indent=2, sort_keys=True))
    return res


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--cache", type=Path, default=Path("data/wang_capacity_rank1_profile/rank1_intersection_cache.pkl"))
    ap.add_argument("--rank-s", type=int, default=20, help="full support length used for capacities s-L(Phi)")
    ap.add_argument("--exact-count", type=int, required=True, help="number of rank-1 points selected in the projected system")
    ap.add_argument("--fixed-point", type=int, default=1)
    ap.add_argument("--no-fixed", action="store_true")
    ap.add_argument("--max-intersection-size", type=int, default=9)
    ap.add_argument("--include-groups", default="")
    ap.add_argument("--cnf", type=Path, required=True)
    ap.add_argument("--meta", type=Path, required=True)
    ap.add_argument("--solve", action="store_true")
    ap.add_argument("--solver-time", type=int, default=0)
    args = ap.parse_args()

    pts, cons, cmeta, lmeta = load_or_build(args.cache, args.lut, args.rank_s, False)
    rows = selected_rows(cons, args.max_intersection_size, parse_groups(args.include_groups))
    write_cnf(
        pts,
        rows,
        exact_count=args.exact_count,
        rank_s=args.rank_s,
        fixed_point=None if args.no_fixed else args.fixed_point,
        cnf=args.cnf,
        meta=args.meta,
        max_intersection_size=args.max_intersection_size,
        include_groups=parse_groups(args.include_groups),
        compression_meta=cmeta,
        lut_meta=lmeta,
    )
    if args.solve:
        run_solver(args.cnf, args.meta, args.solver_time)


if __name__ == "__main__":
    main()
