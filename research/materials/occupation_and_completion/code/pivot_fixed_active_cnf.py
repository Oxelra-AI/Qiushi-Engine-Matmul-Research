#!/usr/bin/env python3
"""Encode a pivot-fixed active Wang row set as SAT.

Input is the JSONL active-row core written by pivot_fixed_full_wang.py.  The
model is Boolean for length 20: variables x_a for all non-pivot A-directions,
cardinality sum x_a = length-1, x_pivot is fixed true, and each row mask gives
sum_{a in row, a!=pivot} x_a <= cap - 1_{pivot in row}.  Pair constraints
span(p,a) are added explicitly.

This is a proof-oriented experiment for small CEGAR row cores: if an active
subset is UNSAT, that subset itself is a compact certificate target; if SAT, the
candidate can be replayed against the complete full Wang binary.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import time
from collections import Counter
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool


def bit_in(words, p: int) -> bool:
    return bool((int(words[p >> 6]) >> (p & 63)) & 1)


def points_in_words(words):
    pts = []
    for wi, w0 in enumerate(words):
        w = int(w0)
        while w:
            lb = w & -w
            b = lb.bit_length() - 1
            p = wi * 64 + b
            if 1 <= p <= 511:
                pts.append(p)
            w ^= lb
    return pts


def read_active_rows(path: Path):
    rows = []
    with path.open() as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            rows.append(r)
    return rows


def build_cnf(active_path: Path, pivot: int, length: int, cnf_path: Path, map_path: Path, include_pairs: bool = True):
    t0 = time.time()
    vpool = IDPool()
    var_of = {}
    point_of = {}
    for p in range(1, 512):
        if p == pivot:
            continue
        var = vpool.id(f"x_{p}")
        var_of[p] = var
        point_of[var] = p

    cnf = CNF()
    stats = {"skipped_tautological": 0, "rhs_negative": 0, "rhs_zero": 0, "row_constraints": 0}
    row_len_hist = Counter(); rhs_hist = Counter(); cap_hist = Counter(); dim_hist = Counter()

    # Exact cardinality of the non-pivot selected set.
    eq = CardEnc.equals(lits=list(var_of.values()), bound=length - 1, vpool=vpool, encoding=EncType.seqcounter)
    cnf.extend(eq.clauses)
    stats["cardinality_clauses"] = len(eq.clauses)

    # Explicit quotient-pair/lift-bit rows x_a + x_{a+p} <= 1 for n=20.
    pair_rows = 0
    if include_pairs:
        seen = set()
        for a in range(1, 512):
            if a == pivot:
                continue
            b = a ^ pivot
            if b == 0 or b == pivot:
                continue
            pair = tuple(sorted((a, b)))
            if pair in seen:
                continue
            seen.add(pair)
            cnf.append([-var_of[pair[0]], -var_of[pair[1]]])
            pair_rows += 1
    stats["manual_pair_rows"] = pair_rows

    rows = read_active_rows(active_path)
    seen_constraints = set()
    for r in rows:
        words = [int(w) for w in r["words"]]
        cap = int(r["cap"]); dim = int(r.get("dim", -1))
        rhs = cap - (1 if bit_in(words, pivot) else 0)
        pts = [p for p in points_in_words(words) if p != pivot]
        lits = sorted(var_of[p] for p in pts)
        if rhs < 0:
            cnf.append([])
            stats["rhs_negative"] += 1
            continue
        if rhs >= len(lits):
            stats["skipped_tautological"] += 1
            continue
        key = (tuple(lits), rhs)
        if key in seen_constraints:
            continue
        seen_constraints.add(key)
        row_len_hist[len(lits)] += 1; rhs_hist[rhs] += 1; cap_hist[cap] += 1; dim_hist[dim] += 1
        if rhs == 0:
            for lit in lits:
                cnf.append([-lit])
            stats["rhs_zero"] += 1
        else:
            enc = CardEnc.atmost(lits=lits, bound=rhs, vpool=vpool, encoding=EncType.seqcounter)
            cnf.extend(enc.clauses)
        stats["row_constraints"] += 1

    cnf_path.parent.mkdir(parents=True, exist_ok=True)
    cnf.to_file(str(cnf_path))
    meta = {
        "schema": "pivot_fixed_active_cnf_v1",
        "active_rows_path": str(active_path),
        "pivot": pivot,
        "length": length,
        "include_pairs": include_pairs,
        "input_active_rows": len(rows),
        "n_point_variables": len(var_of),
        "n_total_variables": vpool.top,
        "n_clauses": len(cnf.clauses),
        "cnf_path": str(cnf_path),
        "stats": stats,
        "row_len_hist": dict(sorted((int(k), int(v)) for k, v in row_len_hist.items())),
        "rhs_hist": dict(sorted((int(k), int(v)) for k, v in rhs_hist.items())),
        "cap_hist": dict(sorted((int(k), int(v)) for k, v in cap_hist.items())),
        "dim_hist": dict(sorted((int(k), int(v)) for k, v in dim_hist.items())),
        "elapsed_sec": time.time() - t0,
    }
    map_data = {"var_to_point": {str(v): int(p) for v, p in point_of.items()}, "point_to_var": {str(p): int(v) for p, v in var_of.items()}, "meta": meta}
    map_path.write_text(json.dumps(map_data, indent=2, sort_keys=True) + "\n")
    cnf_path.with_suffix(".meta.json").write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n")
    print(json.dumps(meta, indent=2, sort_keys=True))
    return meta


def run_solver(cnf_path: Path, solver: str, timeout: int, out_path: Path, proof_path: Path | None = None):
    cmd = [solver, str(cnf_path)]
    if proof_path is not None and solver.endswith("cadical"):
        # CaDiCaL accepts output/proof as positional args in this build; avoid
        # relying on proof logging until this is tested deliberately.
        pass
    t0 = time.time()
    p = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    elapsed = time.time() - t0
    stdout = p.stdout
    status = "UNKNOWN"
    if "UNSATISFIABLE" in stdout:
        status = "UNSAT"
    elif "SATISFIABLE" in stdout:
        status = "SAT"
    model = []
    if status == "SAT":
        for line in stdout.splitlines():
            if line.startswith("v "):
                model.extend(int(x) for x in line.split()[1:] if x != "0")
    rec = {"solver": solver, "cnf": str(cnf_path), "returncode": p.returncode, "status": status, "elapsed_sec": elapsed, "stdout_tail": stdout[-4000:], "stderr_tail": p.stderr[-4000:], "model_head": model[:200], "model_lit_count": len(model)}
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": status, "returncode": p.returncode, "elapsed_sec": elapsed, "out": str(out_path)}, indent=2, sort_keys=True))


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("build")
    p.add_argument("--active", type=Path, required=True)
    p.add_argument("--pivot", type=int, required=True)
    p.add_argument("--length", type=int, default=20)
    p.add_argument("--cnf", type=Path, required=True)
    p.add_argument("--map", type=Path, required=True)
    p.add_argument("--no-pairs", action="store_true")
    p = sub.add_parser("solve")
    p.add_argument("--cnf", type=Path, required=True)
    p.add_argument("--solver", default="kissat")
    p.add_argument("--timeout", type=int, default=300)
    p.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    if args.cmd == "build":
        build_cnf(args.active, args.pivot, args.length, args.cnf, args.map, include_pairs=not args.no_pairs)
    else:
        run_solver(args.cnf, args.solver, args.timeout, args.out)


if __name__ == "__main__":
    main()
