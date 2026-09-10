#!/usr/bin/env python3
"""Add capacity-4 half-purity clauses to an E11 core rank-19 CNF.

Mathematical consequence (defect/leak lemma): for slice s with c active terms,
  dim L_v(s) + dim L_w(s) <= c-3.
Thus if both v-leak and w-leak occur in slice s, then c >= 5.  Equivalently,
  VLEAK_s and WLEAK_s => at least five u_{t,s}=1.

This script adds only that c=4-or-less corollary, not the full rank inequality.
It is intended as a proof-bearing candidate layer after independent review and
positive-control validation.
"""
from __future__ import annotations

import argparse
import itertools
import json
import time
from pathlib import Path

GROUP = [0b000000111, 0b000111000, 0b111000000]
RANK = 19
BASE_STRIDE = 26


def slice_block(s: int):
    a = s + 1
    return a % 3, a // 3


def uvar(t: int, s: int) -> int:
    return BASE_STRIDE * t + s + 1


def vvar(t: int, b: int) -> int:
    return BASE_STRIDE * t + 8 + b + 1


def wvar(t: int, c: int) -> int:
    return BASE_STRIDE * t + 17 + c + 1


def parse_header(path: Path):
    comments = []
    with path.open() as f:
        for line in f:
            if line.startswith('c'):
                comments.append(line.rstrip('\n'))
                continue
            if line.startswith('p cnf'):
                _p, _cnf, nvars, nclauses = line.split()[:4]
                return int(nvars), int(nclauses), comments
    raise ValueError(f"no DIMACS header in {path}")


class VarAlloc:
    def __init__(self, start: int):
        self.n = start
    def new(self) -> int:
        self.n += 1
        return self.n


def build_half_purity_clauses(start_var: int, rank: int = RANK):
    va = VarAlloc(start_var)
    clauses = []
    stats = {
        "y_v_leak_vars": 0,
        "y_w_leak_vars": 0,
        "slice_vleak_vars": 0,
        "slice_wleak_vars": 0,
        "and_definition_clauses": 0,
        "leak_or_forward_clauses": 0,
        "half_purity_cardinality_clauses": 0,
    }

    for s in range(8):
        j_s, i_s = slice_block(s)
        v_out = [b for b in range(9) if b // 3 != j_s]
        w_out = [c for c in range(9) if c // 3 != i_s]
        yv = []
        yw = []
        for t in range(rank):
            u = uvar(t, s)
            for b in v_out:
                y = va.new(); yv.append(y); stats["y_v_leak_vars"] += 1
                v = vvar(t, b)
                # y <-> (u & v)
                clauses.append([-y, u]); clauses.append([-y, v]); clauses.append([y, -u, -v])
                stats["and_definition_clauses"] += 3
            for c in w_out:
                y = va.new(); yw.append(y); stats["y_w_leak_vars"] += 1
                w = wvar(t, c)
                clauses.append([-y, u]); clauses.append([-y, w]); clauses.append([y, -u, -w])
                stats["and_definition_clauses"] += 3
        vleak = va.new(); wleak = va.new()
        stats["slice_vleak_vars"] += 1
        stats["slice_wleak_vars"] += 1
        for y in yv:
            clauses.append([-y, vleak])
            stats["leak_or_forward_clauses"] += 1
        for y in yw:
            clauses.append([-y, wleak])
            stats["leak_or_forward_clauses"] += 1
        # VLEAK & WLEAK => at least five active terms in slice s.
        # CNF: for every 15-subset Z of terms, (-VLEAK or -WLEAK or OR_{t in Z} u_ts).
        # If at most four u's are true, some 15-subset consists only of false u's and forbids both leaks.
        for Z in itertools.combinations(range(rank), rank - 4):
            clauses.append([-vleak, -wleak] + [uvar(t, s) for t in Z])
            stats["half_purity_cardinality_clauses"] += 1

    stats["new_vars"] = va.n - start_var
    stats["new_clauses"] = len(clauses)
    return va.n, clauses, stats


def copy_with_new_clauses(in_path: Path, out_path: Path, total_vars: int, total_clauses: int, add_clauses):
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with in_path.open() as fin, out_path.open('w') as fout:
        fout.write("c half-purity augmentation: VLEAK_s and WLEAK_s imply capacity_s >= 5\n")
        for line in fin:
            if line.startswith('p cnf'):
                fout.write(f"p cnf {total_vars} {total_clauses}\n")
            else:
                fout.write(line)
        for cl in add_clauses:
            fout.write(" ".join(str(int(x)) for x in cl) + " 0\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--in-cnf', type=Path, default=Path('data/core_sat/e11_rank19_blockspread.cnf'))
    ap.add_argument('--out-cnf', type=Path, default=Path('data/core_sat/e11_rank19_blockspread_halfpurity.cnf'))
    ap.add_argument('--meta', type=Path, default=None)
    ap.add_argument('--rank', type=int, default=RANK)
    args = ap.parse_args()
    t0 = time.time()
    nvars, nclauses, comments = parse_header(args.in_cnf)
    total_vars, add_clauses, stats = build_half_purity_clauses(nvars, args.rank)
    total_clauses = nclauses + len(add_clauses)
    copy_with_new_clauses(args.in_cnf, args.out_cnf, total_vars, total_clauses, add_clauses)
    meta = {
        "input_cnf": str(args.in_cnf),
        "output_cnf": str(args.out_cnf),
        "rank": args.rank,
        "base_vars": nvars,
        "base_clauses": nclauses,
        "total_vars": total_vars,
        "total_clauses": total_clauses,
        "half_purity_statement": "For every slice s, if active terms leak on both v outside R_j and w outside C_i, then at least five terms are active in s.",
        "encoding": "AND variables for u_ts & v_out and u_ts & w_out; forward ORs into VLEAK/WLEAK; long clauses encode VLEAK & WLEAK => sum u_ts >= 5.",
        "stats": stats,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    meta_path = args.meta or args.out_cnf.with_suffix(args.out_cnf.suffix + '.meta.json')
    meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        "status": "ok",
        "out_cnf": str(args.out_cnf),
        "meta": str(meta_path),
        "base_vars": nvars,
        "base_clauses": nclauses,
        "total_vars": total_vars,
        "total_clauses": total_clauses,
        "stats": stats,
        "elapsed_sec": meta["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
