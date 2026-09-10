#!/usr/bin/env python3
"""Semantic tools for F2 3x3 matrix-multiplication SAT schemes.

This script intentionally works at the tensor/Brent-equation level rather than
at Tseitin-CNF level. Given a SAT solver assignment for a matrix-challenges
MM-r instance, it reads the first 27*r base coefficient variables only:
  A_i[a], B_i[b], C_i[c] in the same layout as src/encode.c/decode.c,
and verifies the 729 parity equations over F2:
  sum_i A_i[a] B_i[b] C_i[c] = delta(a,b,c) mod 2,
where a,b,c are row-major entries of the three 3x3 coefficient matrices and
  delta=1 iff a=(i,j), b=(j,k), c=(k,i).

It also reports type-m histograms per summand, where m is the number of the
three index equalities b-row=a-col, c-row=b-col, c-col=a-row that hold for a
monomial A[a]B[b]C[c]. Type-3 triples are exactly the 27 right-hand terms.
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

DIM = 3
SDIM = DIM * DIM
CDIM = SDIM ** 3


def avar(i: int, a: int) -> int:
    return i * 27 + a + 1


def bvar(i: int, b: int) -> int:
    return i * 27 + 9 + b + 1


def cvar(i: int, c: int) -> int:
    return i * 27 + 18 + c + 1


def idx2(rc: int) -> tuple[int, int]:
    return divmod(rc, DIM)


def delta(a: int, b: int, c: int) -> int:
    ai, aj = idx2(a)
    bj, bk = idx2(b)
    ck, ci = idx2(c)
    return int(aj == bj and bk == ck and ci == ai)


def cdelta(a: int, b: int, c: int) -> int:
    ai, aj = idx2(a)
    bj, bk = idx2(b)
    ck, ci = idx2(c)
    return int(aj == bj) + int(bk == ck) + int(ci == ai)


def parse_assignment(path: Path) -> dict[int, bool]:
    vals: dict[int, bool] = {}
    for tok in re.findall(r'-?\d+', path.read_text(errors='replace')):
        lit = int(tok)
        if lit == 0:
            continue
        # DIMACS solver output may contain header counts and 'v' lines; accepting
        # all integer tokens is robust enough if the model file is just a model.
        vals[abs(lit)] = lit > 0
    return vals


def extract_base(vals: dict[int, bool], rank: int):
    A = [[int(vals.get(avar(i, a), False)) for a in range(SDIM)] for i in range(rank)]
    B = [[int(vals.get(bvar(i, b), False)) for b in range(SDIM)] for i in range(rank)]
    C = [[int(vals.get(cvar(i, c), False)) for c in range(SDIM)] for i in range(rank)]
    return A, B, C


def verify_base(A, B, C):
    rank = len(A)
    failures = []
    type_parity_failures = {0: 0, 1: 0, 2: 0, 3: 0}
    type_counts_total = {0: 0, 1: 0, 2: 0, 3: 0}
    for a in range(SDIM):
        for b in range(SDIM):
            for c in range(SDIM):
                typ = cdelta(a, b, c)
                type_counts_total[typ] += 1
                lhs = 0
                for i in range(rank):
                    lhs ^= (A[i][a] & B[i][b] & C[i][c])
                rhs = delta(a, b, c)
                if lhs != rhs:
                    failures.append({"a": a, "b": b, "c": c, "type": typ, "lhs": lhs, "rhs": rhs})
                    type_parity_failures[typ] += 1
    return failures, type_parity_failures, type_counts_total


def summand_stats(A, B, C):
    rows = []
    for i, (Ai, Bi, Ci) in enumerate(zip(A, B, C)):
        type_hist = {0: 0, 1: 0, 2: 0, 3: 0}
        type3 = []
        for a in range(SDIM):
            if not Ai[a]:
                continue
            for b in range(SDIM):
                if not Bi[b]:
                    continue
                for c in range(SDIM):
                    if not Ci[c]:
                        continue
                    typ = cdelta(a, b, c)
                    type_hist[typ] += 1
                    if typ == 3:
                        type3.append([a, b, c])
        rows.append({
            "summand": i,
            "A_support": [a for a, v in enumerate(Ai) if v],
            "B_support": [b for b, v in enumerate(Bi) if v],
            "C_support": [c for c, v in enumerate(Ci) if v],
            "A_weight": sum(Ai),
            "B_weight": sum(Bi),
            "C_weight": sum(Ci),
            "monomial_type_hist": type_hist,
            "type3_triples": type3,
        })
    return rows


def layout(rank: int):
    orig = rank * 27
    pair = rank * 81
    cube = rank * 729
    xor_aux = CDIM * ((rank - 3) // 2)
    return {
        "rank": rank,
        "base_coeff_range": [1, orig],
        "pair_range": [orig + 1, orig + pair],
        "cube_range": [orig + pair + 1, orig + pair + cube],
        "xor_aux_range": [orig + pair + cube + 1, orig + pair + cube + xor_aux],
        "semantic_variable_total_without_padding": orig + pair + cube + xor_aux,
        "plain_xor_clause_total": (pair + cube) * 3 + CDIM * (rank - 2) * 4,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--rank', type=int, default=22)
    ap.add_argument('--model', type=Path, help='DIMACS/SAT assignment file to verify')
    ap.add_argument('--json-out', type=Path)
    ap.add_argument('--max-failures', type=int, default=20)
    args = ap.parse_args()

    out = {"layout": layout(args.rank)}
    if args.model:
        vals = parse_assignment(args.model)
        A, B, C = extract_base(vals, args.rank)
        failures, fail_by_type, total_by_type = verify_base(A, B, C)
        stats = summand_stats(A, B, C)
        out.update({
            "model": str(args.model),
            "base_support_total": sum(sum(row) for row in A) + sum(sum(row) for row in B) + sum(sum(row) for row in C),
            "failure_count": len(failures),
            "failure_by_type": fail_by_type,
            "total_monomials_by_type": total_by_type,
            "first_failures": failures[:args.max_failures],
            "summand_stats": stats,
            "type3_terms_total_with_multiplicity": sum(s['monomial_type_hist'][3] for s in stats),
        })
    text = json.dumps(out, indent=2, sort_keys=True)
    print(text)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text + '\n')


if __name__ == '__main__':
    main()
