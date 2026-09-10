#!/usr/bin/env python3
"""Analyze the stored matrix-challenges rank-22 CNF header and variable layout.

The semantic layout follows matrix-challenges/src/encode.c with DIM=3 and
size=22, but the stored challenge4/MM-22.cnf has a corrected header compared to
the current source snapshot. This script checks the stored DIMACS integrity and
prints the exact variable ranges needed to interpret solver assignments.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path


def layout(size: int, dim: int = 3):
    sdim = dim * dim
    cdim = sdim * sdim * sdim
    orig = size * sdim * 3
    pair = size * sdim * sdim
    cube = size * sdim * sdim * sdim
    xor_aux = sdim * sdim * sdim * ((size - 3) // 2)
    return {
        "size": size,
        "dim": dim,
        "sdim": sdim,
        "cdim": cdim,
        "orig_count": orig,
        "pair_count": pair,
        "cube_count": cube,
        "xor_aux_count": xor_aux,
        "base_coeff_range": [1, orig],
        "A_i_a": "i*27 + a + 1, with i=0..21, a=row-major 0..8",
        "B_i_b": "i*27 + 9 + b + 1, with b=row-major 0..8",
        "C_i_c": "i*27 + 18 + c + 1, with c=row-major 0..8",
        "pair_range": [orig + 1, orig + pair],
        "pair_var": "orig + i*81 + a*9 + b + 1 = (A_i,a AND B_i,b)",
        "cube_range": [orig + pair + 1, orig + pair + cube],
        "cube_var": "orig+pair + i*729 + a*81 + b*9 + c + 1 = pair(i,a,b) AND C_i,c",
        "xor_aux_range": [orig + pair + cube + 1, orig + pair + cube + xor_aux],
        "semantic_variable_total_without_padding": orig + pair + cube + xor_aux,
        "pair_clauses": pair * 3,
        "cube_clauses": cube * 3,
        "xor_parity_clauses": cdim * (size - 2) * 4,
        "semantic_clause_total_plain_xor": (pair + cube) * 3 + cdim * (size - 2) * 4,
        "inactive_atleastone_clause_count_in_current_source_header": 3 * (sdim + size),
    }


def parse_dimacs(path: Path):
    header = None
    clauses = 0
    max_abs = 0
    vars_seen = set()
    empty = 0
    with path.open() as f:
        for line_no, line in enumerate(f, 1):
            s = line.strip()
            if not s or s.startswith('c'):
                continue
            if s.startswith('p '):
                parts = s.split()
                header = {"format": parts[1], "vars": int(parts[2]), "clauses": int(parts[3]), "line": line_no}
                continue
            lits = [int(x) for x in s.split()]
            if not lits or lits[-1] != 0:
                raise ValueError(f"bad DIMACS clause line {line_no}: {s[:80]}")
            if len(lits) == 1:
                empty += 1
            for lit in lits[:-1]:
                a = abs(lit)
                max_abs = max(max_abs, a)
                vars_seen.add(a)
            clauses += 1
    return {
        "header": header,
        "actual_clause_lines": clauses,
        "max_abs_literal": max_abs,
        "used_variable_count": len(vars_seen),
        "unused_variables_within_header": header["vars"] - len(vars_seen) if header else None,
        "empty_clause_count": empty,
        "header_clause_count_matches": bool(header and header["clauses"] == clauses),
        "header_vars_cover_literals": bool(header and max_abs <= header["vars"]),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cnf", type=Path)
    ap.add_argument("--out", type=Path)
    args = ap.parse_args()
    result = {"cnf": str(args.cnf), "dimacs": parse_dimacs(args.cnf), "layout_size22": layout(22)}
    text = json.dumps(result, indent=2, sort_keys=True)
    print(text)
    if args.out:
        args.out.write_text(text + "\n")

if __name__ == "__main__":
    main()
