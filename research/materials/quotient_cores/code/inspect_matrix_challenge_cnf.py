#!/usr/bin/env python3
"""Inspect Heule-Kauers-Seidl matrix-challenges CNFs at the semantic/base-variable level.

This script does not solve SAT instances. It parses DIMACS headers and classifies clauses
by whether they involve only the 27*r base variables corresponding to r summands of
(A,B,C) 3x3 factor masks. It is intended to document the exact surface of Challenge 4
(rank 22 over F2) and compare it with rank-23 challenge files.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
from typing import Iterable


def parse_dimacs(path: Path):
    nvars = nclauses = None
    clauses = []
    cur = []
    with path.open("r", encoding="utf-8", errors="replace") as f:
        for raw in f:
            line = raw.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p "):
                parts = line.split()
                if len(parts) >= 4 and parts[1] == "cnf":
                    nvars, nclauses = int(parts[2]), int(parts[3])
                continue
            for tok in line.split():
                lit = int(tok)
                if lit == 0:
                    clauses.append(tuple(cur))
                    cur = []
                else:
                    cur.append(lit)
    if cur:
        raise ValueError(f"unterminated clause in {path}")
    return nvars, nclauses, clauses


def base_var_decode(v: int, rank: int):
    """Return semantic coordinates for 1-indexed base variable v, or None.

    HKS/Palladinos convention: variables 1..27r are ordered by summand,
    factor A/B/C, and row-major 3x3 bit index.
    """
    if not (1 <= v <= 27 * rank):
        return None
    z = v - 1
    t = z // 27
    rem = z % 27
    factor_index = rem // 9
    bit = rem % 9
    return {
        "summand": t + 1,
        "factor": "ABC"[factor_index],
        "bit": bit,
        "row": bit // 3,
        "col": bit % 3,
    }


def inspect(path: Path):
    name = path.name
    # File names use MM-22 or MM-23; parse rank conservatively from first field.
    rank = None
    for part in name.replace(".cnf", "").split("-"):
        if part.isdigit():
            rank = int(part)
            break
    if rank is None:
        raise ValueError(f"cannot infer rank from {name}")
    base_limit = 27 * rank
    nvars, header_clauses, clauses = parse_dimacs(path)
    h = hashlib.sha256(path.read_bytes()).hexdigest()

    length_hist = collections.Counter(len(c) for c in clauses)
    base_only = []
    aux_only = 0
    mixed = 0
    for c in clauses:
        abs_vars = [abs(x) for x in c]
        if all(v <= base_limit for v in abs_vars):
            base_only.append(c)
        elif all(v > base_limit for v in abs_vars):
            aux_only += 1
        else:
            mixed += 1
    base_len_hist = collections.Counter(len(c) for c in base_only)
    base_positive_units = []
    base_negative_units = []
    base_nonunit = []
    for c in base_only:
        if len(c) == 1:
            if c[0] > 0:
                base_positive_units.append(c[0])
            else:
                base_negative_units.append(-c[0])
        else:
            base_nonunit.append(c)

    decoded_units = {
        "positive": [base_var_decode(v, rank) | {"var": v} for v in base_positive_units[:50]],
        "negative": [base_var_decode(v, rank) | {"var": v} for v in base_negative_units[:50]],
    }

    return {
        "file": str(path),
        "sha256": h,
        "rank_from_name": rank,
        "base_variable_count_27r": base_limit,
        "header_vars": nvars,
        "header_clauses": header_clauses,
        "parsed_clauses": len(clauses),
        "header_matches_parsed": (header_clauses == len(clauses)),
        "length_histogram": dict(sorted(length_hist.items())),
        "base_only_clause_count": len(base_only),
        "base_only_length_histogram": dict(sorted(base_len_hist.items())),
        "mixed_clause_count": mixed,
        "aux_only_clause_count": aux_only,
        "base_positive_unit_count": len(base_positive_units),
        "base_negative_unit_count": len(base_negative_units),
        "base_nonunit_clause_count": len(base_nonunit),
        "base_positive_unit_vars_first50": base_positive_units[:50],
        "base_negative_unit_vars_first50": base_negative_units[:50],
        "base_nonunit_clauses_first10": [list(c) for c in base_nonunit[:10]],
        "decoded_base_units_first50": decoded_units,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--matrix-challenges", default=None, help="Path to matrix-challenges checkout")
    parser.add_argument("--out", required=True)
    args = parser.parse_args()
    if args.matrix_challenges:
        root = Path(args.matrix_challenges)
    else:
        env_root = os.environ.get("QIUSHI_PLATFORM_ROOT")
        if not env_root:
            raise SystemExit("QIUSHI_PLATFORM_ROOT not set and --matrix-challenges omitted")
        root = Path(env_root) / "runtime/releases/qiushi-matmul-1f-20260904.7/upstream/matrix-challenges"

    targets = [
        root / "challenge4/MM-22.cnf",
        root / "6pooled3and/challenge4/MM-22-63.cnf",
        root / "challenge3/MM-23-no-type3.cnf",
        root / "challenge1/MM-23-2-2-2-2-A.cnf",
        root / "challenge2/MM-23-2-2-3-A.cnf",
        root / "xor6cut/xor6cut-22.cnf",
    ]
    results = []
    for p in targets:
        if p.exists():
            results.append(inspect(p))
        else:
            results.append({"file": str(p), "exists": False})
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps({"matrix_challenges_root": str(root), "results": results}, indent=2, sort_keys=True) + "\n")
    for r in results:
        print(json.dumps({k: r.get(k) for k in ["file", "rank_from_name", "header_vars", "header_clauses", "base_only_clause_count", "base_positive_unit_count", "base_negative_unit_count", "base_nonunit_clause_count"]}, sort_keys=True))


if __name__ == "__main__":
    main()
