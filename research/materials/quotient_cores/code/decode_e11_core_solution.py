#!/usr/bin/env python3
"""Decode a SAT assignment for an E11 core CNF into a verified core CPD.

The decoder reconstructs the same base variable ordering as e11_core_sat.py,
reads DIMACS solver output containing `v ... 0` lines, extracts u/v/w masks,
verifies the 8x9x9 E11 core identity directly, and optionally saves an NPZ with
u_masks/v_masks/w_masks plus a flat `terms` row.

It deliberately does not trust auxiliary variables: only base variables are read
and the tensor identity is recomputed from scratch over F2.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent


def build_t333() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3 * i + j, 3 * j + k, 3 * i + k] = 1
    return T


def build_core() -> np.ndarray:
    return build_t333()[1:9].copy()


def vec_from_mask(mask: int, n: int) -> np.ndarray:
    return np.array([(int(mask) >> i) & 1 for i in range(n)], dtype=np.uint8)


def reconstruct(terms: List[Tuple[int, int, int]], dims=(8, 9, 9)) -> np.ndarray:
    T = np.zeros(dims, dtype=np.uint8)
    for u, v, w in terms:
        T ^= (vec_from_mask(u, dims[0]).reshape(-1, 1, 1)
              * vec_from_mask(v, dims[1]).reshape(1, -1, 1)
              * vec_from_mask(w, dims[2]).reshape(1, 1, -1)).astype(np.uint8)
    return T


def parse_assignment(path: Path) -> Dict[int, int]:
    assign: Dict[int, int] = {}
    for line in path.read_text(errors="replace").splitlines():
        line = line.strip()
        if not line or not line.startswith("v"):
            continue
        for tok in line.split()[1:]:
            lit = int(tok)
            if lit == 0:
                continue
            assign[abs(lit)] = 1 if lit > 0 else 0
    return assign


def base_var_numbers(rank: int) -> Tuple[List[List[int]], List[List[int]], List[List[int]]]:
    x = 1
    U: List[List[int]] = []
    V: List[List[int]] = []
    W: List[List[int]] = []
    for _t in range(rank):
        U.append(list(range(x, x + 8))); x += 8
        V.append(list(range(x, x + 9))); x += 9
        W.append(list(range(x, x + 9))); x += 9
    return U, V, W


def mask_from_assignment(assign: Dict[int, int], vars_bits: List[int]) -> int:
    m = 0
    missing = []
    for i, var in enumerate(vars_bits):
        if var not in assign:
            missing.append(var)
        elif assign[var] & 1:
            m |= 1 << i
    if missing:
        raise ValueError(f"assignment missing base variables: {missing[:10]}")
    return m


def lift_to_full(terms: List[Tuple[int, int, int]]) -> List[Tuple[int, int, int]]:
    removed = [(1, 1, 1), (1, 2, 2), (1, 4, 4)]
    return [(u << 1, v, w) for u, v, w in terms] + removed


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--assignment", type=Path, required=True)
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--summary", type=Path, default=None)
    args = ap.parse_args()

    assign = parse_assignment(args.assignment)
    Uvars, Vvars, Wvars = base_var_numbers(args.rank)
    terms = []
    for t in range(args.rank):
        u = mask_from_assignment(assign, Uvars[t])
        v = mask_from_assignment(assign, Vvars[t])
        w = mask_from_assignment(assign, Wvars[t])
        terms.append((u, v, w))
    core = build_core()
    rec = reconstruct(terms, (8, 9, 9))
    core_diff = int(np.sum(rec ^ core))
    nonzero_terms = [(u, v, w) for (u, v, w) in terms if u and v and w]

    full_terms = lift_to_full(terms)
    full_rec = reconstruct(full_terms, (9, 9, 9))
    full_diff = int(np.sum(full_rec ^ build_t333()))

    args.out.parent.mkdir(parents=True, exist_ok=True)
    flat = np.array([x for term in terms for x in term], dtype=np.uint16)
    np.savez_compressed(
        args.out,
        u_masks=np.array([u for u, _, _ in terms], dtype=np.uint16),
        v_masks=np.array([v for _, v, _ in terms], dtype=np.uint16),
        w_masks=np.array([w for _, _, w in terms], dtype=np.uint16),
        terms=flat,
        full_terms=np.array([x for term in full_terms for x in term], dtype=np.uint16),
    )
    summary = {
        "assignment": str(args.assignment),
        "rank": args.rank,
        "npz": str(args.out),
        "assignment_vars_read": len(assign),
        "terms": [list(t) for t in terms],
        "nonzero_term_count_strict_uvw": len(nonzero_terms),
        "core_diff_count": core_diff,
        "core_verified": core_diff == 0,
        "full_lift_rank": len(full_terms),
        "full_diff_count": full_diff,
        "full_verified": full_diff == 0,
        "meaning": "core_verified with rank 19 gives an E11 rank-19 CPD; full_verified then gives T333 rank <=22 over F2 by the deleted-slice bridge.",
    }
    if args.summary is None:
        args.summary = args.out.with_suffix(args.out.suffix + ".summary.json")
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.summary.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "status": "ok",
        "npz": str(args.out),
        "summary": str(args.summary),
        "core_verified": core_diff == 0,
        "core_diff_count": core_diff,
        "full_verified": full_diff == 0,
        "full_diff_count": full_diff,
        "strict_nonzero_terms": len(nonzero_terms),
    }, indent=2, sort_keys=True))
    if core_diff != 0:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
