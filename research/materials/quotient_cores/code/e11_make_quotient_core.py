#!/usr/bin/env python3
"""Build an A-side quotient of the E11 core by the span of a prefix.

For prefix A masks P in F2^8, choose a basis of the annihilator P^perp.
The quotient map phi:F2^8 -> F2^{8-dim<P>} has coordinates l_i(x).
The projected core has slices T_i = sum_a l_i(e_a) T_a over F2.
If a rank-19 E11 CPD contains all prefix A factors, this quotient tensor has
rank at most 19-len(prefix).  Therefore an UNSAT rank test on this quotient is
an exact refutation of the whole prefix subtree.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np


def parity(x: int) -> int:
    return int(x).bit_count() & 1


def gf2_basis(vectors: list[int]) -> list[int]:
    basis: dict[int, int] = {}
    for v in vectors:
        x = int(v)
        while x:
            p = x.bit_length() - 1
            if p in basis:
                x ^= basis[p]
            else:
                basis[p] = x
                break
    return [basis[p] for p in sorted(basis.keys(), reverse=True)]


def rank(vectors: list[int]) -> int:
    return len(gf2_basis(vectors))


def annihilator_basis(prefix: list[int], n: int = 8) -> list[int]:
    # Nullspace of the row span under the standard dot product, returned as
    # independent covectors encoded by n-bit masks.
    candidates = [l for l in range(1, 1 << n) if all(parity(l & v) == 0 for v in prefix)]
    out: list[int] = []
    for l in candidates:
        if rank(out + [l]) > len(out):
            out.append(l)
        if len(out) == n - rank(prefix):
            break
    if len(out) != n - rank(prefix):
        raise RuntimeError("annihilator basis construction failed")
    return out


def quotient_core(core: np.ndarray, ann: list[int]) -> np.ndarray:
    q = np.zeros((len(ann), core.shape[1], core.shape[2]), dtype=np.uint8)
    for i, l in enumerate(ann):
        sl = np.zeros(core.shape[1:], dtype=np.uint8)
        for a in range(core.shape[0]):
            if (l >> a) & 1:
                sl ^= core[a].astype(np.uint8)
        q[i] = sl
    return q


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--core", type=Path, default=Path("data/restricted_cores/mask_001_E11_core.npy"))
    ap.add_argument("--prefix", required=True)
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--outdir", type=Path, required=True)
    ap.add_argument("--name", default="quotient")
    args = ap.parse_args()

    prefix = [int(x) for x in args.prefix.split(",") if x.strip()]
    core = np.load(args.core).astype(np.uint8) & 1
    d = rank(prefix)
    ann = annihilator_basis(prefix, core.shape[0])
    q = quotient_core(core, ann)
    args.outdir.mkdir(parents=True, exist_ok=True)
    npy = args.outdir / f"{args.name}.npy"
    np.save(npy, q)
    rec = {
        "purpose": "A-side quotient core for exact prefix subtree rank test",
        "field": "F2",
        "source_core": str(args.core),
        "prefix": prefix,
        "prefix_size": len(prefix),
        "prefix_span_dim": d,
        "quotient_dim": len(ann),
        "annihilator_basis_masks": ann,
        "projected_core_shape": list(q.shape),
        "projected_core_nnz": int(q.sum()),
        "necessary_remaining_rank_bound": int(args.rank - len(prefix)),
        "npy_path": str(npy),
        "meaning": "If this projected tensor has rank greater than rank-prefix_size, no E11 rank decomposition containing the prefix exists. A SAT quotient decomposition is only necessary evidence, not a completion of the original prefix.",
    }
    out = args.outdir / f"{args.name}.json"
    out.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n")
    print(json.dumps(rec, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
