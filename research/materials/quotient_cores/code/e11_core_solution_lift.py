#!/usr/bin/env python3
"""Lift and verify an E11 core CPD over F2 to a full T333 CPD.

Input is an .npz with U,V,W arrays for the E11 8x9x9 core, or masks
u_masks/v_masks/w_masks.  The lift embeds U into the full A-coordinate complement
of E00 and adds the three omitted elementary products (E00,B00,C00),
(E00,B01,C01), (E00,B02,C02), in this investigation's row-major convention.

For a rank-19 core witness this produces a rank-22 full F2 matrix-multiplication
scheme; for rank-21 controls it produces a verified rank-24 scheme.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np


def vec_to_mask(row) -> int:
    out = 0
    for i, b in enumerate(list(row)):
        if int(b) & 1:
            out |= 1 << i
    return out


def vec_from_mask(mask: int, n: int) -> np.ndarray:
    return np.array([(int(mask) >> i) & 1 for i in range(n)], dtype=np.uint8)


def build_t333() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3 * i + j, 3 * j + k, 3 * i + k] = 1
    return T


def reconstruct(terms: list[tuple[int, int, int]], dims=(9, 9, 9)) -> np.ndarray:
    T = np.zeros(dims, dtype=np.uint8)
    for u, v, w in terms:
        U = vec_from_mask(u, dims[0]).reshape(-1, 1, 1)
        V = vec_from_mask(v, dims[1]).reshape(1, -1, 1)
        W = vec_from_mask(w, dims[2]).reshape(1, 1, -1)
        T ^= (U * V * W).astype(np.uint8)
    return T


def load_terms(npz_path: Path) -> list[tuple[int, int, int]]:
    data = np.load(npz_path)
    if all(k in data.files for k in ("u_masks", "v_masks", "w_masks")):
        us = [int(x) for x in data["u_masks"].tolist()]
        vs = [int(x) for x in data["v_masks"].tolist()]
        ws = [int(x) for x in data["w_masks"].tolist()]
    elif all(k in data.files for k in ("U", "V", "W")):
        U = data["U"].astype(np.uint8) & 1
        V = data["V"].astype(np.uint8) & 1
        W = data["W"].astype(np.uint8) & 1
        us = [vec_to_mask(row) for row in U]
        vs = [vec_to_mask(row) for row in V]
        ws = [vec_to_mask(row) for row in W]
    else:
        raise ValueError(f"{npz_path} lacks U,V,W or u_masks,v_masks,w_masks")
    if not (len(us) == len(vs) == len(ws)):
        raise ValueError("factor lengths differ")
    return list(zip(us, vs, ws))


def build_e11_core() -> np.ndarray:
    T = build_t333()
    return T[1:9].copy()


def save_npz(path: Path, terms: list[tuple[int, int, int]], dims=(9, 9, 9)):
    U = np.zeros((len(terms), dims[0]), dtype=np.uint8)
    V = np.zeros((len(terms), dims[1]), dtype=np.uint8)
    W = np.zeros((len(terms), dims[2]), dtype=np.uint8)
    for t, (u, v, w) in enumerate(terms):
        U[t] = vec_from_mask(u, dims[0])
        V[t] = vec_from_mask(v, dims[1])
        W[t] = vec_from_mask(w, dims[2])
    path.parent.mkdir(parents=True, exist_ok=True)
    np.savez(path, U=U, V=V, W=W, u_masks=np.array([u for u, v, w in terms], dtype=np.uint16), v_masks=np.array([v for u, v, w in terms], dtype=np.uint16), w_masks=np.array([w for u, v, w in terms], dtype=np.uint16))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--core-npz", type=Path, required=True)
    ap.add_argument("--out-json", type=Path, required=True)
    ap.add_argument("--out-npz", type=Path, default=None)
    args = ap.parse_args()

    core_terms = load_terms(args.core_npz)
    core_rank = len(core_terms)
    core_T = build_e11_core()
    core_recon = reconstruct(core_terms, dims=(8, 9, 9))
    core_ok = bool(np.array_equal(core_recon, core_T))
    core_diff = int(np.sum(core_recon ^ core_T))

    # E11 complement is full A bits 1..8, so an 8-bit core u embeds by shifting left one bit.
    full_terms = [(int(u) << 1, int(v), int(w)) for u, v, w in core_terms]
    removed_terms = [(1, 1, 1), (1, 2, 2), (1, 4, 4)]
    full_terms += removed_terms
    full_T = build_t333()
    full_recon = reconstruct(full_terms, dims=(9, 9, 9))
    full_ok = bool(np.array_equal(full_recon, full_T))
    full_diff = int(np.sum(full_recon ^ full_T))

    out_npz = args.out_npz or args.out_json.with_suffix(".full_t333.npz")
    save_npz(out_npz, full_terms, dims=(9, 9, 9))

    result = {
        "statement": "An E11 core rank-r CPD lifts over F2 to a full T333 rank-(r+3) CPD by shifting A masks into bits 1..8 and adding the three E00 row products.",
        "input_core_npz": str(args.core_npz),
        "core_rank": core_rank,
        "core_verified": core_ok,
        "core_diff_count": core_diff,
        "full_rank": len(full_terms),
        "full_verified": full_ok,
        "full_diff_count": full_diff,
        "removed_terms": removed_terms,
        "full_npz": str(out_npz),
    }
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    if not core_ok or not full_ok:
        raise SystemExit("lift verification failed")


if __name__ == "__main__":
    main()
