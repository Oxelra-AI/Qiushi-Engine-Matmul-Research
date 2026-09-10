#!/usr/bin/env python3
"""Verify the parsed rank-23 text scheme over F2 against T_{3,3,3}."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
from extract_known_supports import parse_rank23_txt

SRC = Path("data/flip_cpd_inspect/src/khoruzhii-flip-cpd-9eeb17f/data/schemes_paper/gg-333-rank23-rec-0-0-0-z.txt")
OUT = Path("data/wang_native/controls/full_rank23_text_verify.json")


def build_t333():
    T = np.zeros((9,9,9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T


def vec(mask, n=9):
    return np.array([(int(mask)>>i)&1 for i in range(n)], dtype=np.uint8)


def recon(terms):
    T = np.zeros((9,9,9), dtype=np.uint8)
    for u,v,w in terms:
        T ^= (vec(u).reshape(9,1,1) * vec(v).reshape(1,9,1) * vec(w).reshape(1,1,9)).astype(np.uint8)
    return T


def main():
    terms = parse_rank23_txt(SRC)
    T = build_t333()
    R = recon(terms)
    diff_positions = np.argwhere(R != T)
    out = {
        "source": str(SRC),
        "rank": len(terms),
        "verified_over_F2": len(diff_positions) == 0,
        "diff_count": int(len(diff_positions)),
        "diff_head": diff_positions[:20].tolist(),
        "a_distinct_count": len(set(t[0] for t in terms)),
        "a_duplicate_count": len(terms) - len(set(t[0] for t in terms)),
        "a_multiset": [int(t[0]) for t in terms],
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps(out, indent=2, sort_keys=True))
    if not out["verified_over_F2"]:
        raise SystemExit(1)

if __name__ == "__main__":
    main()
