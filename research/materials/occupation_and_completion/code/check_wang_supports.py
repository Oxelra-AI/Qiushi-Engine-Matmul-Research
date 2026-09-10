#!/usr/bin/env python3
"""Check stored A-multiset controls against Wang LUT inequalities.

For E11 controls, rows are E11-containing subspaces projected to quotient.  For
full controls, rows are all F2^9 subspaces.  This is independent of the native
DFS and confirms whether a known A-multiset is a valid positive control for a
chosen length.
"""
from __future__ import annotations

import argparse, json, sys
from collections import Counter
from pathlib import Path

S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import rref_basis, unpack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
MASK9 = (1 << 9) - 1


def contains_e11(key: int) -> bool:
    d = key & 0xF
    return d > 0 and (((key >> (4 + 9 * (d - 1))) & MASK9) == 1)


def key9_to_basis8(key9: int):
    raw = []
    for b in unpack_basis(key9):
        if b == 1:
            continue
        q = int(b)
        if q & 1:
            q ^= 1
        q8 = 0
        for bit in range(1, 9):
            if (q >> bit) & 1:
                q8 |= 1 << (bit - 1)
        if q8:
            raw.append(q8)
    return tuple(rref_basis(raw, n=8)) if raw else tuple()


def points_from_basis(basis):
    pts = []
    d = len(basis)
    for m in range(1, 1 << d):
        v = 0
        for i, b in enumerate(basis):
            if (m >> i) & 1:
                v ^= int(b)
        pts.append(v)
    return pts


def check_e11(a_multiset, length, max_cap=None):
    lut, _ = load_lut(LUT_PATH)
    cnt = Counter(int(x) for x in a_multiset)
    violations = []
    checked = 0
    for key9, lb0 in lut.items():
        key9 = int(key9)
        if not contains_e11(key9):
            continue
        lb = int(lb0)
        cap = length - lb
        if max_cap is not None and (cap < 0 or cap > max_cap):
            continue
        basis8 = key9_to_basis8(key9)
        pts = set(points_from_basis(basis8))
        occ = sum(cnt[p] for p in pts)
        checked += 1
        if occ > cap:
            violations.append({"key9": key9, "lb": lb, "cap": cap, "occ": occ, "dim8": len(basis8), "basis8": list(map(int, basis8))})
            if len(violations) >= 20:
                break
    return checked, violations


def check_full(a_multiset, length, max_cap=None):
    lut, _ = load_lut(LUT_PATH)
    cnt = Counter(int(x) for x in a_multiset)
    violations = []
    checked = 0
    for key9, lb0 in lut.items():
        key9 = int(key9)
        lb = int(lb0)
        cap = length - lb
        if max_cap is not None and (cap < 0 or cap > max_cap):
            continue
        basis = list(unpack_basis(key9))
        pts = set(points_from_basis(basis))
        occ = sum(cnt[p] for p in pts)
        checked += 1
        if occ > cap:
            violations.append({"key9": key9, "lb": lb, "cap": cap, "occ": occ, "dim": len(basis), "basis": list(map(int, basis))})
            if len(violations) >= 20:
                break
    return checked, violations


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--support", type=Path, required=True)
    ap.add_argument("--mode", choices=["e11", "full"], required=True)
    ap.add_argument("--length", type=int, required=True)
    ap.add_argument("--max-cap", type=int, default=None)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    data = json.loads(args.support.read_text())
    a = data["a_multiset"]
    if args.mode == "e11":
        checked, viol = check_e11(a, args.length, args.max_cap)
    else:
        checked, viol = check_full(a, args.length, args.max_cap)
    out = {
        "support": str(args.support),
        "mode": args.mode,
        "length": args.length,
        "max_cap": args.max_cap,
        "rank_terms_in_support": len(a),
        "distinct_count": len(set(a)),
        "checked_rows": checked,
        "violations": len(viol),
        "violation_head": viol,
        "accepted": len(viol) == 0,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps(out, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
