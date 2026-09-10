#!/usr/bin/env python3
"""Canonical quotient/full-lift row comparison and graph-family bounds.

For a pivot q in the A-slot, quotient support rows from full Wang subspaces
containing q have cap 19-LB(U') at target 19, exactly equal to the full-tensor
cap20(U') minus the pivot term.  This script checks that identity against the
research quotient binaries.

For quotient subspaces U with preimage U'=<q,lift(U)>, it also computes the
non-containing graph-complement averaged bound
    |S cap U| <= floor( sum_l cap20(W_l) / 2^(dim U - 1) ),
where W_l={lift(u)+l(u)q : u in U}.  This is a sound support inequality after
summing over all lift bits.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import struct
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

SCRIPT_DIR = Path(__file__).resolve().parent
S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import pack_basis, rref_basis, unpack_basis  # type: ignore
from quotient_line_caps_and_controls import quotient_project  # type: ignore

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
BIN_DIR = Path("data/wang_native/quotient_binaries")
OUT_DIR = Path("data/quotient_lift")
MAGIC = b"E11WANG1"

KNOWN_RANK2_SUPPORT = [1,3,9,33,99,128,132,144,148,160,184,189,192,198,209,215,224,249,254]


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def gf2_reduce(v: int, basis: Sequence[int]) -> int:
    x = int(v)
    piv = {int(b).bit_length() - 1: int(b) for b in basis if b}
    while x:
        p = x.bit_length() - 1
        b = piv.get(p)
        if b is None:
            return x
        x ^= b
    return 0


def in_span(point: int, basis: Sequence[int]) -> bool:
    return gf2_reduce(point, basis) == 0


def load_lut() -> dict[int, int]:
    with LUT_PATH.open("rb") as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload["lut"].items()}


def read_binary(path: Path) -> dict[int, dict]:
    rows = {}
    with path.open("rb") as f:
        magic = f.read(8)
        if magic != MAGIC:
            raise ValueError(f"bad magic {magic!r}")
        n = struct.unpack("<I", f.read(4))[0]
        rec = struct.Struct("<BBHQQQQ")
        for idx in range(n):
            cap, dim, _pad, w0, w1, w2, w3 = rec.unpack(f.read(rec.size))
            pts = []
            for wi, w in enumerate((w0, w1, w2, w3)):
                for b in range(64):
                    p = 64 * wi + b
                    if p and ((int(w) >> b) & 1):
                        pts.append(p)
            qkey = pack_basis(rref_basis(pts, n=8))
            if qkey in rows:
                raise RuntimeError(f"duplicate qkey in binary: {qkey}")
            rows[qkey] = {"idx": idx, "cap": int(cap), "dim": int(dim), "pts": tuple(pts)}
    return rows


def canonical_lift(qv: int, pivot: int) -> int:
    """Embed quotient vector with removed pivot bit set to zero."""
    h = int(pivot).bit_length() - 1
    low = int(qv) & ((1 << h) - 1)
    high = (int(qv) >> h) << (h + 1)
    return low | high


def qkey_preimage_key(qkey: int, pivot: int) -> int:
    qb = list(unpack_basis(int(qkey)))
    basis9 = [int(pivot)] + [canonical_lift(b, pivot) for b in qb]
    return pack_basis(rref_basis(basis9, n=9))


def quotient_key_from_full_containing(key9: int, pivot: int) -> int | None:
    basis = list(unpack_basis(int(key9)))
    if not in_span(pivot, basis):
        return None
    qb = []
    for b in basis:
        q = quotient_project(int(b), pivot)
        if q:
            qb.append(q)
    return pack_basis(rref_basis(qb, n=8))


def graph_keys(qkey: int, pivot: int) -> list[int]:
    qb = list(unpack_basis(int(qkey)))
    d = len(qb)
    keys = []
    for mask in range(1 << d):
        basis9 = []
        for i, b in enumerate(qb):
            v = canonical_lift(b, pivot)
            if (mask >> i) & 1:
                v ^= int(pivot)
            basis9.append(v)
        key = pack_basis(rref_basis(basis9, n=9))
        keys.append(key)
    return keys


def words_from_pts(pts: Iterable[int]) -> tuple[int, int, int, int]:
    words = [0, 0, 0, 0]
    for p in pts:
        words[int(p) >> 6] |= 1 << (int(p) & 63)
    return tuple(words)  # type: ignore[return-value]


def support_occupancy(support: set[int], pts: Sequence[int]) -> int:
    return sum(1 for p in pts if p in support)


def scan(pivot_name: str, pivot: int, support: list[int] | None, sample_head: int) -> dict:
    t0 = time.time()
    lut = load_lut()
    bin_path = BIN_DIR / f"{pivot_name}_all_n19.bin"
    qbin = read_binary(bin_path)

    # Identity: containing full rows projected to quotient rows equal the binary rows.
    projected = {}
    containing = 0
    for key9, lb in lut.items():
        qkey = quotient_key_from_full_containing(key9, pivot)
        if qkey is None:
            continue
        containing += 1
        if qkey == 0:
            continue
        cap = 19 - int(lb)  # full target 20 cap minus the selected pivot term
        if cap < 0 or cap >= 19:
            continue
        qpts = []
        for m in range(1, 1 << len(unpack_basis(qkey))):
            # easier from qkey basis below after reading binary; compare by key/cap only here
            pass
        old = projected.get(qkey)
        if old is not None and old != cap:
            raise RuntimeError(f"same qkey different containing caps: {qkey}: {old}, {cap}")
        projected[qkey] = int(cap)

    missing_from_binary = sorted(k for k in projected if k not in qbin)
    extra_in_binary = sorted(k for k in qbin if k not in projected)
    cap_mismatches = []
    for k, cap in projected.items():
        if k in qbin and int(qbin[k]["cap"]) != cap:
            cap_mismatches.append({"qkey": int(k), "projected_cap": int(cap), "binary_cap": int(qbin[k]["cap"])})

    # Graph-complement averaged rows.
    sup = set(int(x) for x in support) if support else None
    graph_rows = []
    graph_hist_by_dim = Counter()
    tighter_hist = Counter()
    gain_hist = Counter()
    support_violations = []
    impossible_rows = []
    for qkey, row in qbin.items():
        d = int(row["dim"])
        if d <= 0:
            continue
        direct_cap = int(row["cap"])
        gkeys = graph_keys(qkey, pivot)
        cap_sum = 0
        cap_values = []
        for gk in gkeys:
            lb = int(lut[gk])
            cap20 = 20 - lb
            cap_sum += cap20
            cap_values.append(cap20)
        denom = 1 << (d - 1)
        avg_bound = cap_sum // denom
        if cap_sum % denom:
            # For integer supports floor is sound.
            avg_bound = cap_sum // denom
        graph_hist_by_dim[d] += 1
        if avg_bound < direct_cap:
            gain = direct_cap - avg_bound
            tighter_hist[(d, direct_cap, avg_bound)] += 1
            gain_hist[gain] += 1
            occ = support_occupancy(sup, row["pts"]) if sup is not None else None
            rec = {
                "qkey": int(qkey),
                "dim": d,
                "direct_cap": direct_cap,
                "graph_bound": int(avg_bound),
                "gain": int(gain),
                "graph_cap20_hist": dict(sorted(Counter(cap_values).items())),
                "pts": list(row["pts"]),
            }
            if occ is not None:
                rec["support_occ"] = int(occ)
                if occ > avg_bound:
                    support_violations.append(rec)
            graph_rows.append(rec)
        if avg_bound < 0:
            impossible_rows.append({"qkey": int(qkey), "dim": d, "graph_bound": int(avg_bound), "direct_cap": direct_cap})

    graph_rows_sorted = sorted(graph_rows, key=lambda r: (-r["gain"], r["dim"], r["direct_cap"], r["qkey"]))
    support_violations_sorted = sorted(support_violations, key=lambda r: (-r["support_occ"] + r["graph_bound"], r["dim"], r["qkey"]))

    return {
        "schema": "quotient_lift_family_scan_v1",
        "pivot_name": pivot_name,
        "pivot": int(pivot),
        "binary": str(bin_path),
        "binary_sha256": sha256(bin_path),
        "target_quotient": 19,
        "target_full": 20,
        "known_support": support,
        "containing_full_rows": containing,
        "projected_containing_rows_after_filter": len(projected),
        "binary_rows": len(qbin),
        "q_containing_identity": {
            "missing_from_binary": len(missing_from_binary),
            "extra_in_binary": len(extra_in_binary),
            "cap_mismatches": len(cap_mismatches),
            "missing_head": missing_from_binary[:sample_head],
            "extra_head": extra_in_binary[:sample_head],
            "cap_mismatch_head": cap_mismatches[:sample_head],
            "interpretation": "full rows containing the pivot give exactly the quotient Wang rows when cap20 is reduced by the selected pivot term",
        },
        "graph_family": {
            "rows_examined_by_dim": dict(sorted(graph_hist_by_dim.items())),
            "tighter_row_count": len(graph_rows),
            "gain_hist": dict(sorted(gain_hist.items())),
            "tighter_hist_head": {str(k): v for k, v in list(sorted(tighter_hist.items(), key=lambda kv: (kv[0][0], kv[0][1], kv[0][2])))[:50]},
            "tighter_rows_head": graph_rows_sorted[:sample_head],
            "impossible_rows": impossible_rows[:sample_head],
            "impossible_row_count": len(impossible_rows),
        },
        "support_test": None if sup is None else {
            "support_size": len(sup),
            "violations_of_graph_bounds": len(support_violations_sorted),
            "violation_head": support_violations_sorted[:sample_head],
        },
        "elapsed_sec": time.time() - t0,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot-name", choices=["rank2", "rank3", "e11"], required=True)
    ap.add_argument("--support", default="")
    ap.add_argument("--sample-head", type=int, default=20)
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()
    pivots = {"e11": 1, "rank2": 17, "rank3": 273}
    support = [int(x) for x in args.support.split(",") if x.strip()] if args.support else (KNOWN_RANK2_SUPPORT if args.pivot_name == "rank2" else None)
    result = scan(args.pivot_name, pivots[args.pivot_name], support, args.sample_head)
    out = args.out or (OUT_DIR / f"{args.pivot_name}_n19_lift_family_scan.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "pivot_name": args.pivot_name,
        "q_identity": result["q_containing_identity"],
        "graph_tighter_row_count": result["graph_family"]["tighter_row_count"],
        "graph_gain_hist": result["graph_family"]["gain_hist"],
        "support_violations": None if result["support_test"] is None else result["support_test"]["violations_of_graph_bounds"],
        "out": str(out),
        "elapsed_sec": round(result["elapsed_sec"], 3),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
