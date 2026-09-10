#!/usr/bin/env python3
"""analysis: reconstruct lift-derived quotient constraints in one canonical representation.

This script deliberately does not reuse analysis quotient-mask arithmetic.  It uses
subspace bases and the analysis quotient convention: for a pivot q, clear the
highest set bit of q and delete that coordinate.  Quotient point p is stored in
E11WANG1 masks at bit p (not p-1), matching pair_prop_dfs.cpp.

For pivot q and quotient subspace U <= F2^8 (dim <= 3 here):
  * q-containing full row W=<q,s(U)> gives the ordinary quotient capacity
        |S cap U| <= 19 - L(W)
    for the 19 non-pivot terms of a hypothetical length-20 decomposition.
    This should match the existing quotient row binary; it is not exported as
    new lift information.
  * graph rows W_alpha={s(u)+alpha(u)q : u in U} avoiding q give constraints
        #{p in S cap U : eps_p = alpha(p)} <= 20 - L(W_alpha).
    Averaging over all 2^d alpha gives the sound occupation bound
        |S cap U| <= floor(sum_alpha (20-L(W_alpha))/2^(d-1)).
    We compare this bound with the ordinary quotient capacity and export only
    genuinely stronger nontrivial rows.
"""
from __future__ import annotations

import hashlib
import json
import struct
import sys
import time
from collections import Counter
from itertools import combinations, product
from pathlib import Path
from typing import Iterable, Sequence

ROOT = Path("research/research_record")
S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import rref_basis, pack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUTDIR = ROOT / "workspace/data/quotient_lift"
OUTDIR.mkdir(parents=True, exist_ok=True)
PIVOTS = {"rank2": 17, "rank3": 273}
QBINS = {
    "rank2": ROOT / "workspace/data/quotient_dfs/rank2_cap5_n19.bin",
    "rank3": ROOT / "workspace/data/quotient_dfs/rank3_cap5_n19.bin",
}
PEER_RANK2_SUPPORT = [1,3,9,33,99,128,132,144,148,160,184,189,192,198,209,215,224,249,254]


def sha_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def section_lift(qpoint: int, pivot: int) -> int:
    """Canonical section Q -> V: insert 0 at the highest pivot bit."""
    h = pivot.bit_length() - 1
    low = qpoint & ((1 << h) - 1)
    high = (qpoint >> h) << (h + 1)
    return low | high


def quotient_project(a: int, pivot: int) -> int:
    """Canonical V -> V/<pivot>: clear highest pivot bit using pivot, then delete it."""
    if a == 0 or a == pivot:
        return 0
    h = pivot.bit_length() - 1
    if (a >> h) & 1:
        a ^= pivot
    low = a & ((1 << h) - 1)
    high = (a >> (h + 1)) << h
    return low | high


def points_of_basis(basis: Sequence[int]) -> list[int]:
    pts: list[int] = []
    d = len(basis)
    for m in range(1, 1 << d):
        v = 0
        for i, b in enumerate(basis):
            if (m >> i) & 1:
                v ^= int(b)
        pts.append(v)
    return sorted(pts)


def mask_from_points(points: Iterable[int]) -> int:
    mask = 0
    for p in points:
        if p < 1 or p > 255:
            raise ValueError(f"bad quotient point {p}")
        mask |= 1 << p  # IMPORTANT: native DFS uses bit p, not bit p-1.
    return mask


def words_from_mask(mask: int) -> tuple[int, int, int, int]:
    return tuple((mask >> (64 * i)) & ((1 << 64) - 1) for i in range(4))  # type: ignore[return-value]


def load_e11wang1(path: Path) -> tuple[list[tuple[int, int, int]], dict[int, int]]:
    rows: list[tuple[int, int, int]] = []
    best: dict[int, int] = {}
    with path.open("rb") as f:
        magic = f.read(8)
        if magic != b"E11WANG1":
            raise ValueError(f"bad magic {magic!r} in {path}")
        n = struct.unpack("<I", f.read(4))[0]
        for _ in range(n):
            cap = struct.unpack("<B", f.read(1))[0]
            dim = struct.unpack("<B", f.read(1))[0]
            _res = struct.unpack("<H", f.read(2))[0]
            words = list(struct.unpack("<4Q", f.read(32)))
            mask = 0
            for i, w in enumerate(words):
                mask |= int(w) << (64 * i)
            rows.append((cap, dim, mask))
            if mask not in best or cap < best[mask]:
                best[mask] = cap
    return rows, best


def rref_subspace_bases(n: int, d: int) -> list[tuple[int, ...]]:
    """Enumerate RREF bases using highest-bit pivots, matching wang_capacity_lazy."""
    if d == 0:
        return [tuple()]
    out: list[tuple[int, ...]] = []
    for pivs_asc in combinations(range(n), d):
        pivs = tuple(sorted(pivs_asc, reverse=True))
        free_positions_per_row = []
        for p in pivs:
            free = [j for j in range(p) if j not in pivs]
            free_positions_per_row.append(free)
        total_free = sum(len(free) for free in free_positions_per_row)
        # Iterate assignments row by row.
        for assignment in range(1 << total_free):
            rows: list[int] = []
            bitpos = 0
            for p, free in zip(pivs, free_positions_per_row):
                row = 1 << p
                for j in free:
                    if (assignment >> bitpos) & 1:
                        row |= 1 << j
                    bitpos += 1
                rows.append(row)
            # A cheap consistency assertion on a small sample is handled outside.
            out.append(tuple(rows))
    return out


def lut_lb(lut: dict, basis9: Sequence[int]) -> int:
    rb = rref_basis(basis9, n=9)
    key = int(pack_basis(rb))
    if key not in lut:
        raise KeyError(f"missing LUT key for basis {basis9} rref {rb}")
    return int(lut[key])


def peer_mask() -> int:
    return mask_from_points(PEER_RANK2_SUPPORT)


def write_e11wang1(path: Path, rows: list[tuple[int, int, int]]) -> str:
    data = bytearray()
    data.extend(b"E11WANG1")
    data.extend(struct.pack("<I", len(rows)))
    for cap, dim, mask in rows:
        data.extend(struct.pack("<BBH", int(cap), int(dim), 0))
        for w in words_from_mask(mask):
            data.extend(struct.pack("<Q", int(w)))
    path.write_bytes(bytes(data))
    return sha_bytes(bytes(data))


def analyze_pivot(name: str, pivot: int, lut: dict, subspaces_by_dim: dict[int, list[tuple[int, ...]]]) -> dict:
    qrows, qbest = load_e11wang1(QBINS[name])
    qbin_sha = sha_file(QBINS[name])
    record: dict = {
        "pivot": pivot,
        "quotient_binary": str(QBINS[name]),
        "quotient_binary_sha256": qbin_sha,
        "quotient_rows": len(qrows),
        "quotient_distinct_masks": len(qbest),
        "qcontaining_identity_dim_le_3": {},
        "dc_dim_le_3": {},
    }

    dc_rows: list[tuple[int, int, int]] = []
    all_dc_improvements: list[tuple[int, int, int, int, int, int]] = []  # mask,dc,qcap,d,k,capsum
    peer_m = peer_mask() if name == "rank2" else None
    corrected_q_peer_viol = 0
    corrected_dc_peer_viol = 0
    corrected_dc_peer_viol_head = []

    # q-containing identity and graph averaging, for quotient dimensions 1..3.
    qid = {
        "tested_subspaces": 0,
        "with_cap_le_5": 0,
        "missing_from_quotient_binary": 0,
        "cap_mismatch": 0,
        "cap_hist": Counter(),
        "mismatch_head": [],
    }
    dc = {
        "tested_subspaces": 0,
        "missing_graph_lut_keys": 0,
        "dc_cap_hist": Counter(),
        "quotient_cap_hist": Counter(),
        "improvement_count_all_caps": 0,
        "new_export_rows_cap_le_5": 0,
        "improvement_by_dim": Counter(),
        "export_by_cap": Counter(),
        "export_by_dim": Counter(),
        "top_examples": [],
    }

    for d in (1, 2, 3):
        for ubasis in subspaces_by_dim[d]:
            dc["tested_subspaces"] += 1
            upoints = points_of_basis(ubasis)
            umask = mask_from_points(upoints)
            k = len(upoints)
            lifts = [section_lift(u, pivot) for u in ubasis]

            # Ordinary q-containing quotient capacity.
            qcap = 19 - lut_lb(lut, [pivot] + lifts)
            qid["tested_subspaces"] += 1
            qid["cap_hist"][qcap] += 1
            dc["quotient_cap_hist"][qcap] += 1
            if qcap <= 5:
                qid["with_cap_le_5"] += 1
                got = qbest.get(umask)
                if got is None:
                    qid["missing_from_quotient_binary"] += 1
                    if len(qid["mismatch_head"]) < 10:
                        qid["mismatch_head"].append({"dim": d, "points": upoints, "qcap": qcap, "reason": "missing"})
                elif got != qcap:
                    qid["cap_mismatch"] += 1
                    if len(qid["mismatch_head"]) < 10:
                        qid["mismatch_head"].append({"dim": d, "points": upoints, "qcap": qcap, "binary_cap": got, "reason": "cap_mismatch"})
                if peer_m is not None and (peer_m & umask).bit_count() > qcap:
                    corrected_q_peer_viol += 1

            # Graph-family averaging over all linear functionals on U.
            caps = []
            for alpha in range(1 << d):
                gbasis = []
                for i, u in enumerate(ubasis):
                    v = section_lift(u, pivot)
                    if (alpha >> i) & 1:
                        v ^= pivot
                    gbasis.append(v)
                cap = 20 - lut_lb(lut, gbasis)
                caps.append(cap)
            cap_sum = sum(caps)
            dc_cap = min(k, cap_sum // (1 << (d - 1)))
            dc["dc_cap_hist"][dc_cap] += 1

            if dc_cap < qcap and dc_cap < k:
                dc["improvement_count_all_caps"] += 1
                dc["improvement_by_dim"][d] += 1
                all_dc_improvements.append((umask, dc_cap, qcap, d, k, cap_sum))
                if dc_cap <= 5:
                    dc_rows.append((dc_cap, d, umask))
                    dc["new_export_rows_cap_le_5"] += 1
                    dc["export_by_cap"][dc_cap] += 1
                    dc["export_by_dim"][d] += 1
                    if peer_m is not None:
                        occ = (peer_m & umask).bit_count()
                        if occ > dc_cap:
                            corrected_dc_peer_viol += 1
                            if len(corrected_dc_peer_viol_head) < 10:
                                corrected_dc_peer_viol_head.append({"dim": d, "cap": dc_cap, "qcap": qcap, "occ": occ, "points": upoints})
                if len(dc["top_examples"]) < 20:
                    dc["top_examples"].append({
                        "dim": d,
                        "k": k,
                        "dc_cap": dc_cap,
                        "quotient_cap": qcap,
                        "cap_sum": cap_sum,
                        "graph_caps": caps,
                        "points": upoints,
                    })

    # Sort/deduplicate dc rows by mask, keeping tightest cap.  Multiple rows for
    # the same quotient subspace should not occur in this construction, but this
    # makes the exported artifact robust.
    best_dc: dict[int, tuple[int, int]] = {}
    for cap, dim, mask in dc_rows:
        if mask not in best_dc or cap < best_dc[mask][0]:
            best_dc[mask] = (cap, dim)
    dc_rows_dedup = [(cap, dim, mask) for mask, (cap, dim) in best_dc.items()]
    dc_rows_dedup.sort(key=lambda r: (r[0], r[1], r[2]))

    bin_path = OUTDIR / f"{name}_dc_lift_rows_correct.bin"
    bin_sha = write_e11wang1(bin_path, dc_rows_dedup)

    qid_json = dict(qid)
    qid_json["cap_hist"] = {str(k): int(v) for k, v in sorted(qid["cap_hist"].items())}
    dc_json = dict(dc)
    for key in ["dc_cap_hist", "quotient_cap_hist", "improvement_by_dim", "export_by_cap", "export_by_dim"]:
        dc_json[key] = {str(k): int(v) for k, v in sorted(dc[key].items())}

    record["qcontaining_identity_dim_le_3"] = qid_json
    record["corrected_qcontaining_peer_support_violations"] = corrected_q_peer_viol if name == "rank2" else None
    record["dc_dim_le_3"] = dc_json
    record["dc_binary_path"] = str(bin_path)
    record["dc_binary_sha256"] = bin_sha
    record["dc_binary_rows"] = len(dc_rows_dedup)
    record["corrected_dc_peer_support_violations"] = corrected_dc_peer_viol if name == "rank2" else None
    record["corrected_dc_peer_support_violations_head"] = corrected_dc_peer_viol_head if name == "rank2" else None
    return record


def main() -> None:
    t0 = time.time()
    print(f"Loading LUT {LUT_PATH} ...")
    lut, lut_meta = load_lut(LUT_PATH)
    print(f"  LUT entries: {len(lut)}")
    print("Enumerating quotient subspaces dim 1..3 in canonical RREF...")
    subspaces_by_dim = {d: rref_subspace_bases(8, d) for d in (1, 2, 3)}
    # Sanity check against Gaussian counts.
    print({d: len(v) for d, v in subspaces_by_dim.items()})
    for d, bases in subspaces_by_dim.items():
        # Verify a tiny sample against imported rref_basis.
        for b in bases[:5] + bases[-5:]:
            assert tuple(b) == tuple(rref_basis(b, n=8)), (d, b, rref_basis(b, n=8))

    out = {
        "schema": "s0908_corrected_lift_constraints_v1",
        "warning": "analysis lift rows are invalid for proof use; this file reconstructs in the analysis high-pivot quotient convention and native bit-p indexing.",
        "source_lut": str(LUT_PATH),
        "source_lut_sha256": sha_file(LUT_PATH),
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "subspace_counts_dim_1_to_3": {str(d): len(v) for d, v in subspaces_by_dim.items()},
        "pivots": {},
    }
    for name, pivot in PIVOTS.items():
        print(f"\n=== {name} pivot={pivot} ===")
        rec = analyze_pivot(name, pivot, lut, subspaces_by_dim)
        out["pivots"][name] = rec
        print(json.dumps({
            "q_identity": rec["qcontaining_identity_dim_le_3"],
            "dc_binary_rows": rec["dc_binary_rows"],
            "dc_binary_sha256": rec["dc_binary_sha256"],
            "dc_summary": {k: rec["dc_dim_le_3"][k] for k in ["tested_subspaces", "dc_cap_hist", "quotient_cap_hist", "improvement_count_all_caps", "new_export_rows_cap_le_5", "export_by_cap", "export_by_dim"]},
            "peer_q_viol": rec.get("corrected_qcontaining_peer_support_violations"),
            "peer_dc_viol": rec.get("corrected_dc_peer_support_violations"),
        }, indent=2, sort_keys=True))

    out["elapsed_sec"] = time.time() - t0
    out_path = OUTDIR / "corrected_lift_constraints.json"
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(f"\nSaved {out_path} in {out['elapsed_sec']:.1f}s")


if __name__ == "__main__":
    main()
