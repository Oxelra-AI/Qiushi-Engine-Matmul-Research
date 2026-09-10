#!/usr/bin/env python3
"""Orbit-averaged LPs for full Wang occupation systems.

For the full A-side Wang row family and a fixed pivot p, average any feasible
LP solution over Stab(p).  Feasibility is then exactly captured by one variable
per Stab(p)-orbit of nonzero full A-directions.  This script streams a WANG512
binary, aggregates rows by their orbit-count coefficient vector, and solves the
resulting small LP.

It also supports the fully GL3xGL3 averaged root LP, with one variable for each
matrix-rank orbit (rank 1,2,3).  These LPs do not settle integrality, but they
show whether a Farkas/linear proof exists inside the current Wang-row system.
"""
from __future__ import annotations

import argparse
import json
import os
import struct
import sys
import time
from collections import Counter, defaultdict, deque
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
from quotient_line_caps_and_controls import bits_to_mat, mat_to_bits, gf2_inv, gl3, gf2_rank_mat  # type: ignore

MAGIC = b"WANG512\x01"
OUTDIR = Path("data/orbit_lp")


def bit_in(words: Tuple[int, ...], p: int) -> bool:
    return bool((int(words[p >> 6]) >> (p & 63)) & 1)


def points_in_words(words: Tuple[int, ...]) -> List[int]:
    pts: List[int] = []
    for wi, w0 in enumerate(words):
        w = int(w0)
        while w:
            lb = w & -w
            b = lb.bit_length() - 1
            p = wi * 64 + b
            if 1 <= p <= 511:
                pts.append(p)
            w ^= lb
    return pts


def popcount_words(words: Tuple[int, ...]) -> int:
    return sum(int(w).bit_count() for w in words)


def load_binary_rows(path: Path):
    with path.open("rb") as f:
        magic = f.read(8)
        if magic != MAGIC:
            raise ValueError(f"bad magic {magic!r} in {path}")
        nrows = struct.unpack("<I", f.read(4))[0]
        for idx in range(nrows):
            cap, dim, _res = struct.unpack("<BBH", f.read(4))
            words = struct.unpack("<8Q", f.read(64))
            yield idx, int(cap), int(dim), tuple(int(w) for w in words)


def binary_header(path: Path) -> Dict:
    size = path.stat().st_size
    with path.open("rb") as f:
        magic = f.read(8)
        nrows = struct.unpack("<I", f.read(4))[0]
    return {
        "path": str(path),
        "magic": magic.decode("latin1"),
        "nrows": int(nrows),
        "size_bytes": int(size),
        "expected_size_bytes": int(12 + 68 * nrows),
        "size_matches": bool(size == 12 + 68 * nrows),
    }


def full_transform_point(a: int, P: np.ndarray, Q: np.ndarray) -> int:
    A = bits_to_mat(int(a))
    QinvT = gf2_inv(Q).T % 2
    B = (P.T @ A @ QinvT) % 2
    return int(mat_to_bits(B))


def compute_stabilizer(pivot: int) -> List[Tuple[np.ndarray, np.ndarray]]:
    A = bits_to_mat(int(pivot))
    out: List[Tuple[np.ndarray, np.ndarray]] = []
    G = gl3()
    for P in G:
        for Q in G:
            if full_transform_point(pivot, P, Q) == pivot:
                out.append((P.copy(), Q.copy()))
    return out


def full_point_orbits_under_stabilizer(pivot: int) -> Dict:
    stab = compute_stabilizer(pivot)
    visited = set()
    orbits: List[List[int]] = []
    for a in range(1, 512):
        if a in visited:
            continue
        orb = set(full_transform_point(a, P, Q) for P, Q in stab)
        # closure for safety; the image set under the whole group should already be closed
        changed = True
        while changed:
            changed = False
            for x in list(orb):
                for P, Q in stab:
                    y = full_transform_point(x, P, Q)
                    if y not in orb:
                        orb.add(y); changed = True
        so = sorted(orb)
        orbits.append(so)
        visited |= orb
    # Put pivot singleton first for readability if present.
    orbits.sort(key=lambda o: (0 if pivot in o else 1, len(o), o[0]))
    point_to_orbit = {}
    for i, o in enumerate(orbits):
        for a in o:
            point_to_orbit[a] = i
    rank_hist_by_orbit = []
    for o in orbits:
        rank_hist_by_orbit.append(dict(sorted(Counter(int(gf2_rank_mat(bits_to_mat(a))) for a in o).items())))
    return {
        "pivot": int(pivot),
        "stabilizer_size": len(stab),
        "num_orbits": len(orbits),
        "orbit_sizes": [len(o) for o in orbits],
        "orbit_reps": [o[0] for o in orbits],
        "orbits": orbits,
        "rank_hist_by_orbit": rank_hist_by_orbit,
        "point_to_orbit": point_to_orbit,
    }


def matrix_rank(a: int) -> int:
    return int(gf2_rank_mat(bits_to_mat(int(a))))


def solve_lp_from_constraints(num_vars: int, constraints: Dict[Tuple[int, ...], Dict], equal_coeffs: List[int], equal_rhs: int, bounds: List[Tuple[float, float]]) -> Dict:
    rows = []
    cols = []
    vals = []
    b = []
    key_list = list(constraints.keys())
    for ri, coeff in enumerate(key_list):
        for j, v in enumerate(coeff):
            if v:
                rows.append(ri); cols.append(j); vals.append(float(v))
        b.append(float(constraints[coeff]["rhs_min"]))
    A_ub = coo_matrix((vals, (rows, cols)), shape=(len(key_list), num_vars)).tocsr() if key_list else None
    A_eq = np.array([equal_coeffs], dtype=float)
    b_eq = np.array([float(equal_rhs)], dtype=float)
    c = np.zeros(num_vars)
    t0 = time.time()
    res = linprog(c, A_ub=A_ub, b_ub=np.array(b, dtype=float) if b else None,
                  A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs")
    elapsed = time.time() - t0
    out = {
        "status": int(res.status),
        "message": str(res.message),
        "success": bool(res.success),
        "elapsed_sec": elapsed,
        "num_constraints": len(key_list),
        "num_vars": num_vars,
    }
    if res.x is not None:
        out["solution"] = [float(x) for x in res.x]
        slacks = None
        try:
            if A_ub is not None:
                sl = np.array(b, dtype=float) - A_ub.dot(res.x)
                out["min_slack"] = float(sl.min()) if len(sl) else None
                out["near_binding_count_1e-7"] = int(np.sum(sl <= 1e-7)) if len(sl) else 0
                # Store a small sample of binding coefficient rows and their metadata.
                inds = np.where(sl <= 1e-7)[0][:30]
                out["binding_sample"] = []
                for ii in inds:
                    coeff = key_list[int(ii)]
                    meta = constraints[coeff]
                    out["binding_sample"].append({
                        "coeff": list(map(int, coeff)),
                        "rhs": int(meta["rhs_min"]),
                        "count": int(meta["count"]),
                        "p_contains_count": int(meta.get("p_contains_count", 0)),
                        "nonp_count": int(meta.get("nonp_count", 0)),
                        "dim_hist": dict(sorted((str(k), int(v)) for k, v in meta.get("dim_hist", {}).items())),
                        "cap_hist": dict(sorted((str(k), int(v)) for k, v in meta.get("cap_hist", {}).items())),
                    })
        except Exception as e:
            out["slack_error"] = repr(e)
    return out


def aggregate_pivot_lp(binary: Path, pivot: int, length: int, pivot_mult: int = 1, include_p_containing: bool = True, include_nonp: bool = True) -> Dict:
    t0 = time.time()
    orbit_data = full_point_orbits_under_stabilizer(pivot)
    p2o = orbit_data["point_to_orbit"]
    pivot_orbit = p2o[pivot]
    var_orbits = [i for i in range(orbit_data["num_orbits"]) if i != pivot_orbit]
    orbit_to_var = {o: i for i, o in enumerate(var_orbits)}
    var_sizes = [len(orbit_data["orbits"][o]) for o in var_orbits]
    var_reps = [orbit_data["orbits"][o][0] for o in var_orbits]
    var_rank_hists = [orbit_data["rank_hist_by_orbit"][o] for o in var_orbits]
    constraints: Dict[Tuple[int, ...], Dict] = {}
    raw_rows = 0
    used_rows = 0
    skipped_by_family = 0
    rhs_negative = 0
    rhs_hist = Counter(); dim_hist = Counter(); cap_hist = Counter(); p_cont_hist = Counter()
    for idx, cap, dim, words in load_binary_rows(binary):
        raw_rows += 1
        pcont = bit_in(words, pivot)
        if (pcont and not include_p_containing) or ((not pcont) and not include_nonp):
            skipped_by_family += 1
            continue
        rhs = int(cap) - (pivot_mult if pcont else 0)
        if rhs < 0:
            rhs_negative += 1
        coeff = [0] * len(var_orbits)
        for a in points_in_words(words):
            if a == pivot:
                continue
            oi = p2o[a]
            vi = orbit_to_var.get(oi)
            if vi is not None:
                coeff[vi] += 1
        tup = tuple(coeff)
        # Skip tautological empty rows unless rhs is negative.
        if not any(coeff) and rhs >= 0:
            continue
        rec = constraints.get(tup)
        if rec is None or rhs < rec["rhs_min"]:
            constraints[tup] = {
                "rhs_min": int(rhs),
                "row_index_min_rhs": int(idx),
                "cap_at_min_rhs": int(cap),
                "dim_at_min_rhs": int(dim),
                "p_contains_at_min_rhs": bool(pcont),
                "count": 1 if rec is None else rec.get("count", 0) + 1,
                "p_contains_count": (1 if pcont else 0) + (0 if rec is None else rec.get("p_contains_count", 0)),
                "nonp_count": (0 if pcont else 1) + (0 if rec is None else rec.get("nonp_count", 0)),
                "dim_hist": Counter({dim: 1}) + (Counter() if rec is None else rec.get("dim_hist", Counter())),
                "cap_hist": Counter({cap: 1}) + (Counter() if rec is None else rec.get("cap_hist", Counter())),
            }
        else:
            rec["count"] += 1
            if pcont: rec["p_contains_count"] += 1
            else: rec["nonp_count"] += 1
            rec["dim_hist"][dim] += 1
            rec["cap_hist"][cap] += 1
        used_rows += 1
        rhs_hist[rhs] += 1; dim_hist[dim] += 1; cap_hist[cap] += 1; p_cont_hist["p" if pcont else "nonp"] += 1
    ub = max(1, length - 19)
    bounds = [(0.0, float(ub)) for _ in var_orbits]
    lp = solve_lp_from_constraints(len(var_orbits), constraints, var_sizes, length - pivot_mult, bounds)
    return {
        "schema": "pivot_fixed_orbit_lp_v1",
        "binary": binary_header(binary),
        "pivot": int(pivot),
        "pivot_rank": matrix_rank(pivot),
        "length": int(length),
        "pivot_mult": int(pivot_mult),
        "include_p_containing": bool(include_p_containing),
        "include_nonp": bool(include_nonp),
        "orbit_data_summary": {k: orbit_data[k] for k in ["pivot", "stabilizer_size", "num_orbits", "orbit_sizes", "orbit_reps", "rank_hist_by_orbit"]},
        "pivot_orbit": int(pivot_orbit),
        "var_orbits": var_orbits,
        "var_orbit_sizes": var_sizes,
        "var_orbit_reps": var_reps,
        "var_rank_hists": var_rank_hists,
        "raw_rows": int(raw_rows),
        "used_rows": int(used_rows),
        "skipped_by_family": int(skipped_by_family),
        "rhs_negative": int(rhs_negative),
        "unique_coeff_rows": int(len(constraints)),
        "p_contains_hist": dict(p_cont_hist),
        "dim_hist_used": dict(sorted((int(k), int(v)) for k, v in dim_hist.items())),
        "cap_hist_used": dict(sorted((int(k), int(v)) for k, v in cap_hist.items())),
        "rhs_hist_used": dict(sorted((int(k), int(v)) for k, v in rhs_hist.items())),
        "lp": lp,
        "elapsed_sec": time.time() - t0,
    }


def aggregate_root_lp(binary: Path, length: int) -> Dict:
    constraints: Dict[Tuple[int, ...], Dict] = {}
    raw_rows = 0; used_rows = 0
    dim_hist = Counter(); cap_hist = Counter()
    rank_size = {1: 49, 2: 294, 3: 168}
    for idx, cap, dim, words in load_binary_rows(binary):
        raw_rows += 1
        coeff = [0, 0, 0]
        for a in points_in_words(words):
            r = matrix_rank(a)
            if r:
                coeff[r-1] += 1
        tup = tuple(coeff)
        if not any(coeff):
            continue
        rec = constraints.get(tup)
        if rec is None or cap < rec["rhs_min"]:
            constraints[tup] = {
                "rhs_min": int(cap),
                "row_index_min_rhs": int(idx),
                "count": 1 if rec is None else rec.get("count", 0) + 1,
                "dim_hist": Counter({dim: 1}) + (Counter() if rec is None else rec.get("dim_hist", Counter())),
                "cap_hist": Counter({cap: 1}) + (Counter() if rec is None else rec.get("cap_hist", Counter())),
            }
        else:
            rec["count"] += 1; rec["dim_hist"][dim] += 1; rec["cap_hist"][cap] += 1
        used_rows += 1; dim_hist[dim] += 1; cap_hist[cap] += 1
    ub = max(1, length - 19)
    lp = solve_lp_from_constraints(3, constraints, [rank_size[1], rank_size[2], rank_size[3]], length, [(0.0, float(ub))]*3)
    return {
        "schema": "root_rank_orbit_lp_v1",
        "binary": binary_header(binary),
        "length": int(length),
        "rank_orbit_sizes": rank_size,
        "raw_rows": int(raw_rows),
        "used_rows": int(used_rows),
        "unique_coeff_rows": int(len(constraints)),
        "dim_hist_used": dict(sorted((int(k), int(v)) for k, v in dim_hist.items())),
        "cap_hist_used": dict(sorted((int(k), int(v)) for k, v in cap_hist.items())),
        "lp": lp,
    }


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("pivot")
    p.add_argument("--binary", type=Path, required=True)
    p.add_argument("--pivot", type=int, required=True)
    p.add_argument("--length", type=int, required=True)
    p.add_argument("--pivot-mult", type=int, default=1)
    p.add_argument("--only", choices=["all", "p", "nonp"], default="all")
    p.add_argument("--out", type=Path, required=True)
    p = sub.add_parser("root")
    p.add_argument("--binary", type=Path, required=True)
    p.add_argument("--length", type=int, required=True)
    p.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    if args.cmd == "pivot":
        res = aggregate_pivot_lp(args.binary, args.pivot, args.length, args.pivot_mult,
                                 include_p_containing=args.only in ("all", "p"),
                                 include_nonp=args.only in ("all", "nonp"))
    else:
        res = aggregate_root_lp(args.binary, args.length)
    args.out.write_text(json.dumps(res, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "status": "ok",
        "out": str(args.out),
        "lp_success": res["lp"]["success"],
        "lp_status": res["lp"]["status"],
        "lp_message": res["lp"]["message"],
        "unique_coeff_rows": res.get("unique_coeff_rows"),
        "num_vars": res["lp"].get("num_vars"),
        "elapsed_sec": res.get("elapsed_sec"),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
