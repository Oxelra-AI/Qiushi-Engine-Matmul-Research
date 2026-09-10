#!/usr/bin/env python3
"""Surviving coset ansatz analysis for possible rank-20 T333 decomposition over F2.

This script works in the normalized column-type coset
    p + e0 \otimes F_2^3,
with lower block rank two.  It verifies the affine-geometry consequences of
earlier analysis, records the exact Wang lower-bound values for all planes arising
from the coset, and searches the residual rank-one A-support choices after the
coset structure and flattening equality force
    3 rank-3 A-factors + 1 rank-2 A-factor + 16 rank-1 A-factors.

The search here is only on the A-side Wang occupation constraints plus the
coset-derived saturated subspaces.  Any A-support found must still be tested by
full fixed-A B/C completion.
"""
from __future__ import annotations

import argparse
import json
import os
import pickle
import struct
import sys
import time
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

try:
    from ortools.sat.python import cp_model  # type: ignore
except Exception:  # pragma: no cover
    cp_model = None

NBITS = 9
MAGIC = b"WANG512\x01"
DEFAULT_LUT = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
DEFAULT_BINARY = Path("data/wang_native/full_tensor/full_wang512_cap19_len20_all_dim9_allbinding.bin")
DEFAULT_OUT = Path("data/coset_ansatz/surviving_coset_ansatz.json")


def gf2_rank_rows(rows: Sequence[int], ncols: int) -> int:
    basis: List[int] = []
    for x0 in rows:
        x = int(x0)
        for b in basis:
            p = b.bit_length() - 1
            if (x >> p) & 1:
                x ^= b
        if x == 0:
            continue
        p = x.bit_length() - 1
        for i, b in enumerate(basis):
            if (b >> p) & 1:
                basis[i] = b ^ x
        basis.append(x)
        basis.sort(key=lambda z: z.bit_length(), reverse=True)
    return len(basis)


def mat_rank(x: int) -> int:
    rows = []
    for i in range(3):
        row = 0
        for j in range(3):
            if (x >> (3 * i + j)) & 1:
                row |= 1 << j
        rows.append(row)
    return gf2_rank_rows(rows, 3)


def rref_basis(rows: Iterable[int], nbits: int = NBITS) -> Tuple[int, ...]:
    basis: List[int] = []
    for x0 in rows:
        x = int(x0)
        if x == 0:
            continue
        for rb in basis:
            p = rb.bit_length() - 1
            if (x >> p) & 1:
                x ^= rb
        if x == 0:
            continue
        p = x.bit_length() - 1
        for i, rb in enumerate(basis):
            if (rb >> p) & 1:
                basis[i] = rb ^ x
        basis.append(x)
        basis.sort(key=lambda z: z.bit_length(), reverse=True)
    return tuple(basis)


def pack_basis(basis_rref: Sequence[int]) -> int:
    x = 0
    for i, b in enumerate(basis_rref):
        x |= int(b) << (NBITS * i)
    return (x << 4) | len(basis_rref)


def subspace_key(gens: Iterable[int]) -> int:
    return pack_basis(rref_basis(gens))


def span_elements(gens: Sequence[int], include_zero: bool = False) -> List[int]:
    rb = rref_basis(gens)
    out = [0] if include_zero else []
    d = len(rb)
    for m in range(1, 1 << d):
        x = 0
        for i, b in enumerate(rb):
            if (m >> i) & 1:
                x ^= b
        out.append(x)
    return sorted(out)


def in_span(v: int, gens: Sequence[int]) -> bool:
    rb = rref_basis(gens)
    x = int(v)
    for b in rb:
        p = b.bit_length() - 1
        if (x >> p) & 1:
            x ^= b
    return x == 0


def outer_mask(left: int, right: int) -> int:
    x = 0
    for i in range(3):
        if (left >> i) & 1:
            for j in range(3):
                if (right >> j) & 1:
                    x |= 1 << (3 * i + j)
    return x


def rank_one_points() -> List[int]:
    pts = sorted({outer_mask(u, v) for u in range(1, 8) for v in range(1, 8)})
    assert len(pts) == 49
    return pts


def rank_one_uv_map() -> Dict[int, Tuple[int, int]]:
    # Over F2 the representation is unique for nonzero rank-one matrices.
    d: Dict[int, Tuple[int, int]] = {}
    for u in range(1, 8):
        for v in range(1, 8):
            d[outer_mask(u, v)] = (u, v)
    assert len(d) == 49
    return d


def load_lut(path: Path) -> Dict[int, int]:
    obj = pickle.load(open(path, "rb"))
    lut = obj["lut"] if isinstance(obj, dict) and "lut" in obj else obj
    return {int(k): int(v) for k, v in lut.items()}


def wang_lb(lut: Dict[int, int], gens: Iterable[int]) -> int:
    k = subspace_key(gens)
    if k not in lut:
        raise KeyError(f"subspace key not in Wang LUT: key={k}, gens={list(gens)}")
    return int(lut[k])


def rowmask_from_words(words: Tuple[int, ...]) -> int:
    z = 0
    for i, w in enumerate(words):
        z |= int(w) << (64 * i)
    return z


def iter_wang_rows(path: Path):
    with open(path, "rb") as f:
        magic = f.read(8)
        if magic != MAGIC:
            raise ValueError(f"bad WANG512 magic {magic!r} in {path}")
        nrows = struct.unpack("<I", f.read(4))[0]
        for idx in range(nrows):
            cap, dim, _ = struct.unpack("<BBH", f.read(4))
            words = struct.unpack("<8Q", f.read(64))
            yield idx, int(cap), int(dim), rowmask_from_words(words)


def canonical_coset_points() -> Tuple[int, List[int], List[int], List[int]]:
    # Lower block rows e2^T and e3^T: bits (row1,col1)=4 and (row2,col2)=8.
    p = (1 << 4) | (1 << 8)  # 272, first row zero.
    row_space = [r for r in range(8)]
    coset = [p | r for r in row_space]
    rank2 = [p | r for r in row_space if ((r & 1) == 0)]
    rank3 = [p | r for r in row_space if ((r & 1) == 1)]
    assert all(mat_rank(x) == 2 for x in rank2)
    assert all(mat_rank(x) == 3 for x in rank3)
    return p, coset, rank2, rank3


def affine_planes_in_ag3() -> List[Tuple[int, ...]]:
    planes = set()
    pts = list(range(8))
    for base in pts:
        for u, v in combinations([x for x in pts if x], 2):
            if u == v:
                continue
            plane = tuple(sorted({base, base ^ u, base ^ v, base ^ u ^ v}))
            if len(plane) == 4:
                planes.add(plane)
    return sorted(planes)


def affine_plane_count(subset: Sequence[int]) -> int:
    S = set(subset)
    return sum(1 for P in affine_planes_in_ag3() if set(P).issubset(S))


def h_to_firstrows(H: Sequence[int], p: int) -> List[int]:
    return sorted([int(h) ^ int(p) for h in H])


def analyze_H(lut: Dict[int, int], H: Sequence[int], p: int) -> Dict:
    H = list(map(int, H))
    H_mask = sum(1 << h for h in H)
    ranks = [mat_rank(h) for h in H]
    firstrows = h_to_firstrows(H, p)
    S_basis = [p, 1, 2, 4]
    S_lb = wang_lb(lut, S_basis)

    pair_recs = []
    for a, b in combinations(H, 2):
        lb = wang_lb(lut, [a, b])
        elts = span_elements([a, b])
        pair_recs.append({
            "pair": [a, b],
            "pair_firstrows": [a ^ p, b ^ p],
            "lb": lb,
            "rank_pattern": sorted(mat_rank(x) for x in elts),
            "rank_one_sum": a ^ b,
        })

    triple_recs = []
    triple_rank_one_union = set()
    for tri in combinations(H, 3):
        lb = wang_lb(lut, tri)
        elts = span_elements(list(tri))
        r1 = sorted(x for x in elts if mat_rank(x) == 1)
        high = sorted(x for x in elts if mat_rank(x) >= 2)
        triple_rank_one_union.update(r1)
        triple_recs.append({
            "triple": list(tri),
            "triple_firstrows": [x ^ p for x in tri],
            "lb": lb,
            "rank_hist": dict(Counter(mat_rank(x) for x in elts)),
            "rank_one_elements": r1,
            "high_rank_elements": high,
            "cap_len20": 20 - lb,
        })

    r1pts = rank_one_points()
    uv = rank_one_uv_map()
    point_reasons: Dict[int, List[str]] = {x: [] for x in r1pts}
    for x in r1pts:
        # General one-point necessary inequalities for subspaces generated by x and k high-rank terms.
        for k in range(1, 5):
            for subset in combinations(H, k):
                gens = list(subset) + [x]
                lb = wang_lb(lut, gens)
                occ = k + 1
                cap = 20 - lb
                if occ > cap:
                    point_reasons[x].append(f"H{k}+x occ {occ}>cap {cap} (LB {lb})")
                    break
            if point_reasons[x]:
                break
    allowed = sorted(x for x, rs in point_reasons.items() if not rs)
    forbidden = sorted(x for x, rs in point_reasons.items() if rs)
    firstrow_rankone = sorted(outer_mask(1, v) for v in range(1, 8))
    allowed_firstrow = [x for x in allowed if x in firstrow_rankone]
    forbidden_firstrow = [x for x in forbidden if x in firstrow_rankone]

    # Plane facts inside AG(3,2).
    plane_count_by_size = {str(k): Counter() for k in range(0, 9)}
    for k in range(0, 9):
        for sub in combinations(range(8), k):
            plane_count_by_size[str(k)][affine_plane_count(sub)] += 1

    return {
        "H": H,
        "H_mask": H_mask,
        "firstrows": firstrows,
        "rank_hist": dict(Counter(ranks)),
        "affine_plane_count_in_H": affine_plane_count(firstrows),
        "S_basis": S_basis,
        "S_lb": S_lb,
        "pair_lb_hist": dict(Counter(r["lb"] for r in pair_recs)),
        "pair_records": pair_recs,
        "triple_lb_hist": dict(Counter(r["lb"] for r in triple_recs)),
        "triple_records": triple_recs,
        "triple_rank_one_union": sorted(triple_rank_one_union),
        "triple_rank_one_union_uv": {str(x): list(uv[x]) for x in sorted(triple_rank_one_union) if x in uv},
        "allowed_rank_one_count": len(allowed),
        "allowed_rank_one": allowed,
        "allowed_rank_one_uv": {str(x): list(uv[x]) for x in allowed},
        "forbidden_rank_one_count": len(forbidden),
        "allowed_firstrow_rank_one": allowed_firstrow,
        "forbidden_firstrow_rank_one": forbidden_firstrow,
        "point_rejection_reasons_head": {str(x): rs[:3] for x, rs in point_reasons.items() if rs},
        "ag3_plane_count_by_subset_size": {k: dict(v) for k, v in plane_count_by_size.items()},
    }


def add_basic_rankone_caps(model, vars_by_point: Dict[int, object], allowed: Sequence[int]):
    uv = rank_one_uv_map()
    for u in range(1, 8):
        xs = [vars_by_point[x] for x in allowed if uv[x][0] == u]
        if xs:
            model.Add(sum(xs) <= 5)
    for v in range(1, 8):
        xs = [vars_by_point[x] for x in allowed if uv[x][1] == v]
        if xs:
            model.Add(sum(xs) <= 5)


def scan_support(binary: Path, H_mask: int, support: Sequence[int], max_report: int = 200) -> Dict:
    support_mask = sum(1 << int(x) for x in support)
    A_mask = H_mask | support_mask
    viol = []
    count = 0
    excess_total = 0
    max_excess = 0
    rows = 0
    dim_hist = Counter()
    t0 = time.time()
    for idx, cap, dim, rowmask in iter_wang_rows(binary):
        rows += 1
        occ = (rowmask & A_mask).bit_count()
        if occ > cap:
            ex = occ - cap
            count += 1
            excess_total += ex
            max_excess = max(max_excess, ex)
            dim_hist[dim] += 1
            if len(viol) < max_report:
                viol.append({"row_index": idx, "cap": cap, "dim": dim, "occ": occ, "excess": ex, "row_mask": rowmask})
    return {
        "rows_checked": rows,
        "passed": count == 0,
        "violation_count": count,
        "excess_total": excess_total,
        "max_excess": max_excess,
        "violation_dim_hist": dict(sorted(dim_hist.items())),
        "violations": viol,
        "elapsed_sec": time.time() - t0,
    }


def solve_rankone_cegar(lut: Dict[int, int], binary: Path, Hrec: Dict, outdir: Path, max_rounds: int, solver_sec: float, add_per_round: int) -> Dict:
    if cp_model is None:
        raise RuntimeError("ortools CP-SAT is not available")
    H = [int(x) for x in Hrec["H"]]
    H_mask = int(Hrec["H_mask"])
    allowed = [int(x) for x in Hrec["allowed_rank_one"]]
    outdir.mkdir(parents=True, exist_ok=True)

    model = cp_model.CpModel()
    var = {x: model.NewBoolVar(f"r1_{x}") for x in allowed}
    model.Add(sum(var.values()) == 16)
    add_basic_rankone_caps(model, var, allowed)
    constraints_added = 0
    rounds = []

    for rd in range(max_rounds):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(solver_sec)
        solver.parameters.num_search_workers = 8
        t0 = time.time()
        status = solver.Solve(model)
        solve_elapsed = time.time() - t0
        status_name = solver.StatusName(status)
        rec = {"round": rd, "solve_status": status_name, "solve_elapsed_sec": solve_elapsed, "constraints_added_total": constraints_added}
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            rec["status_meaning"] = status_name
            rounds.append(rec)
            final = "CP_SAT_" + status_name
            break
        support = [x for x in allowed if solver.Value(var[x])]
        rec["support"] = support
        rec["support_uv"] = {str(x): list(rank_one_uv_map()[x]) for x in support}
        rec["left_hist"] = dict(Counter(rank_one_uv_map()[x][0] for x in support))
        rec["right_hist"] = dict(Counter(rank_one_uv_map()[x][1] for x in support))
        scan = scan_support(binary, H_mask, support, max_report=add_per_round)
        rec["scan_summary"] = {k: v for k, v in scan.items() if k != "violations"}
        if scan["passed"]:
            rounds.append(rec)
            final = "WANG_FEASIBLE_A_SUPPORT"
            (outdir / f"round_{rd:03d}_support.json").write_text(json.dumps({"H": H, "rank_one_support": support, "A_multiset": H + support, "scan": rec["scan_summary"]}, indent=2, sort_keys=True) + "\n")
            break
        # Add violated rows as cuts.
        added_now = 0
        for vr in scan["violations"]:
            rowmask = int(vr["row_mask"])
            rhs = int(vr["cap"]) - (rowmask & H_mask).bit_count()
            pts = [x for x in allowed if (rowmask >> x) & 1]
            if rhs < 0:
                model.Add(0 <= -1)
                added_now += 1
            elif pts and rhs < len(pts):
                model.Add(sum(var[x] for x in pts) <= rhs)
                added_now += 1
        constraints_added += added_now
        rec["cuts_added_now"] = added_now
        rounds.append(rec)
    else:
        final = "MAX_ROUNDS"

    result = {
        "schema": "surviving_coset_rankone_cegar_v1",
        "H": H,
        "H_firstrows": Hrec["firstrows"],
        "allowed_rank_one_count": len(allowed),
        "target_rank_one_terms": 16,
        "final_status": final,
        "rounds": rounds,
        "binary": str(binary),
        "parameters": {"max_rounds": max_rounds, "solver_sec": solver_sec, "add_per_round": add_per_round},
    }
    (outdir / "cegar_result.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lut", type=Path, default=DEFAULT_LUT)
    ap.add_argument("--binary", type=Path, default=DEFAULT_BINARY)
    ap.add_argument("--out", type=Path, default=DEFAULT_OUT)
    ap.add_argument("--mode", choices=["analyze", "cegar"], default="analyze")
    ap.add_argument("--h-index", type=int, default=0, help="which normalized H configuration to use in cegar mode")
    ap.add_argument("--max-rounds", type=int, default=20)
    ap.add_argument("--solver-sec", type=float, default=10.0)
    ap.add_argument("--add-per-round", type=int, default=200)
    args = ap.parse_args()

    t0 = time.time()
    lut = load_lut(args.lut)
    p, coset, rank2, rank3 = canonical_coset_points()
    Hs = [list(c2) + list(c3) for c2 in combinations(rank2, 1) for c3 in combinations(rank3, 3)]
    # Sort deterministically by first-row pattern.
    Hs = sorted([sorted(H) for H in Hs], key=lambda H: h_to_firstrows(H, p))
    analyses = [analyze_H(lut, H, p) for H in Hs]

    summary = {
        "schema": "surviving_coset_ansatz_v1",
        "normalized_p_base": p,
        "normalized_S_basis": [p, 1, 2, 4],
        "S_lb": wang_lb(lut, [p, 1, 2, 4]),
        "rank2_coset_points": rank2,
        "rank3_coset_points": rank3,
        "H_configuration_count": len(Hs),
        "H_rank_hist_distribution": dict(Counter(json.dumps(a["rank_hist"], sort_keys=True) for a in analyses)),
        "H_affine_plane_count_distribution": dict(Counter(a["affine_plane_count_in_H"] for a in analyses)),
        "pair_lb_hist_distribution": dict(Counter(json.dumps(a["pair_lb_hist"], sort_keys=True) for a in analyses)),
        "triple_lb_hist_distribution": dict(Counter(json.dumps(a["triple_lb_hist"], sort_keys=True) for a in analyses)),
        "allowed_rank_one_count_distribution": dict(Counter(a["allowed_rank_one_count"] for a in analyses)),
        "allowed_firstrow_distribution": {json.dumps(list(k)): v for k, v in Counter(tuple(a["allowed_firstrow_rank_one"]) for a in analyses).items()},
        "ag3_plane_count_by_subset_size": analyses[0]["ag3_plane_count_by_subset_size"],
        "analyses": analyses,
        "elapsed_sec": time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(args.out),
        "mode": args.mode,
        "H_configuration_count": len(Hs),
        "S_lb": summary["S_lb"],
        "pair_lb_hist_distribution": summary["pair_lb_hist_distribution"],
        "triple_lb_hist_distribution": summary["triple_lb_hist_distribution"],
        "allowed_rank_one_count_distribution": summary["allowed_rank_one_count_distribution"],
        "elapsed_sec": summary["elapsed_sec"],
    }, indent=2, sort_keys=True))

    if args.mode == "cegar":
        if not (0 <= args.h_index < len(analyses)):
            raise ValueError("bad h-index")
        outdir = args.out.parent / f"cegar_H{args.h_index:02d}"
        res = solve_rankone_cegar(lut, args.binary, analyses[args.h_index], outdir, args.max_rounds, args.solver_sec, args.add_per_round)
        print(json.dumps({
            "cegar_out": str(outdir / "cegar_result.json"),
            "final_status": res["final_status"],
            "rounds": len(res["rounds"]),
        }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
