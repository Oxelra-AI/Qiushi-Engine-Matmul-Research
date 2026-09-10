#!/usr/bin/env python3
"""MILP/LP support search for rank-2/rank-3 quotient occupation systems.

This is an execution instrument for the three-orbit lower-bound route.  It builds
one 255-variable binary/integer model for a quotient tensor Q_p=T333/span(p):

  * sum_p x_p = target (target=19 here);
  * all Wang occupation rows from the regenerated quotient binary;
  * contraction lower bounds w_q >= rank L(q);
  * optionally learned unconditional quotient-rank cuts
        N_out + sum_{source q}(w_q-r_q) >= rank(pi_W L(target)).

For rank-2 and rank-3 pivots at target 19, line caps force x_p in {0,1}; the
script uses binary variables.  A feasible support is only a necessary-condition
support and must still be sent to exact fixed-A Brent completion.  An infeasible
model is only theorem-facing after the input row semantics and solver certificate
are independently replayed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import struct
import sys
import time
from array import array
from collections import Counter
from pathlib import Path
from typing import Any, Iterable, Sequence

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix, vstack

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
from quotient_line_caps_and_controls import quotient_tensor  # type: ignore

PIVOTS = {"rank2": 17, "rank3": 273, "rank1": 1}
BIN_DIR = SESSION / "workspace/data/wang_native/quotient_binaries"
OUTDIR = SESSION / "workspace/data/quotient_support_ilp"
MAGIC = b"E11WANG1"
ALLMASK255 = (1 << 256) - 1  # bits are indexed by point p; bit 0 unused


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def gf2_rref(rows: Iterable[int], n: int = 9) -> tuple[int, ...]:
    basis = [int(x) for x in rows if int(x)]
    piv: dict[int, int] = {}
    for v0 in basis:
        v = int(v0)
        while v:
            p = v.bit_length() - 1
            if p in piv:
                v ^= piv[p]
            else:
                piv[p] = v
                break
    # reduced form
    for p in sorted(list(piv)):
        for q in sorted(list(piv), reverse=True):
            if q != p and ((piv[q] >> p) & 1):
                piv[q] ^= piv[p]
    return tuple(piv[p] for p in sorted(piv, reverse=True))


def gf2_rank(rows: Iterable[int], n: int = 9) -> int:
    return len(gf2_rref(rows, n))


def vec_to_mask(v: np.ndarray) -> int:
    out = 0
    arr = np.asarray(v, dtype=np.uint8).reshape(-1) & 1
    for i, bit in enumerate(arr):
        if int(bit):
            out |= 1 << i
    return int(out)


def matrix_rank_gf2(M: np.ndarray) -> int:
    rows = [vec_to_mask(row) for row in (np.asarray(M, dtype=np.uint8) & 1)]
    return gf2_rank(rows, M.shape[1])


def col_space_basis(M: np.ndarray) -> tuple[int, ...]:
    A = np.asarray(M, dtype=np.uint8) & 1
    cols = [vec_to_mask(A[:, j]) for j in range(A.shape[1])]
    return gf2_rref(cols, A.shape[0])


def row_space_basis(M: np.ndarray) -> tuple[int, ...]:
    A = np.asarray(M, dtype=np.uint8) & 1
    rows = [vec_to_mask(A[i, :]) for i in range(A.shape[0])]
    return gf2_rref(rows, A.shape[1])


def projection_rank_mod_space(target_space: Sequence[int], W: Sequence[int], n: int = 9) -> int:
    return gf2_rank(list(W) + list(target_space), n) - gf2_rank(W, n)


def point_functional_mask(q: int) -> int:
    mask = 0
    for p in range(1, 256):
        if ((int(q) & p).bit_count() & 1):
            mask |= 1 << p
    return mask


def read_e11wang_binary(path: Path) -> list[tuple[int, int, tuple[int, int, int, int]]]:
    rows: list[tuple[int, int, tuple[int, int, int, int]]] = []
    with path.open("rb") as f:
        magic = f.read(8)
        if magic != MAGIC:
            raise ValueError(f"bad magic {magic!r} in {path}")
        nrows = struct.unpack("<I", f.read(4))[0]
        for _ in range(nrows):
            cap, dim, _res = struct.unpack("<BBH", f.read(4))
            words = struct.unpack("<QQQQ", f.read(32))
            rows.append((int(cap), int(dim), tuple(int(w) for w in words)))
    return rows


def iter_points_from_words(words: Sequence[int]) -> Iterable[int]:
    for wi, w0 in enumerate(words):
        w = int(w0)
        base = wi << 6
        while w:
            lb = w & -w
            bit = lb.bit_length() - 1
            p = base + bit
            if 1 <= p <= 255:
                yield p
            w ^= lb


def words_to_bigmask(words: Sequence[int]) -> int:
    m = 0
    for p in iter_points_from_words(words):
        m |= 1 << p
    return m


def build_contractions(pivot: int) -> dict[int, dict[str, Any]]:
    T = quotient_tensor(pivot).astype(np.uint8) & 1
    out: dict[int, dict[str, Any]] = {}
    for q in range(1, 256):
        M = np.zeros((9, 9), dtype=np.uint8)
        for s in range(8):
            if (q >> s) & 1:
                M ^= T[s]
        out[q] = {
            "rank": int(matrix_rank_gf2(M)),
            "B_space": col_space_basis(M),
            "C_space": row_space_basis(M),
        }
    return out


def build_base_sparse(
    rows: list[tuple[int, int, tuple[int, int, int, int]]],
    contractions: dict[int, dict[str, Any]],
    target: int,
    include_contraction_lb: bool = True,
    max_wang_dim: int = 7,
) -> tuple[Any, np.ndarray, np.ndarray, dict[str, Any]]:
    """Build sparse LinearConstraint matrix for selected Wang rows and contraction lower bounds."""
    nvars = 255
    rr = array("i")
    cc = array("i")
    dd = array("d")
    lbs: list[float] = []
    ubs: list[float] = []
    row_meta: list[dict[str, Any]] = []
    dim_hist: Counter[int] = Counter()
    cap_hist: Counter[int] = Counter()
    nnz_wang = 0

    def add_coeff(row: int, col: int, val: float = 1.0) -> None:
        rr.append(row); cc.append(col); dd.append(val)

    # Cardinality equality.
    rid = 0
    for p in range(1, 256):
        add_coeff(rid, p - 1, 1.0)
    lbs.append(float(target)); ubs.append(float(target)); row_meta.append({"kind": "cardinality"}); rid += 1

    # Wang upper occupancy rows.
    skipped_dim = 0
    for cap, dim, words in rows:
        if int(dim) > int(max_wang_dim):
            skipped_dim += 1
            continue
        for p in iter_points_from_words(words):
            add_coeff(rid, p - 1, 1.0)
            nnz_wang += 1
        lbs.append(-np.inf); ubs.append(float(cap))
        row_meta.append({"kind": "wang", "cap": int(cap), "dim": int(dim)})
        dim_hist[int(dim)] += 1
        cap_hist[int(cap)] += 1
        rid += 1

    # Contraction lower bounds w_q >= rank L(q).  These are often implied by
    # hyperplane Wang rows, but are self-contained and cheap.
    contraction_lb_count = 0
    contraction_rank_hist: Counter[int] = Counter()
    if include_contraction_lb:
        for q, rec in contractions.items():
            rk = int(rec["rank"])
            contraction_rank_hist[rk] += 1
            if rk <= 0:
                continue
            for p in range(1, 256):
                if ((q & p).bit_count() & 1):
                    add_coeff(rid, p - 1, 1.0)
            lbs.append(float(rk)); ubs.append(np.inf)
            row_meta.append({"kind": "contraction_lb", "q": int(q), "rank": rk})
            rid += 1
            contraction_lb_count += 1

    A = coo_matrix((np.frombuffer(dd, dtype=np.float64),
                    (np.frombuffer(rr, dtype=np.int32), np.frombuffer(cc, dtype=np.int32))),
                   shape=(rid, nvars)).tocsr()
    info = {
        "wang_rows_in_input_binary": len(rows),
        "wang_rows_used": int(sum(dim_hist.values())),
        "wang_rows_skipped_by_dim": int(skipped_dim),
        "wang_dim_hist": {str(k): int(v) for k, v in sorted(dim_hist.items())},
        "wang_cap_hist": {str(k): int(v) for k, v in sorted(cap_hist.items())},
        "wang_nnz": int(nnz_wang),
        "contraction_lb_count": int(contraction_lb_count),
        "contraction_rank_hist": {str(k): int(v) for k, v in sorted(contraction_rank_hist.items())},
        "base_constraint_rows": int(rid),
        "base_nnz": int(A.nnz),
    }
    return A, np.array(lbs, dtype=float), np.array(ubs, dtype=float), info


def solve_model(A, lbs, ubs, *, binary: bool, time_limit: float, lp: bool = False) -> dict[str, Any]:
    nvars = A.shape[1]
    integrality = np.zeros(nvars, dtype=int) if lp else np.ones(nvars, dtype=int)
    ub = np.ones(nvars, dtype=float) if binary else np.full(nvars, np.inf)
    bounds = Bounds(np.zeros(nvars), ub)
    ts = time.time()
    res = milp(
        c=np.zeros(nvars),
        integrality=integrality,
        bounds=bounds,
        constraints=LinearConstraint(A, lbs, ubs),
        options={"time_limit": float(time_limit), "mip_rel_gap": 0.0, "presolve": True},
    )
    elapsed = time.time() - ts
    out: dict[str, Any] = {
        "status": int(res.status),
        "message": str(res.message),
        "success": bool(res.success),
        "solve_sec": round(elapsed, 3),
        "mode": "LP" if lp else "ILP",
    }
    if res.x is not None:
        x = np.asarray(res.x[:nvars], dtype=float)
        out["x_sum"] = round(float(x.sum()), 8)
        out["x_nonzero"] = int(np.count_nonzero(x > 1e-8))
        out["x_fractional"] = int(np.count_nonzero(np.abs(x - np.rint(x)) > 1e-7))
        out["x_min"] = round(float(x.min()), 8)
        out["x_max"] = round(float(x.max()), 8)
        if not lp and int(res.status) == 0:
            vals = np.rint(x).astype(int)
            support = [int(i + 1) for i, v in enumerate(vals) if int(v) != 0]
            out["support"] = support
            out["support_size"] = len(support)
            out["max_mult"] = int(vals.max()) if len(vals) else 0
        elif lp:
            top = sorted([(float(v), int(i + 1)) for i, v in enumerate(x) if v > 1e-8], reverse=True)[:40]
            out["x_top_head"] = [{"p": p, "value": round(v, 8)} for v, p in top]
    return out


def support_violations_wang(support: Sequence[int], rows: list[tuple[int, int, tuple[int, int, int, int]]], max_head: int = 20) -> dict[str, Any]:
    S = 0
    for p in support:
        S |= 1 << int(p)
    viol = []
    for idx, (cap, dim, words) in enumerate(rows):
        occ = (S & words_to_bigmask(words)).bit_count()
        if occ > cap:
            viol.append({"row": idx, "cap": cap, "dim": dim, "occ": occ, "excess": occ - cap})
    return {"violation_count": len(viol), "violations_head": viol[:max_head]}


def scan_unconditional_qcut_violations(
    support: Sequence[int],
    contractions: dict[int, dict[str, Any]],
    existing: set[tuple[str, int, int, int]],
    max_store: int = 200,
) -> dict[str, Any]:
    """Find pair-source unconditional quotient-rank cuts violated by a support."""
    support = [int(p) for p in support]
    weights = {q: sum(1 for p in support if ((q & p).bit_count() & 1)) for q in range(1, 256)}
    nonzero_q = [q for q, rec in contractions.items() if int(rec["rank"]) > 0]
    violations: list[dict[str, Any]] = []
    total_checked = 0
    req_hist: Counter[int] = Counter()
    side_hist: Counter[str] = Counter()
    t0 = time.time()

    for ii, q1 in enumerate(nonzero_q):
        r1 = int(contractions[q1]["rank"])
        w1 = int(weights[q1])
        m1 = point_functional_mask(q1)
        for q2 in nonzero_q[ii + 1:]:
            r2 = int(contractions[q2]["rank"])
            excess = (w1 - r1) + (int(weights[q2]) - r2)
            # If excess is already large, cuts with req<=excess cannot fail unless N_out negative.
            m2 = point_functional_mask(q2)
            source_union = m1 | m2
            for side in ("B", "C"):
                side_key = "B_space" if side == "B" else "C_space"
                W = gf2_rref(list(contractions[q1][side_key]) + list(contractions[q2][side_key]), 9)
                if len(W) >= 9:
                    continue
                for tgt in nonzero_q:
                    req = projection_rank_mod_space(contractions[tgt][side_key], W, 9)
                    if req <= 0:
                        continue
                    total_checked += 1
                    if req <= excess:
                        continue
                    N_out = 0
                    for p in support:
                        if ((tgt & p).bit_count() & 1) and not ((q1 & p).bit_count() & 1) and not ((q2 & p).bit_count() & 1):
                            N_out += 1
                    lhs = N_out + excess
                    if lhs < req:
                        key = (side, min(q1, q2), max(q1, q2), tgt)
                        req_hist[int(req)] += 1
                        side_hist[side] += 1
                        violations.append({
                            "side": side,
                            "sources": [min(q1, q2), max(q1, q2)],
                            "target": int(tgt),
                            "source_ranks": [r1, r2],
                            "source_weights": [w1, int(weights[q2])],
                            "excess_sum": int(excess),
                            "W_dim": len(W),
                            "requirement": int(req),
                            "N_out": int(N_out),
                            "unconditional_lhs": int(lhs),
                            "deficit": int(req - lhs),
                            "outside_point_count": int((point_functional_mask(tgt) & ~source_union & ALLMASK255).bit_count()),
                            "is_new": key not in existing,
                        })
    violations.sort(key=lambda z: (-int(z["deficit"]), -int(z["requirement"]), z["side"], z["sources"], z["target"]))
    return {
        "elapsed_sec": round(time.time() - t0, 3),
        "total_checked": int(total_checked),
        "violation_count": len(violations),
        "new_violation_count": sum(1 for v in violations if v["is_new"]),
        "violations_by_requirement": {str(k): int(v) for k, v in sorted(req_hist.items())},
        "violations_by_side": dict(side_hist),
        "violations_head": violations[:max_store],
    }


def qcut_to_sparse_row(cut: dict[str, Any], contractions: dict[int, dict[str, Any]]) -> tuple[list[int], list[float], float]:
    q1, q2 = int(cut["sources"][0]), int(cut["sources"][1])
    tgt = int(cut["target"])
    req = int(cut["requirement"])
    r1 = int(contractions[q1]["rank"])
    r2 = int(contractions[q2]["rank"])
    cols: list[int] = []
    vals: list[float] = []
    for p in range(1, 256):
        coeff = 0
        if ((tgt & p).bit_count() & 1) and not ((q1 & p).bit_count() & 1) and not ((q2 & p).bit_count() & 1):
            coeff += 1
        if ((q1 & p).bit_count() & 1):
            coeff += 1
        if ((q2 & p).bit_count() & 1):
            coeff += 1
        if coeff:
            cols.append(p - 1); vals.append(float(coeff))
    rhs = float(req + r1 + r2)
    return cols, vals, rhs


def append_qcuts(A, lbs, ubs, cuts: Sequence[dict[str, Any]], contractions: dict[int, dict[str, Any]]):
    if not cuts:
        return A, lbs, ubs
    rr: list[int] = []
    cc: list[int] = []
    dd: list[float] = []
    new_lbs: list[float] = []
    new_ubs: list[float] = []
    for i, cut in enumerate(cuts):
        cols, vals, rhs = qcut_to_sparse_row(cut, contractions)
        for c, v in zip(cols, vals):
            rr.append(i); cc.append(c); dd.append(v)
        new_lbs.append(rhs); new_ubs.append(np.inf)
    B = coo_matrix((np.array(dd, dtype=float), (np.array(rr, dtype=np.int32), np.array(cc, dtype=np.int32))),
                   shape=(len(cuts), A.shape[1])).tocsr()
    return vstack([A, B], format="csr"), np.concatenate([lbs, np.array(new_lbs)]), np.concatenate([ubs, np.array(new_ubs)])


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot-name", choices=sorted(PIVOTS), required=True)
    ap.add_argument("--target", type=int, default=19)
    ap.add_argument("--binary", action="store_true", default=True)
    ap.add_argument("--lp-time", type=float, default=60.0)
    ap.add_argument("--ilp-time", type=float, default=300.0)
    ap.add_argument("--max-rounds", type=int, default=1)
    ap.add_argument("--add-qcuts", type=int, default=0, help="after a feasible support, add this many violated unconditional cuts per round")
    ap.add_argument("--skip-lp", action="store_true")
    ap.add_argument("--max-wang-dim", type=int, default=7, help="use quotient Wang rows of dimension at most this value")
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()

    pivot = PIVOTS[args.pivot_name]
    bin_path = BIN_DIR / f"{args.pivot_name}_all_n{args.target}.bin"
    if args.out is None:
        args.out = OUTDIR / f"{args.pivot_name}_n{args.target}_allwang_ilp_qcuts{args.add_qcuts}_rounds{args.max_rounds}.json"
    args.out.parent.mkdir(parents=True, exist_ok=True)

    t0 = time.time()
    rows = read_e11wang_binary(bin_path)
    contractions = build_contractions(pivot)
    A, lbs, ubs, base_info = build_base_sparse(rows, contractions, args.target, include_contraction_lb=True, max_wang_dim=int(args.max_wang_dim))
    built_sec = time.time() - t0
    print(f"{args.pivot_name}: rows={len(rows)} base_constraints={A.shape[0]} nnz={A.nnz} build={built_sec:.2f}s")

    lp_result = None
    if not args.skip_lp:
        print("Solving LP relaxation...")
        lp_result = solve_model(A, lbs, ubs, binary=True, time_limit=args.lp_time, lp=True)
        print(json.dumps({k: lp_result[k] for k in ['status','message','solve_sec','x_sum','x_nonzero','x_fractional','x_max'] if k in lp_result}, sort_keys=True))

    rounds = []
    learned_keys: set[tuple[str, int, int, int]] = set()
    current_A, current_lbs, current_ubs = A, lbs, ubs
    final_status = None
    final_support = None
    learned_qcuts: list[dict[str, Any]] = []

    for rnd in range(int(args.max_rounds)):
        print(f"Solving ILP round {rnd}: constraints={current_A.shape[0]} qcuts={len(learned_qcuts)}")
        res = solve_model(current_A, current_lbs, current_ubs, binary=True, time_limit=args.ilp_time, lp=False)
        rec: dict[str, Any] = {"round": rnd, "active_constraints": int(current_A.shape[0]), "active_qcuts": len(learned_qcuts), "ilp": res}
        print(json.dumps({k: res[k] for k in ['status','message','success','solve_sec','support_size'] if k in res}, sort_keys=True))
        if int(res["status"]) != 0 or "support" not in res:
            final_status = "INFEASIBLE" if int(res["status"]) == 2 else ("TIME_OR_ITERATION_LIMIT" if int(res["status"]) == 1 else "NO_FEASIBLE_SUPPORT_RETURNED")
            rounds.append(rec)
            break
        support = [int(p) for p in res["support"]]
        final_support = support
        rec["support"] = support
        rec["wang_recheck"] = support_violations_wang(support, rows, max_head=20)
        print(f"  support={support}")
        print(f"  Wang recheck violations={rec['wang_recheck']['violation_count']}")
        if args.add_qcuts <= 0:
            final_status = "FEASIBLE_WANG_SUPPORT"
            rounds.append(rec)
            break
        qscan = scan_unconditional_qcut_violations(support, contractions, learned_keys, max_store=max(args.add_qcuts, 50))
        rec["unconditional_qcut_scan"] = {k: v for k, v in qscan.items() if k != "violations_head"}
        rec["unconditional_qcut_violations_head"] = qscan["violations_head"][:min(50, len(qscan["violations_head"]))]
        print(f"  qcut violations={qscan['violation_count']} new={qscan['new_violation_count']} scan={qscan['elapsed_sec']}s")
        if qscan["violation_count"] == 0:
            final_status = "FEASIBLE_WANG_AND_UNCONDITIONAL_QCUT_SUPPORT"
            rounds.append(rec)
            break
        newcuts = []
        for v in qscan["violations_head"]:
            key = (str(v["side"]), int(v["sources"][0]), int(v["sources"][1]), int(v["target"]))
            if key not in learned_keys:
                learned_keys.add(key)
                learned_qcuts.append(v)
                newcuts.append(v)
                if len(newcuts) >= int(args.add_qcuts):
                    break
        rec["learned_qcuts_added"] = len(newcuts)
        rec["learned_qcuts"] = newcuts
        rounds.append(rec)
        if not newcuts:
            final_status = "STALLED_NO_NEW_QCUTS"
            break
        current_A, current_lbs, current_ubs = append_qcuts(current_A, current_lbs, current_ubs, newcuts, contractions)
        final_status = "CONTINUED_AFTER_QCUTS"

    result = {
        "schema": "quotient_support_ilp_v1",
        "pivot_name": args.pivot_name,
        "pivot": pivot,
        "target": int(args.target),
        "binary_variables": True,
        "max_wang_dim": int(args.max_wang_dim),
        "mathematical_meaning": "MILP over quotient A-supports satisfying Wang occupation rows, contraction lower bounds, and learned unconditional quotient-rank inequalities. Feasible support is necessary-condition evidence only; infeasible result requires independent solver certificate/replay before theorem use.",
        "input_binary": str(bin_path),
        "input_binary_sha256": sha256(bin_path),
        "base_info": base_info,
        "build_sec": round(built_sec, 3),
        "lp_relaxation": lp_result,
        "rounds": rounds,
        "final_status": final_status,
        "final_support": final_support,
        "learned_qcut_count": len(learned_qcuts),
        "learned_qcuts_head": learned_qcuts[:200],
        "total_elapsed_sec": round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Saved {args.out}")
    print(json.dumps({"final_status": final_status, "rounds": len(rounds), "learned_qcuts": len(learned_qcuts), "out": str(args.out)}, sort_keys=True))


if __name__ == "__main__":
    main()
