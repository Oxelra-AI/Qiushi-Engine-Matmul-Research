#!/usr/bin/env python3
r"""analysisd: LP comparison of mixed-source cuts with complete Wang occupation.

This is a numerical/linear-programming diagnostic: minimize the mixed cut left
side over the linear relaxation of all canonical E11 Wang rows, x in [0,1],
sum x=19.  If the LP optimum is >= K, the cut is already implied by the Wang
linear relaxation (modulo exact rational recheck if theorem-bearing).  If the LP
optimum is < K, then complete Wang rows do not imply the cut at the linear level;
the cut may still be implied by integrality or by B/C geometry.  This does not by
itself prove existence/nonexistence of a rank-19 core.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from scipy import sparse

SCRIPTS = Path("scripts")
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import contraction_weight_excess_search as base  # noqa:E402
import mixed_source_cuts as cuts  # noqa:E402

OUTDIR = Path("data/mixed_source_cuts")
MATRIX_PATH = OUTDIR / "complete_wang_Aub.npz"
RHS_PATH = OUTDIR / "complete_wang_bub.npy"
META_PATH = OUTDIR / "complete_wang_lp_matrix_meta.json"


def ensure_matrix():
    if MATRIX_PATH.exists() and RHS_PATH.exists() and META_PATH.exists() and MATRIX_PATH.stat().st_size > 0 and RHS_PATH.stat().st_size > 0 and META_PATH.stat().st_size > 0:
        try:
            A = sparse.load_npz(MATRIX_PATH)
            b = np.load(RHS_PATH)
            with META_PATH.open() as f:
                meta = json.load(f)
            return A, b, meta
        except Exception:
            # A previous interrupted/write-path-created file can be zero or corrupt; rebuild below.
            pass
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    records, rec_meta = base.load_complete_records()
    rows = []
    cols = []
    data = []
    rhs = []
    row_id = 0
    by_L = {}
    point_nnz = 0
    for rec in records:
        L = int(rec["L"])
        cap = 19 - L
        if cap >= 19:
            continue
        bs = int(rec["point_bitset"])
        if bs == 0:
            continue
        by_L[str(L)] = by_L.get(str(L), 0) + 1
        tmp = bs
        while tmp:
            bit = tmp & -tmp
            p = bit.bit_length()  # point label p maps to variable p-1
            rows.append(row_id)
            cols.append(p - 1)
            data.append(1.0)
            point_nnz += 1
            tmp ^= bit
        rhs.append(float(cap))
        row_id += 1
    A = sparse.csr_matrix((data, (rows, cols)), shape=(row_id, 255), dtype=np.float64)
    b = np.array(rhs, dtype=np.float64)
    sparse.save_npz(MATRIX_PATH, A)
    np.save(RHS_PATH, b)
    meta = {
        "schema": "s0908_complete_wang_lp_matrix_v1",
        "rows": int(row_id), "cols": 255, "nnz": int(point_nnz),
        "by_L": by_L, "build_sec": round(time.time()-t0,3),
        "records_meta": rec_meta,
        "meaning": "A_ub x <= b_ub encodes all nontrivial canonical E11 Wang occupation rows for distinct 19-point support.",
    }
    with META_PATH.open("w") as f:
        json.dump(meta, f, indent=2, sort_keys=True)
    return A, b, meta


def coeff_vector(mu: int, lam: int, nu: int) -> np.ndarray:
    bs1, bs2, _pos, _counts = cuts.coeff_bitsets(int(mu), int(lam), int(nu))
    c = np.zeros(255, dtype=np.float64)
    for p in base.POINTS:
        if (bs2 >> (p - 1)) & 1:
            c[p - 1] = 2.0
        elif (bs1 >> (p - 1)) & 1:
            c[p - 1] = 1.0
    return c


def solve_cut_lp(mu: int, lam: int, nu: int, method: str = "highs") -> dict:
    t0 = time.time()
    A, b, meta = ensure_matrix()
    cp = cuts.cut_params(mu, lam, nu)
    c = coeff_vector(mu, lam, nu)
    res = linprog(
        c,
        A_ub=A,
        b_ub=b,
        A_eq=np.ones((1, 255), dtype=np.float64),
        b_eq=np.array([19.0]),
        bounds=[(0.0, 1.0)] * 255,
        method=method,
        options={"presolve": True},
    )
    out = {
        "triple": {k: v for k, v in cp.items() if k not in ("coeff1_bitset", "coeff2_bitset", "positive_bitset")},
        "lp": {
            "success": bool(res.success),
            "status": int(res.status),
            "message": str(res.message),
            "fun": None if res.fun is None else float(res.fun),
            "slack_to_K": None if res.fun is None else float(res.fun - cp["K"]),
            "implied_by_wang_lp_numeric": bool(res.success and res.fun >= cp["K"] - 1e-7),
            "violates_cut_fractionally": bool(res.success and res.fun < cp["K"] - 1e-7),
            "nonzero_x_head": [] if not res.success else [(int(i+1), float(v)) for i, v in enumerate(res.x) if v > 1e-7][:40],
            "fractional_count": None if not res.success else int(sum(1 for v in res.x if 1e-7 < v < 1-1e-7)),
            "sum_x": None if not res.success else float(np.sum(res.x)),
        },
        "matrix_meta": {k: meta[k] for k in ("rows", "cols", "nnz", "build_sec") if k in meta},
        "elapsed_sec": round(time.time() - t0, 3),
    }
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--triple", nargs=3, action="append")
    ap.add_argument("--preset", choices=["analysis", "topgap"], default="analysis")
    ap.add_argument("--out", default=str(OUTDIR / "wang_lp_cut_compare.json"))
    args = ap.parse_args()
    if args.triple:
        triples = [(int(a), int(b), int(c)) for a, b, c in args.triple]
    elif args.preset == "analysis":
        triples = [(18,5,34), (27,5,35), (27,6,131)]
    else:
        triples = [(1,48,48), (1,50,50), (1,52,52)]
    result = {"schema": "s0908_wang_lp_cut_compare_batch_v1", "triples": []}
    for tri in triples:
        rec = solve_cut_lp(*tri)
        result["triples"].append(rec)
        print(json.dumps({
            "triple": list(tri), "K": rec["triple"]["K"], "L_D": rec["triple"]["single_wang"]["L_D"],
            "success": rec["lp"]["success"], "fun": rec["lp"]["fun"], "slack_to_K": rec["lp"]["slack_to_K"],
            "frac_count": rec["lp"]["fractional_count"], "elapsed": rec["elapsed_sec"]
        }, sort_keys=True))
    outpath = Path(args.out)
    outpath.parent.mkdir(parents=True, exist_ok=True)
    with outpath.open("w") as f:
        json.dump(result, f, indent=2, sort_keys=True)


if __name__ == "__main__":
    main()
