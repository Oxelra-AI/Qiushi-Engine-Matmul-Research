#!/usr/bin/env python3
r"""
analysis LP relaxation for the trace-saturation gate.

This is the cheap support-level computation requested before building a larger
trace pipeline.  It solves the full Wang occupation linear relaxation with all
417,199 inequalities and the contraction-rank lower bounds, then optimizes

    sum_s nu(a_s),   nu(a)=#{invertible q : <q,a>=1}.

If even the LP maximum were <= 720 in a rank-19 quotient core, then saturated
invertible contractions would be forced by the counting identity.  If the LP
maximum is >720, the counting cut cannot force saturation.  A separate LP with
|I_q|>=10 for every invertible q checks whether avoiding all saturated q is
compatible with these linear constraints at the fractional level.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog
from scipy.sparse import csr_matrix, vstack

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/trace_saturation_gate"
SCRIPTS_A02 = ROOT / "workspace/scripts"
SCRIPTS_A01 = Path("scripts")
for P in (SCRIPTS_A02, SCRIPTS_A01):
    if str(P) not in sys.path:
        sys.path.insert(0, str(P))

from trace_saturation_gate import (  # noqa: E402
    CORES,
    bit_dot,
    build_or_load_core_cache,
    core_raw_summary,
    load_lut,
    mask_to_points,
    point_caps_from_cache,
    support_stats,
)


def wang_sparse(cache: dict, n: int = 255) -> tuple[csr_matrix, np.ndarray]:
    indptr = [0]
    indices = []
    data = []
    b = []
    for m, cap in zip(cache["masks"], cache["caps"]):
        pts = mask_to_points(int(m))
        indices.extend([p - 1 for p in pts])
        data.extend([1.0] * len(pts))
        indptr.append(len(indices))
        b.append(float(cap))
    A = csr_matrix((np.asarray(data), np.asarray(indices), np.asarray(indptr)), shape=(len(b), n))
    return A, np.asarray(b, dtype=float)


def hit_sparse(rows: list[tuple[int, int]], n: int = 255) -> tuple[csr_matrix, np.ndarray]:
    indptr = [0]
    indices = []
    data = []
    b = []
    for q, lb in rows:
        pts = [p for p in range(1, n + 1) if bit_dot(p, q)]
        indices.extend([p - 1 for p in pts])
        data.extend([-1.0] * len(pts))
        indptr.append(len(indices))
        b.append(-float(lb))
    A = csr_matrix((np.asarray(data), np.asarray(indices), np.asarray(indptr)), shape=(len(b), n))
    return A, np.asarray(b, dtype=float)


def solve_lp(cache: dict, c_ranks: dict[int, int], inv_qs: list[int], nu: dict[int, int], mode: str) -> dict:
    n = 255
    pcaps = point_caps_from_cache(cache, int(cache["rank_s"]))
    bounds = [(0.0, float(pcaps[p])) for p in range(1, n + 1)]
    Aw, bw = wang_sparse(cache, n)
    rows = []
    if mode in ("max_rank", "min_rank", "no_saturation"):
        for q, rk in sorted(c_ranks.items()):
            lb = 10 if (mode == "no_saturation" and q in inv_qs) else int(rk)
            if lb > 0:
                rows.append((int(q), lb))
    Ah, bh = hit_sparse(rows, n) if rows else (csr_matrix((0, n)), np.zeros(0))
    Aub = vstack([Aw, Ah], format="csr") if rows else Aw
    bub = np.concatenate([bw, bh]) if rows else bw
    Aeq = np.ones((1, n), dtype=float)
    beq = np.array([float(cache["rank_s"])])
    obj = np.zeros(n)
    if mode.startswith("max"):
        obj = -np.asarray([nu[p] for p in range(1, n + 1)], dtype=float)
    elif mode.startswith("min"):
        obj = np.asarray([nu[p] for p in range(1, n + 1)], dtype=float)
    t0 = time.time()
    res = linprog(obj, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=bounds, method="highs")
    elapsed = time.time() - t0
    out = {
        "mode": mode,
        "success": bool(res.success),
        "status": int(res.status),
        "message": str(res.message),
        "fun": None if res.fun is None else float(res.fun),
        "elapsed_sec": round(elapsed, 3),
        "wang_constraint_count": int(Aw.shape[0]),
        "hit_lower_constraint_count": int(Ah.shape[0]),
    }
    if res.x is not None and res.success:
        x = np.asarray(res.x)
        sum_nu = float(np.dot(np.asarray([nu[p] for p in range(1, n + 1)], dtype=float), x))
        inv_hits = [float(sum(x[p - 1] for p in range(1, n + 1) if bit_dot(p, q))) for q in inv_qs]
        out.update({
            "sum_nu": sum_nu,
            "sum_nu_rationalish": round(sum_nu, 10),
            "saturation_count_fractional_exact9_tol1e-7": int(sum(1 for h in inv_hits if abs(h - 9.0) < 1e-7)),
            "min_rank9_hit": min(inv_hits),
            "max_rank9_hit": max(inv_hits),
            "rank9_hit_values_head": sorted(set(round(h, 10) for h in inv_hits))[:30],
            "positive_variables": int(sum(1 for z in x if z > 1e-8)),
            "largest_variables_head": [[int(i + 1), float(x[i]), int(nu[i + 1])] for i in np.argsort(-x)[:20] if x[i] > 1e-8],
            "linear_saturation_lower_bound_from_sum_nu": 72.0 - (sum_nu - 648.0),
        })
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--cores", nargs="*", default=list(CORES), choices=list(CORES))
    ap.add_argument("--cache-dir", type=Path, default=OUTDIR / "cache")
    ap.add_argument("--out", type=Path, default=OUTDIR / "trace_gate_lp.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    lut, meta = load_lut(args.lut)
    result = {
        "schema": "trace_gate_lp_v1",
        "field": "F2",
        "rank_s": int(args.rank),
        "purpose": "LP feasibility/optimization gate for whether saturation is forced by Wang occupation plus contraction rank constraints.",
        "lut_meta_brief": {"coverage_ok": meta.get("coverage_ok"), "conflict_count": meta.get("conflict_count"), "subspace_count": len(lut)},
        "cores": {},
    }
    t_all = time.time()
    for name in args.cores:
        cfg = CORES[name]
        print(f"=== {name} ===", flush=True)
        raw, _T, c_ranks, inv_qs, nu = core_raw_summary(name, cfg["pivot_mask"])
        cache = build_or_load_core_cache(name, cfg["pivot_mask"], args.rank, lut, args.cache_dir, rebuild=False)
        rec = {"raw_gate": raw, "lp": {}}
        for mode in ["max_rank", "no_saturation", "min_wang_only", "min_rank"]:
            print(" solve", mode, flush=True)
            sol = solve_lp(cache, c_ranks, inv_qs, nu, mode)
            rec["lp"][mode] = sol
            print(json.dumps({"mode": mode, "success": sol["success"], "sum_nu": sol.get("sum_nu"), "minhit": sol.get("min_rank9_hit"), "elapsed": sol["elapsed_sec"]}, sort_keys=True), flush=True)
        result["cores"][name] = rec
    result["elapsed_sec"] = round(time.time() - t_all, 3)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(args.out), "elapsed_sec": result["elapsed_sec"]}, indent=2))


if __name__ == "__main__":
    main()
