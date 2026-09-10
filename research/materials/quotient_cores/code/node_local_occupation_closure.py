#!/usr/bin/env python3
"""Node-local Wang occupation closure tests.

For a Wang certificate node W with stored lower bound L = LB(W), testing
whether the occupation layer alone can raise the node to L+1 means asking
whether a length-L A-multiset for T/W can satisfy all inherited Wang rows
from strict super-subspaces U > W:

    sum_{q in (U/W)\setminus 0} x_q <= L - LB(U),    sum_q x_q = L.

If this integer system is infeasible, the node can be tightened by one using
occupation inequalities only.  If it is feasible, the current LUT value is
occupation-closed at that node.  This script checks orbit representatives from
Wang's closed orbit cache, using all quotient subspaces of F_2^(9-d) for nodes
with quotient dimension up to a chosen limit.

The script is deliberately separate from the earlier bottom_up_tightening*.py
pilots, whose first version used the wrong hyperplane/child mapping and whose
second version used the wrong support-size convention for a one-ARTIFACT raise.
"""
from __future__ import annotations

import argparse
import json
import os
import pickle
import sys
import time
from collections import Counter, defaultdict
from functools import lru_cache
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

try:
    from ortools.sat.python import cp_model  # type: ignore
except Exception:  # pragma: no cover
    cp_model = None

S04S = Path("scripts")
if str(S04S) not in sys.path:
    sys.path.insert(0, str(S04S))
from wang_capacity_lazy import unpack_basis  # type: ignore

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
CACHE_PATH = Path("data/wang_f2_lb20/wang_orbit_closed_cache.pkl")
OUTDIR = Path("data/wang_analysis/node_local")


def rref_basis(rows: Iterable[int], nbits: int = 9) -> Tuple[int, ...]:
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
        x |= int(b) << (9 * i)
    return (x << 4) | len(basis_rref)


def in_span(v0: int, rref: Sequence[int]) -> bool:
    v = int(v0)
    for rb in rref:
        p = int(rb).bit_length() - 1
        if p >= 0 and ((v >> p) & 1):
            v ^= int(rb)
    return v == 0


def free_bits_from_rref(rref: Sequence[int], nbits: int = 9) -> List[int]:
    piv = {int(rb).bit_length() - 1 for rb in rref if int(rb)}
    return [i for i in range(nbits) if i not in piv]


def lift_q(q: int, free_bits: Sequence[int]) -> int:
    v = 0
    for i, bit in enumerate(free_bits):
        if (q >> i) & 1:
            v |= 1 << bit
    return v


@lru_cache(maxsize=None)
def all_subspace_bases(k: int) -> Tuple[Tuple[int, ...], ...]:
    """All row-space RREF bases of F2^k, represented by ints 0..2^k-1.

    Built by incremental closure over vectors.  k<=7 is tiny; k=8 has millions
    of subspaces and is intentionally not used by default.
    """
    spaces = {tuple()}
    for v in range(1, 1 << k):
        new = []
        for sp in spaces:
            if not in_span(v, sp):
                new.append(rref_basis((*sp, v), k))
        spaces.update(new)
    return tuple(sorted(spaces, key=lambda b: (len(b), b)))


@lru_cache(maxsize=None)
def strict_nonzero_proper_subspaces(k: int) -> Tuple[Tuple[int, ...], ...]:
    return tuple(b for b in all_subspace_bases(k) if 0 < len(b) < k)


@lru_cache(maxsize=None)
def mask_from_qbasis(qbasis: Tuple[int, ...]) -> int:
    d = len(qbasis)
    mask = 0
    for m in range(1, 1 << d):
        q = 0
        for i, b in enumerate(qbasis):
            if (m >> i) & 1:
                q ^= int(b)
        mask |= 1 << (q - 1)
    return mask


def popcount(x: int) -> int:
    return int(x).bit_count()


def solve_local_cp(k: int, support_size: int, constraints: List[Tuple[int, int]], time_limit: float, workers: int) -> Dict:
    if cp_model is None:
        return {"status": "NO_ORTOOLS", "feasible": None}
    model = cp_model.CpModel()
    npts = (1 << k) - 1
    xs = [model.NewIntVar(0, support_size, f"x_{i+1}") for i in range(npts)]
    model.Add(sum(xs) == support_size)
    for mask, cap in constraints:
        if cap < 0:
            model.Add(0 <= -1)
            continue
        pts = [i for i in range(npts) if (mask >> i) & 1]
        if not pts:
            if cap < 0:
                model.Add(0 <= -1)
        elif cap < support_size:
            model.Add(sum(xs[i] for i in pts) <= cap)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.num_search_workers = int(workers)
    solver.parameters.random_seed = 21
    t0 = time.time()
    st = solver.Solve(model)
    elapsed = time.time() - t0
    name = solver.StatusName(st)
    if st in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        sol = [int(solver.Value(x)) for x in xs]
        return {
            "status": name,
            "feasible": True,
            "elapsed_sec": elapsed,
            "conflicts": int(solver.NumConflicts()),
            "branches": int(solver.NumBranches()),
            "support_nonzero_count": int(sum(1 for z in sol if z)),
            "max_multiplicity": int(max(sol) if sol else 0),
            "solution": sol,
        }
    if st == cp_model.INFEASIBLE:
        return {"status": name, "feasible": False, "elapsed_sec": elapsed, "conflicts": int(solver.NumConflicts()), "branches": int(solver.NumBranches())}
    return {"status": name, "feasible": None, "elapsed_sec": elapsed, "conflicts": int(solver.NumConflicts()), "branches": int(solver.NumBranches())}


def node_constraints(W_basis: Sequence[int], lut: Dict[int, int], support_size: int) -> Tuple[List[Tuple[int, int]], Dict]:
    W = rref_basis(W_basis, 9)
    d = len(W)
    k = 9 - d
    free = free_bits_from_rref(W, 9)
    constraints: Dict[int, int] = {}
    row_meta = []
    missing = 0
    cap_hist = Counter(); subdim_hist = Counter(); pop_hist = Counter()
    cap_negative = 0; tautological = 0
    for qbasis in strict_nonzero_proper_subspaces(k):
        lifts = [lift_q(q, free) for q in qbasis]
        U = rref_basis((*W, *lifts), 9)
        key = pack_basis(U)
        lb = lut.get(key)
        if lb is None:
            missing += 1
            continue
        cap = int(support_size) - int(lb)
        mask = mask_from_qbasis(tuple(qbasis))
        # Same quotient mask should be unique, but if duplicates arise keep strongest cap.
        if mask not in constraints or cap < constraints[mask]:
            constraints[mask] = cap
        cap_hist[cap] += 1; subdim_hist[len(qbasis)] += 1; pop_hist[popcount(mask)] += 1
        if cap < 0: cap_negative += 1
        if cap >= support_size: tautological += 1
    rows = sorted(constraints.items(), key=lambda mc: (mc[1], popcount(mc[0]), mc[0]))
    meta = {
        "node_dim": d,
        "quotient_dim": k,
        "strict_subspace_rows": len(strict_nonzero_proper_subspaces(k)),
        "unique_masks": len(rows),
        "missing_lut_rows": missing,
        "cap_hist": dict(sorted((int(a), int(b)) for a, b in cap_hist.items())),
        "subspace_dim_hist": dict(sorted((int(a), int(b)) for a, b in subdim_hist.items())),
        "mask_popcount_hist": dict(sorted((int(a), int(b)) for a, b in pop_hist.items())),
        "negative_cap_rows": cap_negative,
        "tautological_rows": tautological,
    }
    return rows, meta


def load_data():
    with LUT_PATH.open("rb") as f:
        data = pickle.load(f)
    lut = data["lut"] if isinstance(data, dict) and "lut" in data else data
    with CACHE_PATH.open("rb") as f:
        cache = pickle.load(f)
    return lut, cache


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dims", default="3,4,5,6,7,8", help="node dimensions to check, comma separated")
    ap.add_argument("--max-qdim", type=int, default=7)
    ap.add_argument("--mode", choices=["raise", "legacy_plus_one"], default="raise", help="raise: support_size=LB(W); legacy_plus_one reproduces analysis's off-by-one pilot")
    ap.add_argument("--time-limit", type=float, default=3.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--limit-per-dim", type=int, default=0)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    dims = {int(x) for x in args.dims.split(',') if x.strip()}
    OUTDIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    lut, cache = load_data()
    reps = cache["orbits"]
    results = []
    summary_by_dim = defaultdict(Counter)
    checked_by_dim = Counter()
    for orb in reps:
        d = int(orb["dim"])
        if d not in dims:
            continue
        k = 9 - d
        if k > args.max_qdim:
            continue
        if args.limit_per_dim and checked_by_dim[d] >= args.limit_per_dim:
            continue
        L = int(orb["raw_lb"])
        support_size = L if args.mode == "raise" else L + 1
        rows, meta = node_constraints(tuple(int(x) for x in orb["basis"]), lut, support_size)
        if meta["negative_cap_rows"]:
            solve = {"status": "NEGATIVE_CAP", "feasible": False, "elapsed_sec": 0.0}
        else:
            solve = solve_local_cp(k, support_size, rows, args.time_limit, args.workers)
        status = "unknown" if solve.get("feasible") is None else ("feasible" if solve.get("feasible") else "infeasible")
        summary_by_dim[d][status] += 1
        summary_by_dim[d][f"lb_{L}"] += 1
        checked_by_dim[d] += 1
        rec = {
            "position": int(orb.get("position", -1)),
            "cert_index": int(orb.get("cert_index", orb.get("index", -1))),
            "dim": d,
            "quotient_dim": k,
            "old_lb": L,
            "attempted_new_lb": L + 1 if args.mode == "raise" else None,
            "support_size_tested": support_size,
            "proof_type": orb.get("proof_type"),
            "orbit_size": int(orb.get("orbit_size", -1)),
            "basis": [int(x) for x in orb["basis"]],
            "constraint_meta": meta,
            "solve": solve,
        }
        # Do not keep all dense solutions for large outputs; keep only first 40 entries and summary.
        if solve.get("solution") is not None:
            sol = solve.pop("solution")
            nz = [(i + 1, int(v)) for i, v in enumerate(sol) if v]
            rec["solve"]["solution_head"] = nz[:40]
            rec["solve"]["solution_weight_check"] = int(sum(v for _, v in nz))
        results.append(rec)
        print(f"dim={d} idx={rec['cert_index']} L={L} support={support_size} rows={meta['unique_masks']} status={status} cp={solve.get('status')} elapsed={solve.get('elapsed_sec',0):.3f}", flush=True)
    out = {
        "schema": "node_local_occupation_closure_v1",
        "interpretation": "mode=raise tests whether occupation rows over all strict super-subspaces exclude length LB(W), which would raise node LB by one. Feasible means occupation-closed at that node, not tensor-decomposition feasible.",
        "mode": args.mode,
        "dims": sorted(dims),
        "max_qdim": args.max_qdim,
        "time_limit_per_node_sec": args.time_limit,
        "checked_total": len(results),
        "summary_by_dim": {str(d): dict(c) for d, c in sorted(summary_by_dim.items())},
        "results": results,
        "elapsed_sec": time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status":"ok", "out":str(args.out), "checked_total":len(results), "summary_by_dim":out["summary_by_dim"], "elapsed_sec":out["elapsed_sec"]}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
