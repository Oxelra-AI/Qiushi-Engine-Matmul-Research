#!/usr/bin/env python3
"""Monotone-closed Wang occupation capacity via subspace orbits.

Wang's certificate supplies one lower bound for each orbit of A-side constraint
subspaces.  If U <= V are constraint subspaces, the tensor restricted by V is a
further quotient/restriction of the tensor restricted by U, so

    rank(T restricted by U) >= rank(T restricted by V).

Thus any lower bound for V is also a valid lower bound for U.  The raw published
table is not stored in this downward-closed form.  This script builds a key ->
orbit map, computes the monotone closure on the 496-orbit poset, and then solves
occupation capacity using the closed orbit lower bounds.

For T-level rank s=20, infeasibility of the closed capacity system proves
R_F2(T_<3,3,3>) >= 21.  A feasible support only passes this A-side necessary
condition; B/C factors are a separate exact decomposition problem.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import (  # noqa: E402
    parse_cert,
    make_actions,
    rref_basis,
    rref_key,
    transform_key,
    unpack_basis,
    pack_basis,
    subspace_points_from_basis,
    all_subset_span_keys,
    occupancy_of_key,
    matrix_rank_of_mask,
)

N = 9
CANON_BY_RANK = {1: 1, 2: 1 | 16, 3: 1 | 16 | 256}


def gaussian_binomial(n: int, k: int, q: int = 2) -> int:
    num = 1
    den = 1
    for i in range(k):
        num *= q ** n - q ** i
        den *= q ** k - q ** i
    return num // den


def extension_keys(basis: Sequence[int], n: int = N) -> List[int]:
    """Immediate one-dimensional extensions of a rowspace basis."""
    pivots = {b.bit_length() - 1 for b in basis if b}
    free = [i for i in range(n) if i not in pivots]
    out = []
    for m in range(1, 1 << len(free)):
        v = 0
        for j, bit in enumerate(free):
            if (m >> j) & 1:
                v |= 1 << bit
        out.append(rref_key(list(basis) + [v], n=n))
    return out


def build_orbit_cache(cert: Path, cache: Path, force: bool = False) -> dict:
    if cache.exists() and not force:
        t0 = time.time()
        with cache.open("rb") as f:
            payload = pickle.load(f)
        print(f"Loaded orbit cache {cache} in {time.time()-t0:.2f}s; keys={len(payload['key_to_orbit']):,}")
        return payload

    records = parse_cert(cert)
    print(f"Parsed {len(records)} Wang orbit records")
    print("Generating actions...")
    t0 = time.time()
    actions = make_actions()
    print(f"  {len(actions)} actions in {time.time()-t0:.2f}s")

    key_to_orbit: Dict[int, int] = {}
    orbits = []
    conflicts = []
    t_exp = time.time()
    for oi, rec in enumerate(records):
        basis = rref_basis(rec.constraints, n=N)
        local = set()
        for img in actions:
            local.add(transform_key(basis, img))
        for key in local:
            old = key_to_orbit.get(key)
            if old is not None and old != oi:
                conflicts.append({"key": key, "old_orbit": old, "new_orbit": oi})
            key_to_orbit[key] = oi
        orbits.append({
            "position": oi,
            "cert_index": rec.index,
            "basis": list(basis),
            "dim": len(basis),
            "raw_lb": rec.lb,
            "proof_type": rec.proof_type,
            "orbit_size": len(local),
        })
        if (oi + 1) % 25 == 0 or oi + 1 == len(records):
            print(f"  orbit {oi+1:3d}/{len(records)} expanded; keys={len(key_to_orbit):,}; elapsed={time.time()-t_exp:.1f}s")

    actual_by_dim = Counter(k & 0xF for k in key_to_orbit)
    expected_by_dim = {d: gaussian_binomial(N, d) for d in range(N + 1)}
    coverage_ok = all(actual_by_dim[d] == expected_by_dim[d] for d in range(N + 1))
    if conflicts:
        print(f"WARNING conflicts: {len(conflicts)}")
    print("Coverage:")
    for d in range(N + 1):
        print(f"  dim {d}: {actual_by_dim[d]:,} / {expected_by_dim[d]:,}")

    # Immediate super-orbit graph on 496 nodes.
    super_edges = [[] for _ in orbits]
    for oi, o in enumerate(orbits):
        d = o["dim"]
        if d >= N:
            continue
        supers = set()
        for skey in extension_keys(o["basis"], n=N):
            supers.add(key_to_orbit[skey])
        super_edges[oi] = sorted(supers)

    closed = [int(o["raw_lb"]) for o in orbits]
    # Higher-dimensional super-orbits already closed when descending by dim.
    for d in range(N - 1, -1, -1):
        for oi, o in enumerate(orbits):
            if o["dim"] != d:
                continue
            best = closed[oi]
            for sj in super_edges[oi]:
                if closed[sj] > best:
                    best = closed[sj]
            closed[oi] = best

    raises = []
    for oi, o in enumerate(orbits):
        if closed[oi] != o["raw_lb"]:
            raises.append({"position": oi, "cert_index": o["cert_index"], "dim": o["dim"], "raw_lb": o["raw_lb"], "closed_lb": closed[oi], "basis": o["basis"]})
    raw_by_dim = defaultdict(Counter)
    closed_by_dim = defaultdict(Counter)
    for o, c in zip(orbits, closed):
        raw_by_dim[o["dim"]][o["raw_lb"]] += o["orbit_size"]
        closed_by_dim[o["dim"]][c] += o["orbit_size"]

    meta = {
        "cert": str(cert),
        "orbit_count": len(orbits),
        "subspace_count": len(key_to_orbit),
        "coverage_ok": coverage_ok,
        "conflict_count": len(conflicts),
        "conflicts_head": conflicts[:20],
        "actual_by_dimension": {str(k): actual_by_dim[k] for k in range(N + 1)},
        "expected_by_dimension": {str(k): expected_by_dim[k] for k in range(N + 1)},
        "raw_lb_by_dimension_subspaces": {str(d): dict(sorted(c.items())) for d, c in sorted(raw_by_dim.items())},
        "closed_lb_by_dimension_subspaces": {str(d): dict(sorted(c.items())) for d, c in sorted(closed_by_dim.items())},
        "raised_orbit_count": len(raises),
        "raises_head": raises[:100],
        "build_elapsed_sec": time.time() - t_exp,
    }
    payload = {"key_to_orbit": key_to_orbit, "orbits": orbits, "super_edges": super_edges, "closed_lb_by_orbit": closed, "meta": meta}
    cache.parent.mkdir(parents=True, exist_ok=True)
    with cache.open("wb") as f:
        pickle.dump(payload, f, protocol=pickle.HIGHEST_PROTOCOL)
    cache.with_suffix(".meta.json").write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n")
    print(f"Saved orbit cache to {cache}")
    print(json.dumps({"coverage_ok": coverage_ok, "raised_orbit_count": len(raises), "closed_lb_by_dimension_subspaces": meta["closed_lb_by_dimension_subspaces"]}, indent=2, sort_keys=True))
    return payload


def check_cn122(payload: dict) -> dict:
    from wang_capacity_lazy import load_qmm_a_factors, check_factor_multiset_against_lut
    # Materialize a tiny adapter dict-like for full scan? Simpler direct scan.
    factors = load_qmm_a_factors(Path("data/cn122_3x3_r23_repro/scheme.qmm"))
    mult = Counter(factors)
    key_to_orbit = payload["key_to_orbit"]
    closed = payload["closed_lb_by_orbit"]
    violations = []
    t0 = time.time()
    for key, oi in key_to_orbit.items():
        lb = closed[oi]
        cap = len(factors) - lb
        basis = unpack_basis(key)
        occ = sum(c for p, c in mult.items() if _in_rowspace_local(p, basis))
        if occ > cap:
            violations.append({"key": key, "dim": key & 0xF, "lb": lb, "cap": cap, "occupancy": occ, "basis": list(basis)})
            if len(violations) >= 20:
                break
    return {"factor_count": len(factors), "distinct_factors": len(mult), "max_multiplicity": max(mult.values()), "violation_count_reported": len(violations), "violations_head": violations, "elapsed_sec": time.time() - t0}


def _in_rowspace_local(v: int, basis: Sequence[int]) -> bool:
    piv = {b.bit_length() - 1: b for b in basis if b}
    x = v
    while x:
        p = x.bit_length() - 1
        b = piv.get(p)
        if b is None:
            return False
        x ^= b
    return True


def subset_violations(solution: Dict[int, int], s: int, payload: dict, max_cuts: int = 0):
    key_to_orbit = payload["key_to_orbit"]
    closed = payload["closed_lb_by_orbit"]
    support = sorted(solution)
    t0 = time.time()
    keys = all_subset_span_keys(support)
    violations = []
    for key in keys:
        oi = key_to_orbit[key]
        lb = closed[oi]
        occ = occupancy_of_key(key, solution)
        cap = s - lb
        if occ > cap:
            violations.append({"key": key, "dim": key & 0xF, "lb": lb, "cap": cap, "occupancy": occ, "excess": occ - cap, "basis": list(unpack_basis(key))})
    violations.sort(key=lambda v: (v["excess"], v["lb"], v["occupancy"], -v["dim"]), reverse=True)
    stats = {
        "support_size": len(support),
        "total_multiplicity": sum(solution.values()),
        "unique_subset_spans": len(keys),
        "violation_count": len(violations),
        "violations_by_dim": dict(Counter(v["dim"] for v in violations)),
        "violations_by_lb": dict(Counter(v["lb"] for v in violations)),
        "elapsed_sec": time.time() - t0,
    }
    return (violations[:max_cuts] if max_cuts and len(violations) > max_cuts else violations), stats


def solve_closed(payload: dict, s: int, outdir: Path, label: str, init_max_dim: int, max_iters: int, solver_time: float, max_cuts_per_iter: int, branch_rank: int) -> dict:
    from ortools.sat.python import cp_model

    key_to_orbit = payload["key_to_orbit"]
    closed = payload["closed_lb_by_orbit"]
    model = cp_model.CpModel()
    points = list(range(1, 512))
    x = {p: model.NewIntVar(0, s, f"x_{p}") for p in points}
    model.Add(sum(x[p] for p in points) == s)

    if branch_rank:
        canon = CANON_BY_RANK[branch_rank]
        model.Add(x[canon] >= 1)
        if branch_rank >= 2:
            for p in points:
                if matrix_rank_of_mask(p) < branch_rank:
                    model.Add(x[p] == 0)
        print(f"Branch rank {branch_rank}: fixed {canon}; excluded lower-rank points for branches 2/3")

    added = set()
    cuts = []

    def add_cut(key: int, reason: str) -> bool:
        if key in added:
            return False
        oi = key_to_orbit[key]
        lb = closed[oi]
        cap = s - lb
        pts = subspace_points_from_basis(unpack_basis(key))
        model.Add(sum(x[p] for p in pts) <= cap)
        added.add(key)
        cuts.append({"key": key, "dim": key & 0xF, "orbit": oi, "closed_lb": lb, "cap": cap, "point_count": len(pts), "reason": reason})
        return True

    t0 = time.time()
    for key in sorted(key_to_orbit):
        d = key & 0xF
        if 1 <= d <= init_max_dim:
            add_cut(key, f"closed_dim_le_{init_max_dim}_initial")
    print(f"Initial closed cuts dim<={init_max_dim}: {len(added):,} in {time.time()-t0:.2f}s; by dim {dict(Counter(c['dim'] for c in cuts))}; by LB {dict(Counter(c['closed_lb'] for c in cuts))}")

    history = []
    final_status = None
    final_solution = None
    for it in range(1, max_iters + 1):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = solver_time
        solver.parameters.num_search_workers = 8
        solver.parameters.random_seed = 11000 + it
        ts = time.time()
        status = solver.Solve(model)
        solve_elapsed = time.time() - ts
        status_name = {
            cp_model.OPTIMAL: "OPTIMAL",
            cp_model.FEASIBLE: "FEASIBLE",
            cp_model.INFEASIBLE: "INFEASIBLE",
            cp_model.MODEL_INVALID: "MODEL_INVALID",
            cp_model.UNKNOWN: "UNKNOWN",
        }.get(status, str(status))
        entry = {"iteration": it, "solver_status": status_name, "cut_count": len(added), "solve_elapsed_sec": solve_elapsed}
        print(f"[{label}] iter {it}: status={status_name}, cuts={len(added):,}, solve={solve_elapsed:.2f}s")
        if status in (cp_model.INFEASIBLE, cp_model.MODEL_INVALID):
            final_status = status_name
            history.append(entry)
            break
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            final_status = status_name
            history.append(entry)
            break
        sol = {p: solver.Value(var) for p, var in x.items() if solver.Value(var)}
        entry["solution"] = {str(k): v for k, v in sorted(sol.items())}
        entry["support_size"] = len(sol)
        entry["max_mult"] = max(sol.values()) if sol else 0
        entry["rank_count"] = dict(Counter(matrix_rank_of_mask(p) for p in sol for _ in range(sol[p])))
        violations, stats = subset_violations(sol, s, payload, max_cuts=max_cuts_per_iter)
        entry["check_stats"] = stats
        entry["violations_head"] = violations[:50]
        print(f"  support={len(sol)} maxmult={entry['max_mult']} ranks={entry['rank_count']} spans={stats['unique_subset_spans']:,} violations={stats['violation_count']:,} selected={len(violations):,} check={stats['elapsed_sec']:.2f}s")
        if not violations:
            final_status = "CAPACITY_FEASIBLE_MONOTONE_CLOSED_CHECK"
            final_solution = sol
            history.append(entry)
            break
        nadd = 0
        for v in violations:
            if add_cut(v["key"], f"closed_lazy_iter_{it}"):
                nadd += 1
        entry["lazy_cuts_added"] = nadd
        print(f"  added {nadd:,} closed cuts")
        history.append(entry)
        if nadd == 0:
            final_status = "STALLED_NO_NEW_CLOSED_CUTS"
            final_solution = sol
            break

    result = {
        "problem": "T-level Wang monotone-closed occupation capacity",
        "field": "F2",
        "rank_s": s,
        "label": label,
        "init_max_dim": init_max_dim,
        "max_cuts_per_iter": max_cuts_per_iter,
        "branch_rank": branch_rank,
        "final_status": final_status,
        "final_solution": {str(k): v for k, v in sorted(final_solution.items())} if final_solution else None,
        "iterations": history,
        "cut_count": len(added),
        "cuts_by_dim": dict(Counter(c["dim"] for c in cuts)),
        "cuts_by_closed_lb": dict(Counter(c["closed_lb"] for c in cuts)),
        "cut_records_head": cuts[:100],
        "cut_records_tail": cuts[-100:],
    }
    outdir.mkdir(parents=True, exist_ok=True)
    outpath = outdir / f"closed_{label}.json"
    outpath.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Saved {outpath}")
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cert", type=Path, default=Path("data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt"))
    ap.add_argument("--cache", type=Path, default=Path("data/wang_f2_lb20/wang_orbit_closed_cache.pkl"))
    ap.add_argument("--outdir", type=Path, default=Path("data/wang_capacity_closed"))
    ap.add_argument("--force-cache", action="store_true")
    ap.add_argument("--build-only", action="store_true")
    ap.add_argument("--check-cn122", action="store_true")
    ap.add_argument("--solve", action="store_true")
    ap.add_argument("--rank", type=int, default=20)
    ap.add_argument("--label", default="s20_closed")
    ap.add_argument("--init-max-dim", type=int, default=3)
    ap.add_argument("--max-iters", type=int, default=50)
    ap.add_argument("--solver-time", type=float, default=300.0)
    ap.add_argument("--max-cuts-per-iter", type=int, default=0)
    ap.add_argument("--branch-rank", type=int, choices=[0, 1, 2, 3], default=0)
    args = ap.parse_args()

    payload = build_orbit_cache(args.cert, args.cache, force=args.force_cache)
    args.outdir.mkdir(parents=True, exist_ok=True)
    if args.check_cn122:
        check = check_cn122(payload)
        print("cn122 closed-L consistency:", json.dumps(check, indent=2)[:4000])
        (args.outdir / "cn122_closed_capacity_check.json").write_text(json.dumps(check, indent=2, sort_keys=True) + "\n")
    if args.solve:
        solve_closed(payload, args.rank, args.outdir, args.label, args.init_max_dim, args.max_iters, args.solver_time, args.max_cuts_per_iter, args.branch_rank)


if __name__ == "__main__":
    main()
