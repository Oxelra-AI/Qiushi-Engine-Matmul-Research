#!/usr/bin/env python3
"""analysis: project an actual global fractional Wang-LP point to local 4D color models.

Purpose:
  analysis only optimized a few local objectives. This script performs the
  consequential experiment requested by the research state:
    1. Solve the complete E11-core Wang LP and save one full 255-coordinate
       fractional solution.
    2. For selected 4D dual flags (from pairs of dim-5 near-miss violations),
       project that fractional solution to its 16 color counts.
    3. Test whether the projected point lies in the convex hull of integer
       local color profiles satisfying the induced local Wang rows, total
       length 19, and fiber capacities.

The hull test uses column generation:
  - restricted master: exact convex-combination LP over generated profiles;
  - restricted separator: an L1-normalized separating functional for the current
    generated hull;
  - integer oracle: optimize that functional over all local integer profiles.
If the oracle maximum is strictly below the target value, we have a valid local
integer cut. If the master finds a convex combination, membership is established
for that projection. If neither happens within the iteration limit, the result is
unresolved rather than generalized.
"""
from __future__ import annotations

import json
import math
import sys
import time
from collections import defaultdict
from itertools import combinations
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np
from scipy import sparse
from scipy.optimize import Bounds as ScBounds
from scipy.optimize import LinearConstraint, linprog, milp

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import build_core_constraints
from wang_capacity_lazy import pack_basis, rref_basis, subspace_points_from_basis, unpack_basis

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/local_hull"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
BASE_SUPPORT = [1, 2, 3, 4, 8, 20, 24, 31, 32, 36, 64, 73, 109, 127, 128, 141, 160, 182, 219]


def dot2(a: int, b: int) -> int:
    return (a & b).bit_count() & 1


def rref(rows: Sequence[int], n: int = 8) -> List[int]:
    return list(rref_basis(list(rows), n=n))


def intersection_basis(b1: Sequence[int], b2: Sequence[int], n: int = 8) -> List[int]:
    s1 = set(subspace_points_from_basis(list(b1)))
    s2 = set(subspace_points_from_basis(list(b2)))
    inter = sorted(s1 & s2)
    return rref(inter, n=n) if inter else []


def annihilator_basis(primal_basis: Sequence[int], n: int = 8) -> List[int]:
    vecs = [q for q in range(1, 1 << n) if all(dot2(q, b) == 0 for b in primal_basis)]
    return rref(vecs, n=n)


def eval_color(p: int, dual_basis: Sequence[int]) -> int:
    c = 0
    for i, q in enumerate(dual_basis):
        if dot2(p, q):
            c |= 1 << i
    return c


def enumerate_subspaces(dim: int) -> List[Tuple[int, ...]]:
    pts = list(range(1, 1 << dim))
    out: List[Tuple[int, ...]] = []
    seen = set()
    for k in range(1, dim + 1):
        for combo in combinations(pts, k):
            b = tuple(rref_basis(list(combo), n=dim))
            if len(b) == k and b not in seen:
                seen.add(b)
                out.append(b)
    return out


def build_global_sparse(records, n_cols: int = 255):
    rows, cols, vals, caps = [], [], [], []
    for i, rec in enumerate(records):
        caps.append(19 - int(rec["L"]))
        bs = int(rec["point_bitset"])
        while bs:
            bit = bs & -bs
            rows.append(i)
            cols.append(bit.bit_length() - 1)
            vals.append(1.0)
            bs ^= bit
    A = sparse.csr_matrix((np.array(vals), (np.array(rows), np.array(cols))), shape=(len(records), n_cols))
    b = np.array(caps, dtype=float)
    return A, b


def solve_global_fractional(records, seed: int = 6101):
    A, b = build_global_sparse(records)
    rng = np.random.default_rng(seed)
    # A fixed random objective generally exposes a vertex without bias toward any old support.
    c = rng.normal(size=255)
    t0 = time.time()
    res = linprog(c, A_ub=A, b_ub=b,
                  A_eq=sparse.csr_matrix(np.ones((1, 255))), b_eq=np.array([19.0]),
                  bounds=[(0.0, 1.0)] * 255, method="highs", options={"time_limit": 120})
    elapsed = time.time() - t0
    if not res.success:
        raise RuntimeError(f"Global LP failed: {res.message}")
    x = np.asarray(res.x, dtype=float)
    rounded = np.rint(x)
    frac = [(i + 1, float(x[i])) for i in range(255) if abs(x[i] - rounded[i]) > 1e-7]
    slacks = b - A.dot(x)
    active = np.where(np.abs(slacks) < 1e-7)[0]
    full = {
        "objective_seed": seed,
        "objective_value": float(res.fun),
        "elapsed_sec": elapsed,
        "sum_x": float(x.sum()),
        "n_fractional_coordinates": len(frac),
        "max_round_distance": float(np.max(np.abs(x - rounded))),
        "fractional_coordinates": frac,
        "x_full": [float(v) for v in x],
        "active_constraint_count_tol_1e-7": int(len(active)),
        "active_constraints_head": [
            {
                "row_index": int(j),
                "key8": int(records[j]["key8"]),
                "dim8": int(records[j]["dim8"]),
                "L": int(records[j]["L"]),
                "cap": 19 - int(records[j]["L"]),
            }
            for j in active[:40]
        ],
    }
    return x, full


def base_violations(records) -> List[Dict]:
    bits = 0
    for p in BASE_SUPPORT:
        bits |= 1 << (p - 1)
    out = []
    for r in records:
        occ = (int(r["point_bitset"]) & bits).bit_count()
        cap = 19 - int(r["L"])
        if occ > cap:
            out.append({
                "key8": int(r["key8"]),
                "dim8": int(r["dim8"]),
                "L": int(r["L"]),
                "cap": cap,
                "occ": occ,
                "basis8": list(unpack_basis(int(r["key8"]))),
            })
    return out


def build_local_constraints(ann_basis: Sequence[int], rec_by_key: Dict[int, Dict]):
    constraints = []
    for e_basis in enumerate_subspaces(4):
        perp_colors = []
        for v in range(16):
            if all(dot2(v, e) == 0 for e in e_basis):
                perp_colors.append(v)
        lifted = []
        for e in e_basis:
            q = 0
            for k in range(4):
                if (e >> k) & 1:
                    q ^= ann_basis[k]
            lifted.append(q)
        primal_pts = [p for p in range(1, 256) if all(dot2(p, q) == 0 for q in lifted)]
        key = pack_basis(rref_basis(primal_pts, n=8))
        rec = rec_by_key[key]
        L = int(rec["L"])
        constraints.append({
            "e_basis": list(e_basis),
            "e_dim": len(e_basis),
            "perp_colors": perp_colors,
            "L": L,
            "cap": 19 - L,
            "key8": int(key),
        })
    return constraints


def local_matrix(constraints: Sequence[Dict]):
    A = np.zeros((len(constraints), 16), dtype=float)
    b = np.zeros(len(constraints), dtype=float)
    for i, con in enumerate(constraints):
        for v in con["perp_colors"]:
            A[i, v] = 1.0
        b[i] = float(con["cap"])
    return A, b


class LocalHullOracle:
    def __init__(self, constraints: Sequence[Dict]):
        self.constraints = list(constraints)
        self.A, self.b = local_matrix(self.constraints)
        self.bounds = ScBounds(lb=np.zeros(16), ub=np.array([15.0] + [16.0] * 15))
        self.integrality = np.ones(16, dtype=int)
        self.lin_constraints = [
            LinearConstraint(self.A, -np.inf, self.b),
            LinearConstraint(np.ones((1, 16)), np.array([19.0]), np.array([19.0])),
        ]
        self.ub = [15] + [16] * 15
        # Bound tightening from one- and two-color constraints.
        for con in self.constraints:
            colors = con["perp_colors"]
            if len(colors) == 1:
                self.ub[colors[0]] = min(self.ub[colors[0]], int(con["cap"]))
            if len(colors) == 2 and 0 in colors:
                other = colors[0] ^ colors[1]
                self.ub[other] = min(self.ub[other], int(con["cap"]))
        self.var_to_constraints = defaultdict(list)
        for ci, con in enumerate(self.constraints):
            for v in con["perp_colors"]:
                self.var_to_constraints[v].append(ci)

    def is_profile_feasible(self, p: Sequence[int]) -> bool:
        if sum(p) != 19:
            return False
        if any(p[i] < 0 or p[i] > self.ub[i] for i in range(16)):
            return False
        for con in self.constraints:
            if sum(p[v] for v in con["perp_colors"]) > con["cap"]:
                return False
        return True

    def optimize_float(self, a: Sequence[float], time_limit: float = 10.0):
        a = np.asarray(a, dtype=float)
        res = milp(c=-a, integrality=self.integrality, bounds=self.bounds,
                   constraints=self.lin_constraints,
                   options={"time_limit": time_limit, "mip_rel_gap": 0.0, "presolve": True})
        if not res.success:
            return None, None, str(res.message)
        prof = tuple(int(round(v)) for v in res.x)
        val = float(np.dot(a, prof))
        return prof, val, str(res.message)

    def exact_max_integer_coeff(self, coeff: Sequence[int]):
        """Exact branch-and-bound max for a 16-variable integer objective.

        This is used only to validate a final rounded cut. The search is finite
        over local count profiles; it records node count to expose computational
        weight. It is not a formal proof certificate, but it avoids depending on
        floating MIP optimality for the final beta.
        """
        coeff = [int(c) for c in coeff]
        order = sorted(range(16), key=lambda v: (-abs(coeff[v]), self.ub[v], v))
        suffix_pos = [0] * (len(order) + 1)
        for i in range(len(order) - 1, -1, -1):
            v = order[i]
            suffix_pos[i] = suffix_pos[i + 1] + max(coeff[v], 0) * self.ub[v]
        sums = [0] * len(self.constraints)
        assigned = [0] * 16
        best_val = -10**30
        best_prof = None
        nodes = 0
        t0 = time.time()

        def dfs(pos: int, rem: int, obj: int):
            nonlocal best_val, best_prof, nodes
            nodes += 1
            if rem < 0:
                return
            if pos == len(order):
                if rem == 0 and obj > best_val:
                    prof = tuple(assigned)
                    if self.is_profile_feasible(prof):
                        best_val = obj
                        best_prof = prof
                return
            # easy upper bound: remaining positive coefficients at upper bounds
            if obj + suffix_pos[pos] <= best_val:
                return
            v = order[pos]
            maxv = min(self.ub[v], rem)
            # Explore good objective values first.
            vals = range(maxv, -1, -1) if coeff[v] >= 0 else range(0, maxv + 1)
            for val in vals:
                ok = True
                for ci in self.var_to_constraints[v]:
                    sums[ci] += val
                    if sums[ci] > self.constraints[ci]["cap"]:
                        ok = False
                if ok:
                    assigned[v] = val
                    dfs(pos + 1, rem - val, obj + coeff[v] * val)
                    assigned[v] = 0
                for ci in self.var_to_constraints[v]:
                    sums[ci] -= val

        dfs(0, 19, 0)
        return {"best_value": best_val, "best_profile": list(best_prof) if best_prof is not None else None,
                "nodes": nodes, "elapsed_sec": time.time() - t0}


def convex_membership_column_generation(target: Sequence[float], oracle: LocalHullOracle,
                                        max_iters: int = 80, tol: float = 1e-7):
    target = np.asarray(target, dtype=float)
    profiles: Dict[Tuple[int, ...], str] = {}

    def add_profile(p, reason):
        if p is not None and oracle.is_profile_feasible(p):
            profiles.setdefault(tuple(p), reason)

    # Seed profiles with coordinate/rand objective optima. Include both signs so
    # the generated hull has a chance to surround an interior target.
    rng = np.random.default_rng(6117)
    directions = []
    for i in range(16):
        e = np.zeros(16); e[i] = 1.0; directions.append((e, f"max_c{i}"))
        directions.append((-e, f"min_c{i}"))
    directions.append((target - target.mean(), "target_centered"))
    directions.append((-(target - target.mean()), "neg_target_centered"))
    for k in range(20):
        directions.append((rng.normal(size=16), f"random_{k}"))
    oracle_log = []
    for a, reason in directions:
        p, val, msg = oracle.optimize_float(a, time_limit=5.0)
        oracle_log.append({"phase": "seed", "reason": reason, "status": msg, "value": val})
        add_profile(p, reason)

    iteration_log = []
    membership_certificate = None
    separation_certificate = None

    for it in range(max_iters):
        P = np.array(list(profiles.keys()), dtype=float)  # m x 16
        m = P.shape[0]
        # Master membership LP: find lambdas with P^T lambda = target, sum lambda=1.
        A_eq = np.vstack([np.ones((1, m)), P.T])
        b_eq = np.concatenate([[1.0], target])
        res_mem = linprog(np.zeros(m), A_eq=A_eq, b_eq=b_eq, bounds=[(0.0, None)] * m,
                          method="highs")
        if res_mem.success:
            lam = res_mem.x
            recon = lam @ P
            resid = float(np.max(np.abs(recon - target)))
            active_terms = [(int(i), float(lam[i]), list(map(int, P[i])))
                            for i in range(m) if lam[i] > 1e-8]
            membership_certificate = {
                "status": "in_convex_hull_of_generated_profiles",
                "iteration": it,
                "profile_count": int(m),
                "max_reconstruction_residual": resid,
                "active_combination_size": len(active_terms),
                "active_combination": active_terms[:40],
            }
            iteration_log.append({"iteration": it, "profile_count": int(m), "master": "membership", "residual": resid})
            break

        # Restricted separator LP: maximize a.target - eta subject a.p <= eta
        # for generated profiles and ||a||_1 <= 1. Variables are a+ (16), a- (16), eta.
        nvar = 33
        c_obj = np.zeros(nvar)
        c_obj[:16] = -target
        c_obj[16:32] = target
        c_obj[32] = 1.0  # minimize -a.target + eta
        A_ub = []
        b_ub = []
        for p in P:
            row = np.zeros(nvar)
            row[:16] = p
            row[16:32] = -p
            row[32] = -1.0
            A_ub.append(row); b_ub.append(0.0)
        row = np.zeros(nvar); row[:32] = 1.0
        A_ub.append(row); b_ub.append(1.0)
        bounds = [(0.0, None)] * 32 + [(-25.0, 25.0)]
        res_sep = linprog(c_obj, A_ub=np.array(A_ub), b_ub=np.array(b_ub), bounds=bounds, method="highs")
        if not res_sep.success:
            iteration_log.append({"iteration": it, "profile_count": int(m), "master": "separator_failed", "message": res_sep.message})
            break
        z = res_sep.x
        a = z[:16] - z[16:32]
        eta = z[32]
        target_val = float(np.dot(a, target))
        restricted_margin = target_val - float(eta)
        if restricted_margin <= tol:
            iteration_log.append({"iteration": it, "profile_count": int(m), "master": "no_restricted_separator", "margin": restricted_margin})
            break
        p_oracle, M, msg = oracle.optimize_float(a, time_limit=10.0)
        if p_oracle is None:
            iteration_log.append({"iteration": it, "profile_count": int(m), "master": "oracle_failed", "message": msg})
            break
        full_margin = target_val - float(M)
        iteration_log.append({
            "iteration": it, "profile_count": int(m), "restricted_margin": restricted_margin,
            "target_value": target_val, "restricted_eta": float(eta), "oracle_max": float(M),
            "full_margin": full_margin, "oracle_profile": list(p_oracle),
        })
        if full_margin > 1e-6:
            # Validate a rounded integer cut as an independently checkable finite search.
            scale = 1000000.0
            h = [int(round(scale * ai)) for ai in a]
            g = 0
            for v in h:
                g = math.gcd(g, abs(v))
            if g > 1:
                h = [v // g for v in h]
            exact = oracle.exact_max_integer_coeff(h)
            h_target = float(np.dot(np.array(h, dtype=float), target))
            separation_certificate = {
                "status": "separated_by_local_integer_hull",
                "iteration": it,
                "profile_count": int(m),
                "float_a": [float(ai) for ai in a],
                "float_target_value": target_val,
                "float_oracle_beta": float(M),
                "float_margin": full_margin,
                "rounded_integer_coefficients": h,
                "integer_beta_exact_search": exact["best_value"],
                "integer_beta_profile": exact["best_profile"],
                "integer_exact_search_nodes": exact["nodes"],
                "integer_exact_search_elapsed_sec": exact["elapsed_sec"],
                "rounded_target_value": h_target,
                "rounded_margin": h_target - exact["best_value"],
                "interpretation": "If rounded_margin is positive by a safe tolerance, sum_p h[color(p)] x_p <= integer_beta is a valid local integer cut separating this fractional projection. This is a computational certificate, not a formal proof log.",
            }
            break
        add_profile(p_oracle, f"oracle_iter_{it}")
        if tuple(p_oracle) in profiles and profiles[tuple(p_oracle)] != f"oracle_iter_{it}":
            # Already had this profile and it does not separate: no progress.
            pass

    status = "unresolved"
    if membership_certificate is not None:
        status = "membership_found"
    if separation_certificate is not None:
        status = "separation_found"
    return {
        "status": status,
        "target_profile": [float(v) for v in target],
        "final_profile_count": len(profiles),
        "seed_oracle_log_head": oracle_log[:10],
        "iteration_log": iteration_log,
        "membership_certificate": membership_certificate,
        "separation_certificate": separation_certificate,
    }


def main():
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    lut, _ = load_lut(LUT_PATH)
    core = CoreQuotient(1)
    records, meta = build_core_constraints(core, lut)
    rec_by_key = {int(r["key8"]): r for r in records}
    print(f"Built {len(records)} core Wang records")

    x, global_info = solve_global_fractional(records)
    print(f"Global LP: {global_info['n_fractional_coordinates']} fractional coordinates; sum={global_info['sum_x']:.12f}")

    violations = base_violations(records)
    d5 = [v for v in violations if v["dim8"] == 5]
    pairs = []
    for i, j in combinations(range(len(d5)), 2):
        inter = intersection_basis(d5[i]["basis8"], d5[j]["basis8"])
        if len(inter) == 4:
            pairs.append((i, j, inter))
    print(f"Base support violations={len(violations)}; dim5={len(d5)}; selected dim4-intersection pairs={len(pairs)}")

    pair_results = []
    for pair_index, (i, j, inter) in enumerate(pairs[:4]):
        ann = annihilator_basis(inter)
        constraints = build_local_constraints(ann, rec_by_key)
        oracle = LocalHullOracle(constraints)
        target = np.zeros(16, dtype=float)
        for p in range(1, 256):
            target[eval_color(p, ann)] += x[p - 1]
        # Diagnostic: target should satisfy local LP inequalities inherited from full LP.
        A_loc, b_loc = local_matrix(constraints)
        local_slacks = b_loc - A_loc.dot(target)
        nm_profile = [0] * 16
        for p in BASE_SUPPORT:
            nm_profile[eval_color(p, ann)] += 1
        nm_viol = [idx for idx, con in enumerate(constraints) if sum(nm_profile[v] for v in con["perp_colors"]) > con["cap"]]
        print(f"Pair {pair_index}: target min local slack={local_slacks.min():.3e}; near-miss local violations={len(nm_viol)}")
        cg = convex_membership_column_generation(target, oracle, max_iters=60)
        print(f"  hull test status={cg['status']}, profiles={cg['final_profile_count']}")
        pair_results.append({
            "pair_index": pair_index,
            "violation_indices": [i, j],
            "violation_keys": [d5[i]["key8"], d5[j]["key8"]],
            "intersection_basis": inter,
            "annihilator_basis": ann,
            "target_profile": [float(v) for v in target],
            "target_sum": float(target.sum()),
            "target_min_local_slack": float(local_slacks.min()),
            "target_tight_local_constraints": int(np.sum(np.abs(local_slacks) < 1e-7)),
            "near_miss_profile": nm_profile,
            "near_miss_local_violation_count": len(nm_viol),
            "near_miss_local_violation_indices": nm_viol[:20],
            "local_constraint_L_cap_hist": {f"L{int(c['L'])}_cap{int(c['cap'])}": 0 for c in constraints},
            "hull_test": cg,
        })

    # fill hist counters compactly after building (kept late to avoid clutter)
    for pr in pair_results:
        hist = defaultdict(int)
        ann = pr["annihilator_basis"]
        constraints = build_local_constraints(ann, rec_by_key)
        for c in constraints:
            hist[f"L{int(c['L'])}_cap{int(c['cap'])}"] += 1
        pr["local_constraint_L_cap_hist"] = dict(sorted(hist.items()))

    out_global = OUTDIR / "global_fractional_solution.json"
    out_global.write_text(json.dumps({
        "schema": "global_fractional_solution_v1",
        "meaning": "One full 255-coordinate fractional solution of the complete E11-core Wang LP; this is a target for local integer-hull projection, not a measurement that all vertices are fractional.",
        "global_lp": global_info,
    }, indent=2) + "\n")

    out = OUTDIR / "fractional_local_membership.json"
    out.write_text(json.dumps({
        "schema": "fractional_local_membership_v1",
        "elapsed_sec": time.time() - t0,
        "meaning": "Projection of one complete-Wang LP fractional point to selected 4D dual color models, with column-generation tests for membership/separation against local integer profiles. Membership is projection-specific; separation is a valid local integer cut only when the oracle closes the inequality.",
        "global_solution_file": str(out_global),
        "base_support": BASE_SUPPORT,
        "base_violation_count": len(violations),
        "selected_pair_count": len(pair_results),
        "pair_results": pair_results,
    }, indent=2) + "\n")
    print(f"Saved {out_global}")
    print(f"Saved {out}")
    print(f"Elapsed {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
