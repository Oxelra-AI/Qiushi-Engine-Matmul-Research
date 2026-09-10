#!/usr/bin/env python3
"""analysis: face-conditioned local hull tests for the saved fractional Wang-LP point.

analysis showed that selected 4D local color projections of one global fractional
LP solution lie in generic local integer hulls.  The generic local hulls forgot a
crucial fact: the fractional point x has support J of only 65 nonzero point
coordinates.  Any nonnegative convex representation of x by binary 19-supports
would use only points in J, because outside coordinates have expectation zero.

For each selected 4D dual color map, this script replaces the generic fiber caps
(15 for color 0, 16 otherwise) by the face caps |J ∩ fiber(color)|.  It then
checks whether the projected target is in the convex hull of local integer
profiles satisfying:
  * total count 19;
  * 0 <= c_v <= |J ∩ fiber(v)|;
  * the 66 induced E11 Wang inequalities for subspaces of the 4D dual flag.

If a local separating functional h is found and validated by an exact finite
search over integer profiles, the script also builds the globally valid cut
  h·c <= beta + M * sum_{p notin J} x_p,
where M = max(0, U - beta) and U is the sum of the 19 largest coefficients
h[color(p)] over all 255 points.  This cut is valid for every distinct 19-point
support: with no outside point the face-local bound applies; with at least one
outside point the right side is at least U, a trivial global upper bound.

These are computational witnesses/cuts for the support-incidence problem, not a
rank lower-bound proof by themselves.
"""
from __future__ import annotations

import json
import math
import sys
import time
from collections import defaultdict
from itertools import combinations
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np
from scipy.optimize import Bounds as ScBounds
from scipy.optimize import LinearConstraint, linprog, milp

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import build_core_constraints
from wang_capacity_lazy import pack_basis, rref_basis
from fractional_local_membership import (
    dot2,
    eval_color,
    build_local_constraints,
    local_matrix,
)

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/face_local_hull"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
GLOBAL_PATH = ROOT / "workspace/data/local_hull/global_fractional_solution.json"
OLD_MEMBERSHIP_PATH = ROOT / "workspace/data/local_hull/fractional_local_membership.json"
ACTIVE_MEMBERSHIP_PATH = ROOT / "workspace/data/local_hull/active_fractional_local_membership.json"


def load_global_x(tol: float = 1e-10):
    data = json.loads(GLOBAL_PATH.read_text())
    x = np.array(data["global_lp"]["x_full"], dtype=float)
    J = [p for p in range(1, 256) if x[p - 1] > tol]
    outside = [p for p in range(1, 256) if x[p - 1] <= tol]
    return x, J, outside, data


def selected_maps() -> List[Dict]:
    out: List[Dict] = []
    seen = set()
    for path, label in [(OLD_MEMBERSHIP_PATH, "old_near_miss_pair"), (ACTIVE_MEMBERSHIP_PATH, "active_lp_pair")]:
        data = json.loads(path.read_text())
        for pr in data.get("pair_results", []):
            ann = tuple(int(v) for v in pr["annihilator_basis"])
            if ann in seen:
                continue
            seen.add(ann)
            out.append({
                "source_file": str(path),
                "source_label": label,
                "source_pair_index": int(pr["pair_index"]),
                "annihilator_basis": list(ann),
                "intersection_basis": pr.get("intersection_basis"),
                "source_target_min_local_slack": pr.get("target_min_local_slack"),
                "source_target_tight_local_constraints": pr.get("target_tight_local_constraints"),
                "source_hull_status": pr.get("hull_test", {}).get("status"),
            })
    return out


def fiber_caps_and_target(ann_basis: Sequence[int], x: np.ndarray, J: Sequence[int]):
    caps = [0] * 16
    target = np.zeros(16, dtype=float)
    for p in J:
        c = eval_color(p, ann_basis)
        caps[c] += 1
        target[c] += x[p - 1]
    return caps, target


class FaceLocalOracle:
    def __init__(self, constraints: Sequence[Dict], fiber_caps: Sequence[int]):
        self.constraints = list(constraints)
        self.A, self.b = local_matrix(self.constraints)
        self.fiber_caps = [int(v) for v in fiber_caps]
        self.ub = list(self.fiber_caps)
        # Tighten using one-color and {0,v} constraints, but never exceed face caps.
        for con in self.constraints:
            colors = con["perp_colors"]
            if len(colors) == 1:
                v = colors[0]
                self.ub[v] = min(self.ub[v], int(con["cap"]))
        for con in self.constraints:
            colors = con["perp_colors"]
            if len(colors) == 2 and 0 in colors:
                other = colors[0] ^ colors[1]
                self.ub[other] = min(self.ub[other], int(con["cap"]))
        self.bounds = ScBounds(lb=np.zeros(16), ub=np.array(self.ub, dtype=float))
        self.integrality = np.ones(16, dtype=int)
        self.lin_constraints = [
            LinearConstraint(self.A, -np.inf, self.b),
            LinearConstraint(np.ones((1, 16)), np.array([19.0]), np.array([19.0])),
        ]
        self.var_to_constraints = defaultdict(list)
        for ci, con in enumerate(self.constraints):
            for v in con["perp_colors"]:
                self.var_to_constraints[v].append(ci)

    def is_profile_feasible(self, prof: Sequence[int]) -> bool:
        if len(prof) != 16:
            return False
        if sum(prof) != 19:
            return False
        for i, val in enumerate(prof):
            if int(val) != val or val < 0 or val > self.ub[i]:
                return False
        for con in self.constraints:
            if sum(prof[v] for v in con["perp_colors"]) > int(con["cap"]):
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
        if not self.is_profile_feasible(prof):
            return None, None, "solver_returned_profile_failing_local_check"
        return prof, float(np.dot(a, prof)), str(res.message)

    def exact_feasible_profile(self):
        order = sorted(range(16), key=lambda v: (self.ub[v], v))
        suffix = [0] * (len(order) + 1)
        for i in range(len(order) - 1, -1, -1):
            suffix[i] = suffix[i + 1] + self.ub[order[i]]
        assigned = [0] * 16
        sums = [0] * len(self.constraints)
        nodes = 0
        t0 = time.time()
        found: Optional[Tuple[int, ...]] = None

        def dfs(pos: int, rem: int) -> bool:
            nonlocal nodes, found
            nodes += 1
            if rem < 0 or rem > suffix[pos]:
                return False
            if pos == len(order):
                if rem == 0 and self.is_profile_feasible(assigned):
                    found = tuple(assigned)
                    return True
                return False
            v = order[pos]
            for val in range(min(self.ub[v], rem) + 1):
                ok = True
                for ci in self.var_to_constraints[v]:
                    sums[ci] += val
                    if sums[ci] > int(self.constraints[ci]["cap"]):
                        ok = False
                if ok:
                    assigned[v] = val
                    if dfs(pos + 1, rem - val):
                        return True
                    assigned[v] = 0
                for ci in self.var_to_constraints[v]:
                    sums[ci] -= val
            return False

        ok = dfs(0, 19)
        return {"feasible": bool(ok), "profile": list(found) if found is not None else None,
                "nodes": nodes, "elapsed_sec": time.time() - t0}

    def exact_max_integer_coeff(self, coeff: Sequence[int]):
        coeff = [int(c) for c in coeff]
        # Put high-impact variables early; still use exact DP upper bounds over the remaining total count.
        order = sorted(range(16), key=lambda v: (-abs(coeff[v]), self.ub[v], v))
        n = len(order)
        neg_inf = -10**60
        dp = [[neg_inf] * 20 for _ in range(n + 1)]
        dp[n][0] = 0
        for pos in range(n - 1, -1, -1):
            v = order[pos]
            for r in range(20):
                best = neg_inf
                for val in range(min(self.ub[v], r) + 1):
                    tail = dp[pos + 1][r - val]
                    if tail != neg_inf:
                        best = max(best, coeff[v] * val + tail)
                dp[pos][r] = best
        assigned = [0] * 16
        sums = [0] * len(self.constraints)
        best_val = neg_inf
        best_prof: Optional[Tuple[int, ...]] = None
        nodes = 0
        t0 = time.time()

        def dfs(pos: int, rem: int, obj: int):
            nonlocal best_val, best_prof, nodes
            nodes += 1
            if rem < 0:
                return
            ubound = dp[pos][rem]
            if ubound == neg_inf or obj + ubound <= best_val:
                return
            if pos == n:
                if rem == 0 and obj > best_val and self.is_profile_feasible(assigned):
                    best_val = obj
                    best_prof = tuple(assigned)
                return
            v = order[pos]
            vals = range(min(self.ub[v], rem), -1, -1) if coeff[v] >= 0 else range(0, min(self.ub[v], rem) + 1)
            for val in vals:
                ok = True
                for ci in self.var_to_constraints[v]:
                    sums[ci] += val
                    if sums[ci] > int(self.constraints[ci]["cap"]):
                        ok = False
                if ok:
                    assigned[v] = val
                    dfs(pos + 1, rem - val, obj + coeff[v] * val)
                    assigned[v] = 0
                for ci in self.var_to_constraints[v]:
                    sums[ci] -= val

        dfs(0, 19, 0)
        return {"best_value": int(best_val) if best_val != neg_inf else None,
                "best_profile": list(best_prof) if best_prof is not None else None,
                "nodes": nodes, "elapsed_sec": time.time() - t0}


def column_generation(target: Sequence[float], oracle: FaceLocalOracle,
                      max_iters: int = 100, tol: float = 1e-8):
    target = np.asarray(target, dtype=float)
    profiles: Dict[Tuple[int, ...], str] = {}

    def add_profile(p, reason):
        if p is None:
            return False
        if not oracle.is_profile_feasible(p):
            return False
        old = tuple(p) in profiles
        profiles.setdefault(tuple(p), reason)
        return not old

    feasibility = oracle.exact_feasible_profile()
    if not feasibility["feasible"]:
        return {
            "status": "face_local_integer_empty",
            "target_profile": [float(v) for v in target],
            "exact_feasibility": feasibility,
            "final_profile_count": 0,
            "iteration_log": [],
            "membership_certificate": None,
            "separation_certificate": None,
        }
    add_profile(tuple(feasibility["profile"]), "exact_feasible_seed")

    rng = np.random.default_rng(6201)
    directions: List[Tuple[np.ndarray, str]] = []
    for i in range(16):
        e = np.zeros(16); e[i] = 1.0
        directions.append((e, f"max_c{i}"))
        directions.append((-e, f"min_c{i}"))
    centered = target - target.mean()
    directions.append((centered, "target_centered"))
    directions.append((-centered, "neg_target_centered"))
    # Include directions that stress face caps: high target/cap ratios and low slack colors.
    cap_arr = np.array(oracle.fiber_caps, dtype=float)
    ratio = np.zeros(16)
    for i in range(16):
        ratio[i] = target[i] / cap_arr[i] if cap_arr[i] > 0 else 0.0
    directions.append((ratio - ratio.mean(), "target_over_facecap_centered"))
    directions.append((-(ratio - ratio.mean()), "neg_target_over_facecap_centered"))
    for k in range(30):
        directions.append((rng.normal(size=16), f"random_{k}"))

    seed_log = []
    for a, reason in directions:
        p, val, msg = oracle.optimize_float(a, time_limit=5.0)
        changed = add_profile(p, reason)
        seed_log.append({"reason": reason, "status": msg, "value": val, "new_profile": bool(changed)})

    iteration_log = []
    membership_certificate = None
    separation_certificate = None
    duplicate_oracle_steps = 0

    for it in range(max_iters):
        P = np.array(list(profiles.keys()), dtype=float)
        m = int(P.shape[0])
        A_eq = np.vstack([np.ones((1, m)), P.T])
        b_eq = np.concatenate([[1.0], target])
        res_mem = linprog(np.zeros(m), A_eq=A_eq, b_eq=b_eq, bounds=[(0.0, None)] * m,
                          method="highs")
        if res_mem.success:
            lam = res_mem.x
            recon = lam @ P
            resid = float(np.max(np.abs(recon - target)))
            active = [(int(i), float(lam[i]), list(map(int, P[i]))) for i in range(m) if lam[i] > 1e-8]
            membership_certificate = {
                "status": "in_face_conditioned_local_hull_of_generated_profiles",
                "iteration": it,
                "profile_count": m,
                "max_reconstruction_residual": resid,
                "active_combination_size": len(active),
                "active_combination": active[:80],
            }
            iteration_log.append({"iteration": it, "profile_count": m, "master": "membership", "residual": resid})
            break

        # Restricted separator: maximize a·target - eta subject a·p <= eta for generated profiles, ||a||_1 <= 1.
        nvar = 33
        c_obj = np.zeros(nvar)
        c_obj[:16] = -target
        c_obj[16:32] = target
        c_obj[32] = 1.0
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
            iteration_log.append({"iteration": it, "profile_count": m, "master": "separator_failed", "message": res_sep.message})
            break
        z = res_sep.x
        a = z[:16] - z[16:32]
        eta = z[32]
        target_val = float(np.dot(a, target))
        restricted_margin = target_val - float(eta)
        if restricted_margin <= tol:
            iteration_log.append({"iteration": it, "profile_count": m, "master": "no_restricted_separator", "margin": restricted_margin})
            break
        p_oracle, M, msg = oracle.optimize_float(a, time_limit=10.0)
        if p_oracle is None:
            iteration_log.append({"iteration": it, "profile_count": m, "master": "oracle_failed", "message": msg})
            break
        full_margin = target_val - float(M)
        step = {"iteration": it, "profile_count": m, "restricted_margin": restricted_margin,
                "target_value": target_val, "restricted_eta": float(eta),
                "oracle_max": float(M), "full_margin": full_margin,
                "oracle_profile": list(map(int, p_oracle))}
        if full_margin > 1e-6:
            # Round the functional and validate the integer optimum exactly.  Try a few scales;
            # keep the simplest separating integer functional with positive margin.
            rounded_records = []
            chosen = None
            for scale in [1000.0, 10000.0, 100000.0, 1000000.0]:
                h = [int(round(scale * ai)) for ai in a]
                g = 0
                for v in h:
                    g = math.gcd(g, abs(v))
                if g > 1:
                    h = [v // g for v in h]
                if all(v == 0 for v in h):
                    continue
                exact = oracle.exact_max_integer_coeff(h)
                h_target = float(np.dot(np.array(h, dtype=float), target))
                margin = h_target - (exact["best_value"] if exact["best_value"] is not None else float("inf"))
                rec = {"scale": scale, "integer_coefficients": h,
                       "integer_beta_exact_search": exact["best_value"],
                       "integer_beta_profile": exact["best_profile"],
                       "integer_exact_search_nodes": exact["nodes"],
                       "integer_exact_search_elapsed_sec": exact["elapsed_sec"],
                       "target_value": h_target, "margin": margin}
                rounded_records.append(rec)
                if exact["best_value"] is not None and margin > 1e-5:
                    chosen = rec
                    break
            separation_certificate = {
                "status": "separated_by_face_conditioned_local_hull" if chosen else "float_separation_no_verified_rounded_cut",
                "iteration": it,
                "profile_count": m,
                "float_a": [float(ai) for ai in a],
                "float_target_value": target_val,
                "float_oracle_beta": float(M),
                "float_margin": full_margin,
                "rounded_trials": rounded_records,
                "chosen_integer_cut": chosen,
            }
            step["rounded_cut_status"] = separation_certificate["status"]
            iteration_log.append(step)
            break
        changed = add_profile(p_oracle, f"oracle_iter_{it}")
        step["new_profile"] = bool(changed)
        iteration_log.append(step)
        if not changed:
            duplicate_oracle_steps += 1
            if duplicate_oracle_steps >= 3:
                iteration_log.append({"iteration": it, "profile_count": len(profiles), "master": "stopped_after_duplicate_oracle_profiles"})
                break
        else:
            duplicate_oracle_steps = 0

    status = "unresolved"
    if membership_certificate is not None:
        status = "membership_found"
    if separation_certificate is not None:
        status = separation_certificate["status"]
    return {
        "status": status,
        "target_profile": [float(v) for v in target],
        "exact_feasibility": feasibility,
        "final_profile_count": len(profiles),
        "seed_oracle_log_head": seed_log[:20],
        "iteration_log": iteration_log,
        "membership_certificate": membership_certificate,
        "separation_certificate": separation_certificate,
    }


def global_cut_from_local_h(h: Sequence[int], beta: int, ann_basis: Sequence[int], J_set: set):
    coeffs = []
    for p in range(1, 256):
        coeffs.append(int(h[eval_color(p, ann_basis)]))
    top19 = sorted(coeffs, reverse=True)[:19]
    U = int(sum(top19))
    M = int(max(0, U - int(beta)))
    moved_coeffs = [coeffs[p - 1] - (M if p not in J_set else 0) for p in range(1, 256)]
    return {
        "h_by_color": [int(v) for v in h],
        "beta_face": int(beta),
        "U_top19_global": U,
        "big_M": M,
        "valid_inequality_form": "sum_p h[color(p)] x_p <= beta_face + big_M * sum_{p_notin_J} x_p",
        "moved_lhs_coefficients": moved_coeffs,
        "moved_rhs_beta": int(beta),
        "point_coefficients_h_color": coeffs,
        "top19_coefficients": top19,
    }


def evaluate_cut_on_x(cut: Dict, x: np.ndarray, J_set: set):
    coeffs = np.array(cut["point_coefficients_h_color"], dtype=float)
    outside = np.array([0.0 if (p in J_set) else 1.0 for p in range(1, 256)])
    lhs = float(np.dot(coeffs, x))
    rhs = float(cut["beta_face"] + cut["big_M"] * np.dot(outside, x))
    moved_lhs = float(np.dot(np.array(cut["moved_lhs_coefficients"], dtype=float), x))
    return {"lhs_original_form": lhs, "rhs_original_form": rhs,
            "violation_margin_original_form": lhs - rhs,
            "moved_lhs": moved_lhs, "moved_rhs": float(cut["moved_rhs_beta"]),
            "moved_violation_margin": moved_lhs - float(cut["moved_rhs_beta"]),
            "outside_mass_x": float(np.dot(outside, x))}


def solve_lp_with_generated_cuts(records: Sequence[Dict], cuts: Sequence[Dict], seed: int = 6202):
    """A small feedback test: re-solve the complete Wang LP plus generated cuts.

    This is not a proof; it checks whether the generated cuts only remove the old
    point or also change a generic LP vertex substantially.
    """
    from scipy import sparse
    rows = []
    cols = []
    vals = []
    b = []
    for i, rec in enumerate(records):
        b.append(19 - int(rec["L"]))
        bs = int(rec["point_bitset"])
        while bs:
            bit = bs & -bs
            rows.append(i); cols.append(bit.bit_length() - 1); vals.append(1.0)
            bs ^= bit
    n0 = len(records)
    for k, cut in enumerate(cuts):
        for j, c in enumerate(cut["moved_lhs_coefficients"]):
            if c:
                rows.append(n0 + k); cols.append(j); vals.append(float(c))
        b.append(float(cut["moved_rhs_beta"]))
    A = sparse.csr_matrix((np.array(vals), (np.array(rows), np.array(cols))), shape=(n0 + len(cuts), 255))
    rng = np.random.default_rng(seed)
    c = rng.normal(size=255)
    t0 = time.time()
    res = linprog(c, A_ub=A, b_ub=np.array(b, dtype=float),
                  A_eq=sparse.csr_matrix(np.ones((1, 255))), b_eq=np.array([19.0]),
                  bounds=[(0.0, 1.0)] * 255, method="highs", options={"time_limit": 120})
    info = {"success": bool(res.success), "message": str(res.message), "elapsed_sec": time.time() - t0,
            "cut_count": len(cuts), "objective_seed": seed}
    if res.success:
        xx = np.asarray(res.x, dtype=float)
        rounded = np.rint(xx)
        slacks = np.array(b, dtype=float) - A.dot(xx)
        info.update({
            "objective_value": float(res.fun),
            "sum_x": float(xx.sum()),
            "n_fractional_coordinates": int(np.sum(np.abs(xx - rounded) > 1e-7)),
            "max_round_distance": float(np.max(np.abs(xx - rounded))),
            "generated_cut_slacks": [float(slacks[n0 + k]) for k in range(len(cuts))],
            "generated_cut_tight_count": int(np.sum(np.abs(slacks[n0:n0 + len(cuts)]) < 1e-7)) if cuts else 0,
            "x_nonzero_count_tol_1e-9": int(np.sum(xx > 1e-9)),
            "x_head_nonzero": [(int(i + 1), float(v)) for i, v in enumerate(xx) if v > 1e-9][:80],
        })
    return info


def main():
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    x, J, outside, global_data = load_global_x()
    J_set = set(J)
    print(f"Loaded global fractional x: sum={x.sum():.12f}, |J|={len(J)}, outside={len(outside)}")
    lut, _ = load_lut(LUT_PATH)
    core = CoreQuotient(1)
    records, meta = build_core_constraints(core, lut)
    rec_by_key = {int(r["key8"]): r for r in records}
    maps = selected_maps()
    print(f"Selected {len(maps)} distinct 4D color maps")

    results = []
    generated_cuts = []
    for mi, mp in enumerate(maps):
        ann = [int(v) for v in mp["annihilator_basis"]]
        constraints = build_local_constraints(ann, rec_by_key)
        caps, target = fiber_caps_and_target(ann, x, J)
        oracle = FaceLocalOracle(constraints, caps)
        A, b = local_matrix(constraints)
        local_slacks = b - A.dot(target)
        cap_slacks = np.array(caps, dtype=float) - target
        print(f"Map {mi:02d} {mp['source_label']}#{mp['source_pair_index']}: caps={caps}, min_row_slack={local_slacks.min():.3e}, min_cap_slack={cap_slacks.min():.3e}")
        hull = column_generation(target, oracle, max_iters=100)
        print(f"  status={hull['status']}, profiles={hull['final_profile_count']}")
        cut = None
        cut_eval = None
        sep = hull.get("separation_certificate")
        if sep and sep.get("chosen_integer_cut"):
            chosen = sep["chosen_integer_cut"]
            h = chosen["integer_coefficients"]
            beta = int(chosen["integer_beta_exact_search"])
            cut = global_cut_from_local_h(h, beta, ann, J_set)
            cut_eval = evaluate_cut_on_x(cut, x, J_set)
            cut["source_map_index"] = mi
            cut["source_label"] = mp["source_label"]
            cut["source_pair_index"] = mp["source_pair_index"]
            cut["face_target_margin"] = float(chosen["margin"])
            cut["evaluation_on_saved_x"] = cut_eval
            generated_cuts.append(cut)
            print(f"  generated cut: beta={beta}, U={cut['U_top19_global']}, M={cut['big_M']}, saved_x_margin={cut_eval['violation_margin_original_form']:.6g}")
        elif hull["status"] == "face_local_integer_empty":
            # Valid cut: sum outside >= 1 for any complete local-feasible support.
            cut = {
                "source_map_index": mi,
                "source_label": mp["source_label"],
                "source_pair_index": mp["source_pair_index"],
                "type": "outside_J_at_least_one_due_to_empty_face_local_profile",
                "valid_inequality_form": "sum_{p_notin_J} x_p >= 1",
                "outside_points": outside,
                "evaluation_on_saved_x": {"outside_mass_x": 0.0, "violation_margin_for_outside_ge_1": 1.0},
            }
            generated_cuts.append(cut)
        hist = defaultdict(int)
        for con in constraints:
            hist[f"L{int(con['L'])}_cap{int(con['cap'])}"] += 1
        results.append({
            "map_index": mi,
            "map_source": mp,
            "annihilator_basis": ann,
            "face_fiber_caps": caps,
            "face_fiber_nonzero_colors": [i for i, v in enumerate(caps) if v > 0],
            "target_profile": [float(v) for v in target],
            "target_sum": float(target.sum()),
            "target_vs_face_cap_min_slack": float(cap_slacks.min()),
            "target_min_local_wang_slack": float(local_slacks.min()),
            "target_tight_local_constraints": int(np.sum(np.abs(local_slacks) < 1e-7)),
            "local_constraint_L_cap_hist": dict(sorted(hist.items())),
            "tight_local_constraint_indices_head": [int(i) for i in np.where(np.abs(local_slacks) < 1e-7)[0][:40]],
            "hull_test": hull,
            "generated_global_cut": cut,
        })

    lp_with_cuts = None
    # Re-solve with at most the normal h-cuts; skip empty-face cut translation here if present.
    hcuts = [c for c in generated_cuts if "moved_lhs_coefficients" in c]
    if hcuts:
        print(f"Re-solving complete LP with {len(hcuts)} generated h-cuts")
        lp_with_cuts = solve_lp_with_generated_cuts(records, hcuts)
        print(f"  LP+cuts success={lp_with_cuts['success']} frac={lp_with_cuts.get('n_fractional_coordinates')}")

    out = OUTDIR / "face_conditioned_local_hull_results.json"
    out.write_text(json.dumps({
        "schema": "face_conditioned_local_hull_v1",
        "elapsed_sec": time.time() - t0,
        "meaning": "Face-conditioned 4D local hull tests for the saved analysis global fractional Wang-LP point. Fiber caps are restricted to J=support(x), because any convex representation of x by binary supports must avoid outside coordinates. Generated h-cuts use a big-M outside-J term and are valid for all distinct 19-point supports when the recorded exact local beta is correct.",
        "global_solution_file": str(GLOBAL_PATH),
        "global_solution_sum": float(x.sum()),
        "J_size": len(J),
        "J_points": J,
        "outside_size": len(outside),
        "tested_map_count": len(results),
        "status_counts": dict(sorted({s: sum(1 for r in results if r["hull_test"]["status"] == s) for s in set(r["hull_test"]["status"] for r in results)}.items())),
        "generated_cut_count": len(generated_cuts),
        "generated_cuts_summary": [
            {
                "source_map_index": c.get("source_map_index"),
                "source_label": c.get("source_label"),
                "source_pair_index": c.get("source_pair_index"),
                "beta_face": c.get("beta_face"),
                "U_top19_global": c.get("U_top19_global"),
                "big_M": c.get("big_M"),
                "saved_x_margin": c.get("evaluation_on_saved_x", {}).get("violation_margin_original_form"),
                "face_target_margin": c.get("face_target_margin"),
                "type": c.get("type", "h_color_bigM_cut"),
            }
            for c in generated_cuts
        ],
        "lp_with_generated_hcuts": lp_with_cuts,
        "map_results": results,
    }, indent=2) + "\n")
    print(f"Saved {out}")
    print(f"Elapsed {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
