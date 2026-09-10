#!/usr/bin/env python3
r"""analysis: Joint integer hull analysis for the E11 core distinct branch.

For pairs of dim-5 violating subspaces that share a dim-4 primal intersection,
the dual span F has dimension 4 in (F_2^8)*.  The 255 nonzero points partition
into 16 color fibers under evaluation on F (15 in F^perp, 16 in each nonzero
fiber).  All nonzero subspaces E <= F (66 total) induce a Wang constraint on the
color counts.  This script builds the local 16-variable LP relaxation and
compares it with the integer hull to detect rounding/Gomory cuts that are
invisible to the original row-by-row LP but valid for the IP.

The script also builds the full global compressed LP and tests whether its
fractional optimum projects outside any local integer hull.
"""
from __future__ import annotations

import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np
from scipy.optimize import linprog

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from wang_capacity_lazy import (
    in_rowspace,
    pack_basis,
    rref_basis,
    rref_key,
    subspace_points_from_basis,
    unpack_basis,
)

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/joint_hull"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"

BASE_SUPPORT = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]

# ── GF(2) linear algebra helpers ──────────────────────────────────────
def gf2_rank(rows: Sequence[int], n: int = 8) -> int:
    pivots = []
    working = list(rows)
    for bit in range(n - 1, -1, -1):
        found = False
        for i in range(len(pivots), len(working)):
            if (working[i] >> bit) & 1:
                working[len(pivots)], working[i] = working[i], working[len(pivots)]
                for j in range(len(working)):
                    if j != len(pivots) and (working[j] >> bit) & 1:
                        working[j] ^= working[len(pivots)]
                pivots.append(bit)
                found = True
                break
        if not found:
            continue
    return len(pivots)


def gf2_intersection_basis(b1: Sequence[int], b2: Sequence[int], n: int = 8) -> List[int]:
    """Basis of intersection of two GF(2) subspaces given by bases."""
    s1 = set(subspace_points_from_basis(list(b1)))
    s2 = set(subspace_points_from_basis(list(b2)))
    inter_pts = sorted(s1 & s2)
    if not inter_pts:
        return []
    return list(rref_basis(inter_pts, n=n))


def subspace_dim(basis: Sequence[int], n: int = 8) -> int:
    return gf2_rank(basis, n)


def eval_on_dual_basis(p: int, dual_basis: Sequence[int]) -> int:
    """Evaluate point p on a dual basis (list of functionals), returning color in Z."""
    c = 0
    for i, q in enumerate(dual_basis):
        if bin(p & q).count('1') % 2:
            c |= 1 << i
    return c


def enumerate_gf2_subspaces(dim: int) -> List[Tuple[int, ...]]:
    """Enumerate all nonzero subspaces of GF(2)^dim as sorted tuples of basis vectors."""
    if dim == 0:
        return []
    points = list(range(1, 1 << dim))
    result = []
    for size in range(1, dim + 1):
        seen = set()
        for combo in combinations(points, size):
            b = tuple(rref_basis(list(combo), n=dim))
            if len(b) == size and b not in seen:
                seen.add(b)
                result.append(b)
    return result


# ── Main analysis ─────────────────────────────────────────────────────
def main() -> None:
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)

    # Load LUT and build core
    lut, _ = load_lut(LUT_PATH)
    core = CoreQuotient(1)

    # Build complete core records (import from analysis)
    from complete_core_and_transversal import build_core_constraints
    records, meta = build_core_constraints(core, lut)
    rec_by_key = {int(r["key8"]): r for r in records}
    print(f"Loaded {len(records)} core records in {time.time()-t0:.1f}s")

    # Extract base near-miss violations
    support_bits = 0
    for p in BASE_SUPPORT:
        support_bits |= 1 << (p - 1)

    violations = []
    for rec in records:
        L = int(rec["L"])
        cap = 19 - L
        occ = bin(int(rec["point_bitset"]) & support_bits).count('1')
        if occ > cap:
            violations.append({
                "key8": int(rec["key8"]),
                "dim8": int(rec["dim8"]),
                "L": L,
                "cap": cap,
                "occ": occ,
                "basis8": list(unpack_basis(int(rec["key8"]))),
            })

    print(f"Base near-miss: {len(violations)} violations")
    dim5_viols = [v for v in violations if v["dim8"] == 5]
    dim6_viols = [v for v in violations if v["dim8"] == 6]
    print(f"  dim5: {len(dim5_viols)}, dim6: {len(dim6_viols)}")

    # Compute pairwise intersections of dim-5 violations
    pair_results = []
    for i, j in combinations(range(len(dim5_viols)), 2):
        v1, v2 = dim5_viols[i], dim5_viols[j]
        inter = gf2_intersection_basis(v1["basis8"], v2["basis8"])
        inter_dim = len(inter)
        pair_results.append({
            "i": i, "j": j,
            "key8_i": v1["key8"], "key8_j": v2["key8"],
            "intersection_dim": inter_dim,
            "intersection_basis": inter,
        })
        print(f"  dim5 pair ({i},{j}): intersection dim = {inter_dim}")

    # Also check dim-6 pairs
    for i, j in combinations(range(len(dim6_viols)), 2):
        v1, v2 = dim6_viols[i], dim6_viols[j]
        inter = gf2_intersection_basis(v1["basis8"], v2["basis8"])
        inter_dim = len(inter)
        print(f"  dim6 pair ({i},{j}): intersection dim = {len(inter)}")

    # Select pairs with dim-4 intersection for the joint hull analysis
    good_pairs = [p for p in pair_results if p["intersection_dim"] == 4]
    print(f"\nGood pairs (dim-4 intersection): {len(good_pairs)}")

    # If no dim5-dim5 pairs, try dim5-dim6 or dim6-dim6
    if not good_pairs:
        # Try dim5-dim6 pairs
        for i in range(len(dim5_viols)):
            for j in range(len(dim6_viols)):
                v1, v2 = dim5_viols[i], dim6_viols[j]
                inter = gf2_intersection_basis(v1["basis8"], v2["basis8"])
                if len(inter) == 4:
                    good_pairs.append({
                        "i": f"d5_{i}", "j": f"d6_{j}",
                        "key8_i": v1["key8"], "key8_j": v2["key8"],
                        "intersection_dim": 4,
                        "intersection_basis": inter,
                        "type": "dim5-dim6",
                    })
        print(f"After dim5-dim6 pairs: {len(good_pairs)} good pairs")

    # For the first good pair (or all), build the local analysis
    hull_results = []
    for pidx, pair in enumerate(good_pairs[:5]):  # limit to 5 pairs
        inter_basis = pair["intersection_basis"]
        inter_dim = pair["intersection_dim"]
        assert inter_dim == 4, f"Expected dim 4, got {inter_dim}"

        # The joint subspace in the dual: F = (intersection)^perp has dim 4
        # Build a dual basis for F (4 functionals that vanish on the intersection)
        # The intersection has basis vectors in F_2^8. F^perp is the 4D primal intersection.
        # F itself (the dual space) has a basis of 4 functionals.

        # Compute dual basis: find 4 independent 8-bit vectors q such that
        # q . b = 0 for all b in inter_basis (dot product over F_2)
        # These q's are the dual basis of (F_2^8 / intersection)^* = annihilator of intersection

        # Find the annihilator of the intersection
        # A vector q annihilates inter_basis iff bin(q & b).count('1') % 2 == 0 for all b
        ann_basis = []
        for q in range(1, 256):
            if all(bin(q & b).count('1') % 2 == 0 for b in inter_basis):
                ann_basis.append(q)
        ann_basis = list(rref_basis(ann_basis, n=8))
        assert len(ann_basis) == 4, f"Expected 4D annihilator, got {len(ann_basis)}"

        # Now ann_basis is the dual basis for F
        # Color of point p: c = eval_on_dual_basis(p, ann_basis) in {0,...,15}
        # Fiber v: all points p with color v

        # Compute fiber partition
        fibers: Dict[int, List[int]] = defaultdict(list)
        for p in range(1, 256):
            c = eval_on_dual_basis(p, ann_basis)
            fibers[c].append(p)

        # Verify fiber sizes
        assert len(fibers[0]) == 15, f"Zero fiber has {len(fibers[0])} points"
        for v in range(1, 16):
            assert len(fibers[v]) == 16, f"Fiber {v} has {len(fibers[v])} points"

        # Color profile of the near-miss
        color_profile = [0] * 16
        for p in BASE_SUPPORT:
            c = eval_on_dual_basis(p, ann_basis)
            color_profile[c] += 1
        print(f"\nPair {pidx}: color profile = {color_profile}, sum = {sum(color_profile)}")

        # Enumerate all nonzero subspaces of F_2^4 (the dual quotient)
        # For each, find the corresponding primal subspace and its Wang bound
        local_subspaces = enumerate_gf2_subspaces(4)
        print(f"  {len(local_subspaces)} nonzero subspaces of F_2^4")

        # For each subspace E of the dual (F_2^4), the annihilator in F_2^4 is E_perp.
        # The primal subspace is {p: eval(p) in E_perp} = {p: q(p)=0 for all q in E_mapped}
        # where E_mapped lifts E back through ann_basis.

        local_constraints = []
        for e_basis in local_subspaces:
            e_dim = len(e_basis)
            # Annihilator of E in F_2^4
            e_perp_vecs = []
            for v in range(1, 16):
                if all(bin(v & e).count('1') % 2 == 0 for e in e_basis):
                    e_perp_vecs.append(v)
            e_perp_basis = list(rref_basis(e_perp_vecs, n=4)) if e_perp_vecs else []
            # The sum of c_v for v in E_perp (including 0 since the zero fiber is always in the perp)
            perp_colors = set()
            perp_colors.add(0)  # zero fiber is always in the annihilator
            for v in range(1, 16):
                if all(bin(v & e).count('1') % 2 == 0 for e in e_basis):
                    perp_colors.add(v)

            # The primal subspace: lift E through the dual basis
            lifted_E = []
            for e in e_basis:
                q = 0
                for k in range(4):
                    if (e >> k) & 1:
                        q ^= ann_basis[k]
                lifted_E.append(q)
            # The primal subspace V = annihilator of lifted_E in F_2^8
            primal_pts = []
            for p in range(1, 256):
                if all(bin(p & q).count('1') % 2 == 0 for q in lifted_E):
                    primal_pts.append(p)
            primal_basis = list(rref_basis(primal_pts, n=8))
            primal_dim = len(primal_basis)

            # Look up the Wang bound for this primal subspace
            key8 = pack_basis(rref_basis(primal_pts, n=8))
            if key8 in rec_by_key:
                L_val = int(rec_by_key[key8]["L"])
            else:
                # Should always be found in the complete table
                L_val = 0
            cap = 19 - L_val

            # The constraint: sum_{v in perp_colors} c_v <= cap
            local_constraints.append({
                "e_basis": list(e_basis),
                "e_dim": e_dim,
                "perp_colors": sorted(perp_colors),
                "primal_dim": primal_dim,
                "L": L_val,
                "cap": cap,
                "near_miss_lhs": sum(color_profile[v] for v in perp_colors),
            })

        # How many local constraints are violated by the near-miss?
        local_viols = [c for c in local_constraints if c["near_miss_lhs"] > c["cap"]]
        print(f"  Local constraints: {len(local_constraints)}, violated by near-miss: {len(local_viols)}")

        # ── Build local LP and IP ─────────────────────────────
        # 16 variables c_0, c_1, ..., c_15
        # Constraints:
        #   sum c_v = 19
        #   c_0 <= 15 (zero fiber capacity)
        #   c_v <= 16 for v != 0 (nonzero fiber capacity)
        #   For each local constraint: sum_{v in perp_colors} c_v <= cap
        #   c_v >= 0

        n_vars = 16
        n_constraints = len(local_constraints) + 1 + 16  # Wang + sum + bounds

        # Build A_ub, b_ub for inequality constraints
        A_ub_rows = []
        b_ub_vals = []

        # Wang constraints
        for lc in local_constraints:
            row = [0.0] * n_vars
            for v in lc["perp_colors"]:
                row[v] = 1.0
            A_ub_rows.append(row)
            b_ub_vals.append(float(lc["cap"]))

        # Upper bound constraints (c_0 <= 15, c_v <= 16 for v > 0)
        for v in range(n_vars):
            row = [0.0] * n_vars
            row[v] = 1.0
            A_ub_rows.append(row)
            b_ub_vals.append(15.0 if v == 0 else 16.0)

        A_ub = np.array(A_ub_rows)
        b_ub = np.array(b_ub_vals)

        # Equality constraint: sum c_v = 19
        A_eq = np.ones((1, n_vars))
        b_eq = np.array([19.0])

        # Bounds: 0 <= c_v
        bounds = [(0, None)] * n_vars

        # Solve LP for several objectives to find fractional vertices
        fractional_found = False
        lp_results = []

        # Objective 1: maximize c_0 (push points into zero fiber)
        for obj_idx in range(n_vars):
            c_obj = [0.0] * n_vars
            c_obj[obj_idx] = -1.0  # maximize c_{obj_idx}
            res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                         bounds=bounds, method='highs')
            if res.success:
                x_opt = res.x
                is_integral = all(abs(x_opt[v] - round(x_opt[v])) < 1e-6 for v in range(n_vars))
                lp_obj = -res.fun
                if not is_integral:
                    fractional_found = True
                lp_results.append({
                    "objective": f"max_c_{obj_idx}",
                    "optimal_value": round(lp_obj, 6),
                    "solution": [round(x, 6) for x in x_opt],
                    "is_integral": is_integral,
                })
            else:
                lp_results.append({
                    "objective": f"max_c_{obj_idx}",
                    "status": res.message,
                })

        # Also try: maximize a direction that pushes toward the near-miss violation
        # (max sum of c_v for violated constraint's perp_colors)
        for vi, lc in enumerate(local_viols[:3]):
            c_obj = [0.0] * n_vars
            for v in lc["perp_colors"]:
                c_obj[v] = -1.0
            res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                         bounds=bounds, method='highs')
            if res.success:
                x_opt = res.x
                is_integral = all(abs(x_opt[v] - round(x_opt[v])) < 1e-6 for v in range(n_vars))
                lp_results.append({
                    "objective": f"max_violated_perp_{vi}",
                    "optimal_value": round(-res.fun, 6),
                    "cap": lc["cap"],
                    "solution": [round(x, 6) for x in x_opt],
                    "is_integral": is_integral,
                })

        # Check: is the near-miss profile feasible for the LOCAL LP?
        c_nm = np.array(color_profile, dtype=float)
        nm_feasible_lp = True
        nm_violations_local = []
        for idx, lc in enumerate(local_constraints):
            lhs = sum(c_nm[v] for v in lc["perp_colors"])
            if lhs > lc["cap"] + 1e-9:
                nm_feasible_lp = False
                nm_violations_local.append({
                    "constraint_idx": idx,
                    "lhs": int(lhs),
                    "cap": lc["cap"],
                    "excess": int(lhs - lc["cap"]),
                })

        # Try to find integer feasible points near the boundary
        # Enumerate by solving IP for various objectives
        try:
            from scipy.optimize import milp, LinearConstraint, Bounds as ScBounds

            ip_results = []
            for obj_idx in range(min(n_vars, 4)):
                c_obj = np.zeros(n_vars)
                c_obj[obj_idx] = -1.0
                integrality = np.ones(n_vars)
                constraints_list = []
                if A_ub.shape[0] > 0:
                    constraints_list.append(LinearConstraint(A_ub, -np.inf, b_ub))
                constraints_list.append(LinearConstraint(A_eq, b_eq, b_eq))
                ip_bounds = ScBounds(lb=0, ub=np.array([15.0] + [16.0]*15))
                res_ip = milp(c_obj, constraints=constraints_list, integrality=integrality,
                             bounds=ip_bounds)
                if res_ip.success:
                    ip_results.append({
                        "objective": f"max_c_{obj_idx}",
                        "optimal_value": round(-res_ip.fun, 6),
                        "solution": [int(round(x)) for x in res_ip.x],
                    })
                else:
                    ip_results.append({
                        "objective": f"max_c_{obj_idx}",
                        "status": str(res_ip.message),
                    })

            # Compare LP vs IP
            gap_found = False
            for lp_r, ip_r in zip(lp_results[:4], ip_results):
                if "optimal_value" in lp_r and "optimal_value" in ip_r:
                    gap = abs(lp_r["optimal_value"] - ip_r["optimal_value"])
                    if gap > 0.01:
                        gap_found = True
                        print(f"  INTEGRALITY GAP: {lp_r['objective']}: LP={lp_r['optimal_value']}, IP={ip_r['optimal_value']}, gap={gap:.4f}")

        except ImportError:
            ip_results = [{"status": "milp not available"}]
            gap_found = False

        hull_results.append({
            "pair_index": pidx,
            "pair_keys": [pair.get("key8_i"), pair.get("key8_j")],
            "intersection_basis": inter_basis,
            "annihilator_basis": ann_basis,
            "near_miss_color_profile": color_profile,
            "near_miss_feasible_local_lp": nm_feasible_lp,
            "near_miss_local_violations": nm_violations_local,
            "local_constraint_count": len(local_constraints),
            "local_violated_by_near_miss": len(local_viols),
            "fractional_vertex_found": fractional_found,
            "lp_results_head": lp_results[:6],
            "ip_results": ip_results if 'ip_results' in dir() else [],
            "integrality_gap_detected": gap_found if 'gap_found' in dir() else None,
        })

    # Save results
    result = {
        "schema": "joint_integer_hull_v1",
        "elapsed_sec": round(time.time() - t0, 3),
        "base_support": BASE_SUPPORT,
        "violation_count": len(violations),
        "dim5_violation_count": len(dim5_viols),
        "dim6_violation_count": len(dim6_viols),
        "pair_intersection_results": pair_results,
        "good_pair_count": len(good_pairs),
        "hull_analyses": hull_results,
    }
    out = OUTDIR / "joint_integer_hull_analysis.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=False) + "\n")
    print(f"\nSaved: {out}")
    print(f"Total elapsed: {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
