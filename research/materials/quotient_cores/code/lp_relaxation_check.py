#!/usr/bin/env python3
r"""analysis: LP relaxation check for the unconditional E11 core model.

If the LP relaxation is infeasible, we get a Farkas dual certificate: a set of
nonneg multipliers for the constraints whose weighted sum produces a contradiction
(like 0 >= 1).  This would be a compact, independently verifiable certificate of
infeasibility without needing integer programming proof systems.

Also builds a fresh unconditional separator (no repeat constraint) that learns
both Wang rows and unconditional quotient-rank cuts, to test whether the
unconditional mechanism alone can exclude all E11 rank-19 supports.
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from scipy.sparse import lil_matrix

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient
from fixed_A_saturation import mat_rank_f2
from complete_core_and_transversal import ROOT, build_core_constraints
from quotient_rank_cuts import (
    build_contractions, point_mask_for_q, projection_rank_mod_space, sum_basis,
)
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis

OUTDIR = ROOT / "workspace/data/unconditional_qcuts"


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--source', type=Path,
                    default=ROOT / 'workspace/data/quotient_rank_cuts/core_e11_multiset_quotient_sep_24r_fullstored.json')
    ap.add_argument('--time-limit', type=float, default=120.0)
    ap.add_argument('--out', type=Path, default=OUTDIR / 'lp_relaxation_check.json')
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

    t0 = time.time()
    s = 19
    core = CoreQuotient(1)
    src = json.loads(args.source.read_text())
    T = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2
    lut = load_lut(ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    records, meta = build_core_constraints(core, lut)
    record_by_key = {int(r['key8']): r for r in records}
    contractions = build_contractions(T)
    masks = {q: point_mask_for_q(q) for q in contractions}
    points = list(range(1, 256))

    point_cap = {}
    for p in points:
        key8 = core.key8_from_rows([p])
        key9 = core.key9_from_key8(key8)
        point_cap[p] = max(0, min(s, s - int(lut[key9])))
    repeat_pts = [p for p, c in point_cap.items() if c >= 2]

    # Extract learned constraints
    wang_keys = set()
    qcuts = []
    for r in records:
        if int(r['dim8']) in (1, 2):
            wang_keys.add(int(r['key8']))
    for rnd in src.get('rounds', []):
        for w in rnd.get('learned_wang_rows', []):
            wang_keys.add(int(w['key8']))
        for c in rnd.get('learned_quotient_cuts', []):
            qcuts.append(c)

    print(f"Loaded: {len(wang_keys)} Wang rows, {len(qcuts)} quotient cuts")

    # Build constraint matrix for LP relaxation
    # Model: WITH repeat constraint
    p_index = {p: p - 1 for p in points}
    nx = 255
    nr = len(repeat_pts)
    nvars = nx + nr
    r_index = {p: nx + i for i, p in enumerate(repeat_pts)}

    rows_A = []
    lbs = []
    ubs = []

    def add(coeff, lb=-np.inf, ub=np.inf):
        rows_A.append(coeff)
        lbs.append(lb)
        ubs.append(ub)

    # Sum = 19
    add({p_index[p]: 1 for p in points}, s, s)
    # Repeat encoding
    add({r_index[p]: 1 for p in repeat_pts}, 1, np.inf)
    for p in repeat_pts:
        add({p_index[p]: 1, r_index[p]: -1}, -np.inf, 1)
        add({p_index[p]: 1, r_index[p]: -2}, 0, np.inf)
    # Wang rows
    for key8 in sorted(wang_keys):
        rec = record_by_key[key8]
        cap = s - int(rec['L'])
        pts = subspace_points_from_basis(unpack_basis(key8))
        add({p_index[p]: 1 for p in pts}, -np.inf, cap)
    # Contraction lower bounds
    for q, c in contractions.items():
        rk = int(c['rank'])
        if rk > 0:
            add({p_index[p]: 1 for p in points if ((q & p).bit_count() & 1)}, rk, np.inf)
    # Unconditional quotient cuts
    for c in qcuts:
        q1, q2 = int(c['sources'][0]), int(c['sources'][1])
        target = int(c['target'])
        req = int(c['requirement'])
        rq1 = int(contractions[q1]['rank'])
        rq2 = int(contractions[q2]['rank'])
        source_union = masks[q1] | masks[q2]
        outside_mask = masks[target] & (~source_union) & ((1 << 255) - 1)
        coeff = {}
        for p in points:
            if (outside_mask >> (p - 1)) & 1:
                coeff[p_index[p]] = coeff.get(p_index[p], 0) + 1
            if ((q1 & p).bit_count() & 1):
                coeff[p_index[p]] = coeff.get(p_index[p], 0) + 1
            if ((q2 & p).bit_count() & 1):
                coeff[p_index[p]] = coeff.get(p_index[p], 0) + 1
        rhs = req + rq1 + rq2
        add(coeff, rhs, np.inf)

    # Build sparse matrix
    A = lil_matrix((len(rows_A), nvars), dtype=float)
    for i, coeff in enumerate(rows_A):
        for j, v in coeff.items():
            A[i, j] = v
    A_csr = A.tocsr()

    # Variable bounds (continuous relaxation: x_p in [0, cap_p], r_p in [0, 1])
    lb_vec = np.zeros(nvars)
    ub_vec = np.zeros(nvars)
    for p in points:
        ub_vec[p_index[p]] = point_cap[p]
    for p in repeat_pts:
        ub_vec[r_index[p]] = 1.0

    # Solve LP relaxation
    print(f"\nLP relaxation: {nvars} vars, {len(rows_A)} constraints")
    c_obj = np.zeros(nvars)
    ts = time.time()
    result = linprog(
        c=c_obj,
        A_ub=None, b_ub=None,
        A_eq=None, b_eq=None,
        bounds=list(zip(lb_vec, ub_vec)),
        method='highs',
    )
    # Actually linprog needs standard form. Use milp with integrality=0.
    ts = time.time()
    integrality_lp = np.zeros(nvars, dtype=int)  # all continuous
    res_lp = milp(
        c=c_obj,
        integrality=integrality_lp,
        bounds=Bounds(lb_vec, ub_vec),
        constraints=LinearConstraint(A_csr, np.array(lbs), np.array(ubs)),
        options={'time_limit': float(args.time_limit), 'presolve': True},
    )
    lp_sec = time.time() - ts

    lp_status = {
        "status": int(res_lp.status),
        "message": str(res_lp.message),
        "success": bool(res_lp.success),
        "solve_sec": round(lp_sec, 3),
    }

    if res_lp.x is not None:
        x_vals = res_lp.x[:nx]
        lp_status["x_sum"] = round(float(x_vals.sum()), 6)
        lp_status["x_nonzero"] = int(np.count_nonzero(x_vals > 1e-8))
        lp_status["x_integer_count"] = int(np.count_nonzero(np.abs(x_vals - np.rint(x_vals)) < 1e-8))
        lp_status["x_max"] = round(float(x_vals.max()), 6)
        lp_status["x_fractional_count"] = int(np.count_nonzero(np.abs(x_vals - np.rint(x_vals)) >= 1e-8))
        if nr > 0:
            r_vals = res_lp.x[nx:]
            lp_status["r_sum"] = round(float(r_vals.sum()), 6)
            lp_status["r_max"] = round(float(r_vals.max()), 6)

    print(f"LP relaxation result: status={lp_status['status']} message={lp_status['message']}")
    if 'x_sum' in lp_status:
        print(f"  x_sum={lp_status['x_sum']} nonzero={lp_status['x_nonzero']} "
              f"fractional={lp_status['x_fractional_count']} max={lp_status['x_max']}")
        if nr > 0:
            print(f"  r_sum={lp_status['r_sum']} r_max={lp_status['r_max']}")

    # Also test LP relaxation WITHOUT repeat constraint
    rows_B = []
    lbs_B = []
    ubs_B = []

    def add_b(coeff, lb=-np.inf, ub=np.inf):
        rows_B.append(coeff)
        lbs_B.append(lb)
        ubs_B.append(ub)

    add_b({p_index[p]: 1 for p in points}, s, s)
    for key8 in sorted(wang_keys):
        rec = record_by_key[key8]
        cap = s - int(rec['L'])
        pts = subspace_points_from_basis(unpack_basis(key8))
        add_b({p_index[p]: 1 for p in pts}, -np.inf, cap)
    for q, c in contractions.items():
        rk = int(c['rank'])
        if rk > 0:
            add_b({p_index[p]: 1 for p in points if ((q & p).bit_count() & 1)}, rk, np.inf)
    for c in qcuts:
        q1, q2 = int(c['sources'][0]), int(c['sources'][1])
        target = int(c['target'])
        req = int(c['requirement'])
        rq1 = int(contractions[q1]['rank'])
        rq2 = int(contractions[q2]['rank'])
        source_union = masks[q1] | masks[q2]
        outside_mask = masks[target] & (~source_union) & ((1 << 255) - 1)
        coeff = {}
        for p in points:
            if (outside_mask >> (p - 1)) & 1:
                coeff[p_index[p]] = coeff.get(p_index[p], 0) + 1
            if ((q1 & p).bit_count() & 1):
                coeff[p_index[p]] = coeff.get(p_index[p], 0) + 1
            if ((q2 & p).bit_count() & 1):
                coeff[p_index[p]] = coeff.get(p_index[p], 0) + 1
        rhs = req + rq1 + rq2
        add_b(coeff, rhs, np.inf)

    A_B = lil_matrix((len(rows_B), nx), dtype=float)
    for i, coeff in enumerate(rows_B):
        for j, v in coeff.items():
            A_B[i, j] = v

    ts2 = time.time()
    res_lp2 = milp(
        c=np.zeros(nx),
        integrality=np.zeros(nx, dtype=int),
        bounds=Bounds(lb_vec[:nx], ub_vec[:nx]),
        constraints=LinearConstraint(A_B.tocsr(), np.array(lbs_B), np.array(ubs_B)),
        options={'time_limit': float(args.time_limit), 'presolve': True},
    )
    lp2_sec = time.time() - ts2

    lp2_status = {
        "status": int(res_lp2.status),
        "message": str(res_lp2.message),
        "solve_sec": round(lp2_sec, 3),
    }
    if res_lp2.x is not None:
        x2 = res_lp2.x[:nx]
        lp2_status["x_sum"] = round(float(x2.sum()), 6)
        lp2_status["x_nonzero"] = int(np.count_nonzero(x2 > 1e-8))
        lp2_status["x_max"] = round(float(x2.max()), 6)
        lp2_status["x_fractional_count"] = int(np.count_nonzero(np.abs(x2 - np.rint(x2)) >= 1e-8))
    print(f"\nLP relaxation without repeat: status={lp2_status['status']} message={lp2_status['message']}")
    if 'x_sum' in lp2_status:
        print(f"  x_sum={lp2_status['x_sum']} nonzero={lp2_status['x_nonzero']} "
              f"fractional={lp2_status['x_fractional_count']} max={lp2_status['x_max']}")

    out = {
        "schema": "lp_relaxation_check_v1",
        "field": "F2",
        "core": "E11",
        "rank_s": s,
        "stored_wang_rows": len(wang_keys),
        "stored_quotient_cuts": len(qcuts),
        "lp_with_repeat": lp_status,
        "lp_without_repeat": lp2_status,
        "total_elapsed_sec": round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(f"\nSaved {args.out}")


if __name__ == "__main__":
    main()
