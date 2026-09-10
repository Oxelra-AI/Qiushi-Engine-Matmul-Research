#!/usr/bin/env python3
"""analysis: fixed-n integer pair-count search with PSD testing/separation.

For a fixed orbit count vector n, an averaged actual support has integer
pair-orbit counts m_j and normalized pair moments y_j=m_j/|P_j|.  This script
asks for exact integer m satisfying the already developed linear conditions
(Wang RLT, triangle/Fortet, and block pair totals), then tests the labelled
256x256 moment matrix for PSD.

If a sampled integer m is not PSD, an optional floating square cut from its most
negative eigenvector is added to steer CP-SAT away from that region.  Those cuts
are numerical search instruments only unless later rationalized/certified; a
PSD-passing integer m would be a real second-moment/count witness, still not a
point support.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, List, Tuple

import numpy as np
from scipy import sparse

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import build_core_constraints  # noqa: E402
from rlt_pair_lift import (  # noqa: E402
    LUT_PATH,
    build_lp,
    build_stabilizer,
    compute_pair_orbits,
    compute_point_orbits,
)
from rlt_triangle_integrality import (  # noqa: E402
    build_triangle_constraints,
    dense_rows_to_csr,
    exact_fraction_check,
)
from block_sdp_v2 import build_full_moment_matrix  # noqa: E402

OUT = ROOT / "workspace/data/integer_pair_psd_loop"
SCALE = 1152

DEFAULT_COUNTS = [
    [0, 0, 3, 5, 4, 7],
    [1, 0, 3, 6, 2, 7],
    [1, 0, 4, 5, 2, 7],
]


def parse_counts(text: str | None) -> list[list[int]]:
    if not text:
        return [list(c) for c in DEFAULT_COUNTS]
    out = []
    for block in text.split(";"):
        if not block.strip():
            continue
        vals = [int(x) for x in block.replace(",", " ").split()]
        if len(vals) != 6 or sum(vals) != 19:
            raise ValueError(f"bad count vector {block!r}: {vals}")
        out.append(vals)
    return out


def build_block_lists(pair_ep, K):
    by_block = defaultdict(list)
    for j, (a, b) in enumerate(pair_ep):
        by_block[(int(a), int(b))].append(j)
    return by_block


def add_scaled_substituted_rows(model, m_vars, A, b, n_vec, point_sizes, pair_sizes, K, equality: bool, max_rows: int | None = None):
    added = 0
    for r in range(A.shape[0]):
        if max_rows is not None and added >= max_rows:
            break
        terms = []
        lhs_const = 0
        start, end = A.indptr[r], A.indptr[r + 1]
        for idx, coeff in zip(A.indices[start:end], A.data[start:end]):
            c = int(round(float(coeff)))
            if c == 0:
                continue
            idx = int(idx)
            if idx < K:
                denom = int(point_sizes[idx])
                if SCALE % denom:
                    raise ValueError((idx, denom))
                lhs_const += c * (SCALE // denom) * int(n_vec[idx])
            else:
                j = idx - K
                denom = int(pair_sizes[j])
                if SCALE % denom:
                    raise ValueError((j, denom))
                terms.append(c * (SCALE // denom) * m_vars[j])
        rhs = int(round(float(b[r]) * SCALE)) - lhs_const
        if equality:
            model.Add(sum(terms) == rhs)
        else:
            model.Add(sum(terms) <= rhs)
        added += 1
    return added


def add_block_total_rows(model, m_vars, n_vec, by_block, K):
    count = 0
    for a in range(K):
        target = int(n_vec[a] * (n_vec[a] - 1) // 2)
        model.Add(sum(m_vars[j] for j in by_block[(a, a)]) == target)
        count += 1
    for a in range(K):
        for b in range(a + 1, K):
            target = int(n_vec[a] * n_vec[b])
            model.Add(sum(m_vars[j] for j in by_block[(a, b)]) == target)
            count += 1
    return count


def make_z(n_vec, m_vec, point_sizes, pair_sizes, K, Mpair):
    z = np.zeros(K + Mpair, dtype=float)
    for a in range(K):
        z[a] = n_vec[a] / point_sizes[a]
    for j in range(Mpair):
        z[K + j] = m_vec[j] / pair_sizes[j]
    return z


def quadratic_coefficients(v, n_vec, point_orbits, pair_orb, pair_sizes, K, Mpair):
    """Return const, coeff_m so v^T M v = const + coeff_m dot m."""
    const = float(v[0] * v[0])
    point_sizes = [len(o) for o in point_orbits]
    for a, orb in enumerate(point_orbits):
        x = n_vec[a] / point_sizes[a]
        s = 0.0
        for p in orb:
            p = int(p)
            s += 2.0 * v[0] * v[p] + v[p] * v[p]
        const += x * s
    pair_sum = np.zeros(Mpair, dtype=float)
    for (p, q), j in pair_orb.items():
        pair_sum[j] += 2.0 * v[int(p)] * v[int(q)]
    coeff = np.array([pair_sum[j] / float(pair_sizes[j]) for j in range(Mpair)], dtype=float)
    return const, coeff


def add_numeric_square_cut(model, m_vars, const, coeff, scale, safety=0.0):
    """Add rounded inequality coeff*m + const >= 0 as search cut.

    This is intentionally labelled numerical: rounding is not a proof-producing
    rational certificate.  It is safe as an exploratory branch guide only.
    """
    icoeff = np.rint(coeff * scale).astype(np.int64)
    rhs = int(math.ceil((-const + safety) * scale))
    terms = []
    for j, c in enumerate(icoeff):
        if c:
            terms.append(int(c) * m_vars[j])
    model.Add(sum(terms) >= rhs)
    return {"nonzero_coeffs": int(np.count_nonzero(icoeff)), "rhs": rhs, "scale": int(scale), "max_abs_coeff": int(np.max(np.abs(icoeff))) if icoeff.size else 0}


def solve_fixed_n(n_vec, infra, args):
    from ortools.sat.python import cp_model

    point_orbits = infra["point_orbits"]; pair_ep = infra["pair_ep"]
    point_sizes = infra["point_sizes"]; pair_sizes = infra["pair_sizes"]
    K = infra["K"]; Mpair = infra["Mpair"]
    Aeq = infra["Aeq"]; beq = infra["beq"]; Aub_all = infra["Aub_all"]; bub_all = infra["bub_all"]
    by_block = infra["by_block"]

    model = cp_model.CpModel()
    m = [model.NewIntVar(0, min(int(pair_sizes[j]), 171), f"m_{j}") for j in range(Mpair)]
    model.Add(sum(m) == 171)
    eq_added = add_scaled_substituted_rows(model, m, Aeq, beq, n_vec, point_sizes, pair_sizes, K, True)
    ub_added = add_scaled_substituted_rows(model, m, Aub_all, bub_all, n_vec, point_sizes, pair_sizes, K, False)
    block_added = add_block_total_rows(model, m, n_vec, by_block, K)

    cuts = []
    rounds = []
    found_psd = None
    for it in range(args.max_iters):
        # Change deterministic objective each iteration to sample different integer corners.
        model.Minimize(sum(((j * 1000003 + args.seed + 17 * it) % 1009) * m[j] for j in range(Mpair)))
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(args.per_solve_time)
        solver.parameters.num_search_workers = int(args.workers)
        solver.parameters.random_seed = int(args.seed + it)
        ts = time.time(); st = solver.Solve(model); solve_sec = time.time() - ts
        status = solver.StatusName(st)
        rec = {"iter": it, "status": status, "solve_sec": round(solve_sec, 3), "active_numeric_psd_cuts": len(cuts)}
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            rounds.append(rec)
            break
        m_vec = [int(solver.Value(v)) for v in m]
        z = make_z(n_vec, m_vec, point_sizes, pair_sizes, K, Mpair)
        Mfull = build_full_moment_matrix(z, infra["pt_orb"], infra["pair_orb"], K)
        eigvals, eigvecs = np.linalg.eigh(Mfull)
        min_eig = float(eigvals[0])
        exact_chk = exact_fraction_check(Aeq, beq, Aub_all, bub_all, n_vec, m_vec, point_sizes, [int(x) for x in pair_sizes], K, Mpair)
        rec.update({
            "min_eig": min_eig,
            "neg_eigs_1e_8": int(np.sum(eigvals < -1e-8)),
            "m_nonzero_orbits": int(sum(1 for v in m_vec if v)),
            "exact_fraction_feasible": exact_chk.get("is_exact_feasible"),
            "exact_max_ub_violation": exact_chk.get("max_ub_violation"),
            "m_vec": m_vec,
        })
        rounds.append(rec)
        print(f"      iter {it}: status={status} min_eig={min_eig:.6g} neg={rec['neg_eigs_1e_8']} nonzero_m={rec['m_nonzero_orbits']} solve={solve_sec:.2f}s", flush=True)
        if min_eig >= -float(args.psd_tol):
            found_psd = {"iter": it, "m_vec": m_vec, "min_eig": min_eig, "z": z.tolist()}
            break
        # Add a numerical square cut from the most negative eigenvector if violation is not merely roundoff.
        if min_eig < -float(args.cut_threshold):
            const, coeff = quadratic_coefficients(eigvecs[:, 0], n_vec, point_orbits, infra["pair_orb"], pair_sizes, K, Mpair)
            value = float(const + np.dot(coeff, np.array(m_vec, dtype=float)))
            cut_info = add_numeric_square_cut(model, m, const, coeff, args.cut_scale)
            cut_info.update({"iter": it, "source_min_eig": min_eig, "source_quadratic_value": value, "note": "floating rounded PSD separation cut; search-only"})
            cuts.append(cut_info)
        else:
            # Exclude exact m vector and continue sampling if violation too small for a useful numeric cut.
            model.Add(sum(m[j] for j, val in enumerate(m_vec) if val) <= sum(1 for val in m_vec if val) * 171 - 1)
            cuts.append({"iter": it, "kind": "weak_no_good_placeholder", "note": "min eigenvalue too close to zero for square cut"})
    return {
        "n": list(map(int, n_vec)),
        "eq_rows_added": eq_added,
        "ub_rows_added": ub_added,
        "block_total_rows_added": block_added,
        "numeric_square_cuts_added": len([c for c in cuts if c.get("source_min_eig") is not None]),
        "cuts": cuts,
        "found_psd_integer_pair_witness": found_psd is not None,
        "psd_integer_pair_witness": found_psd,
        "rounds": rounds,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--counts", type=str, default=None)
    ap.add_argument("--max-iters", type=int, default=8)
    ap.add_argument("--per-solve-time", type=float, default=60.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=700170)
    ap.add_argument("--psd-tol", type=float, default=1e-8)
    ap.add_argument("--cut-threshold", type=float, default=1e-6)
    ap.add_argument("--cut-scale", type=int, default=1000000)
    ap.add_argument("--out", type=Path, default=OUT / "integer_pair_psd_loop.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    print("analysis: fixed-n integer pair counts + PSD loop", flush=True)
    counts = parse_counts(args.counts)
    print(f"  counts={counts}", flush=True)

    perms = build_stabilizer()
    pt_orb, point_orbits = compute_point_orbits(perms)
    pair_orb, pair_sizes, pair_ep, Mpair = compute_pair_orbits(perms, pt_orb)
    K = len(point_orbits); N = K + Mpair; point_sizes = [len(o) for o in point_orbits]
    lut, lut_meta = load_lut(LUT_PATH)
    records, wmeta = build_core_constraints(CoreQuotient(1), lut)
    eq_A, eq_b, ub_A, ub_b, K2, M2, N2, n_aj = build_lp(records, pt_orb, point_orbits, pair_orb, Mpair, pair_ep)
    assert (K2, M2, N2) == (K, Mpair, N)
    Aeq = dense_rows_to_csr(eq_A, N); beq = np.array(eq_b, dtype=float)
    Aub = dense_rows_to_csr(ub_A, N); bub = np.array(ub_b, dtype=float)
    Atri, btri, tri_meta = build_triangle_constraints(pt_orb, pair_orb, K, Mpair)
    Aub_all = sparse.vstack([Aub, Atri], format="csr"); bub_all = np.concatenate([bub, btri])
    infra = {
        "pt_orb": pt_orb,
        "point_orbits": point_orbits,
        "point_sizes": point_sizes,
        "pair_orb": pair_orb,
        "pair_sizes": [int(x) for x in pair_sizes],
        "pair_ep": pair_ep,
        "K": K,
        "Mpair": Mpair,
        "Aeq": Aeq,
        "beq": beq,
        "Aub_all": Aub_all,
        "bub_all": bub_all,
        "by_block": build_block_lists(pair_ep, K),
    }
    print(f"  built infra: K={K}, M={Mpair}, eq={Aeq.shape[0]}, ub={Aub_all.shape[0]}, elapsed={time.time()-t0:.1f}s", flush=True)

    results = []
    for n in counts:
        print(f"  solve n={n}", flush=True)
        rs = solve_fixed_n(n, infra, args)
        results.append(rs)
        print(json.dumps({"n": n, "found_psd_integer_pair_witness": rs["found_psd_integer_pair_witness"], "iters": len(rs["rounds"]), "last": rs["rounds"][-1] if rs["rounds"] else None}, sort_keys=True)[:3000], flush=True)

    payload = {
        "schema": "fixed_n_integer_pair_psd_loop_v1",
        "meaning": "Exact integer pair-count search under fixed n, block totals, Wang RLT, and triangles, followed by PSD testing. Added square cuts are floating search cuts only; infeasibility after them is not a proof. A PSD integer-pair witness is still not an actual support.",
        "parameters": {
            "counts": counts,
            "max_iters": args.max_iters,
            "per_solve_time": args.per_solve_time,
            "workers": args.workers,
            "seed": args.seed,
            "psd_tol": args.psd_tol,
            "cut_threshold": args.cut_threshold,
            "cut_scale": args.cut_scale,
        },
        "point_orbit_sizes": point_sizes,
        "pair_orbit_count": int(Mpair),
        "linear_model": {"n_eq": int(Aeq.shape[0]), "n_ub": int(Aub_all.shape[0]), "triangle_rows": int(Atri.shape[0])},
        "lut_coverage_ok": lut_meta.get("coverage_ok"),
        "results": results,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(args.out),
        "witness_counts": [r["n"] for r in results if r["found_psd_integer_pair_witness"]],
        "elapsed_sec": payload["elapsed_sec"],
    }, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
