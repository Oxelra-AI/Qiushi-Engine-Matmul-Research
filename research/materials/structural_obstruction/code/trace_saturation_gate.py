#!/usr/bin/env python3
r"""
analysis: support-level gate for the corrected saturated-contraction trace layer.

The corrected trace rows from earlier analysis are only the diagonal part of a
stronger algebraic consequence of a tight contraction.  This script measures
whether tight invertible contractions are forced at rank 19 in the three
codimension-one F2 quotient cores.

For a core tensor T_core in F2^8 \otimes F2^9 \otimes F2^9 and q in (F2^8)^*,
let M(q) be the 9x9 contraction matrix.  If rank M(q)=9, every rank-one CPD
support A={a_s} must have

    |I_q| = #{s : <q,a_s>=1} >= 9.

Write nu(a)=#{invertible q : <q,a>=1}.  Then

    sum_s nu(a_s) = sum_{q invertible} |I_q|,

and with 72 invertible q in each quotient core,

    number of saturated q (|I_q|=9) >= 72 - (sum_s nu(a_s)-648).

The script computes nu exactly, then solves Wang-occupation + contraction-rank
support problems lazily to decide whether a rank-19 Wang-admissible support can
avoid all saturated invertible q.  Feasible no-saturation supports mean the
orthogonality/trace layer is not support-forced; infeasibility means every
surviving support has at least one tight contraction before B/C variables are
considered.

This is support-level evidence only.  It does not solve B/C rank-one completion
and does not prove a tensor-rank lower bound without complete coverage plus
certificates.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, Optional, Sequence

import numpy as np

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/trace_saturation_gate"

SCRIPTS_A01 = Path("scripts")
SCRIPTS_A02 = Path("scripts")
for P in (SCRIPTS_A01, SCRIPTS_A02):
    if str(P) not in sys.path:
        sys.path.insert(0, str(P))

from wang_capacity_lazy import pack_basis, unpack_basis, subspace_points_from_basis  # noqa: E402
from wang_capacity_orbit_closed import extension_keys  # noqa: E402
from core_capacity_from_wang_lut import CoreQuotient  # noqa: E402

CORES = {
    "E11": {"pivot_mask": 1, "label": "rank-1 quotient E11"},
    "E12_E21": {"pivot_mask": 10, "label": "rank-2 quotient E12+E21"},
    "H3": {"pivot_mask": 84, "label": "rank-3 quotient E13+E22+E31"},
}


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def bit_dot(a: int, q: int) -> int:
    return (int(a) & int(q)).bit_count() & 1


def mask_to_points(mask: int) -> list[int]:
    pts: list[int] = []
    x = int(mask)
    while x:
        lb = x & -x
        pts.append(lb.bit_length())  # bit p-1 represents nonzero point p
        x ^= lb
    return pts


def pts_to_mask(pts: Iterable[int]) -> int:
    out = 0
    for p in pts:
        if int(p):
            out |= 1 << (int(p) - 1)
    return out


def enumerate_subspace_keys(n: int = 8) -> list[int]:
    levels = {0: {pack_basis(tuple())}}
    all_keys = set(levels[0])
    for d in range(n):
        nxt = set()
        for key in levels[d]:
            for ekey in extension_keys(unpack_basis(key), n=n):
                if (int(ekey) & 0xF) == d + 1:
                    nxt.add(int(ekey))
        levels[d + 1] = nxt
        all_keys.update(nxt)
    return sorted(all_keys)


def load_lut(path: Path) -> tuple[dict[int, int], dict]:
    with path.open("rb") as f:
        payload = pickle.load(f)
    return payload["lut"], payload.get("meta", {})


def build_or_load_core_cache(
    core_name: str,
    pivot_mask: int,
    rank_s: int,
    lut: dict[int, int],
    cache_dir: Path,
    rebuild: bool = False,
) -> dict:
    cache_dir.mkdir(parents=True, exist_ok=True)
    path = cache_dir / f"wang_cache_{core_name}_s{rank_s}.pkl"
    if path.exists() and not rebuild:
        with path.open("rb") as f:
            cache = pickle.load(f)
        if cache.get("rank_s") == rank_s and cache.get("pivot_mask") == pivot_mask:
            return cache

    core = CoreQuotient(pivot_mask)
    keys8 = enumerate_subspace_keys(8)
    masks: list[int] = []
    caps: list[int] = []
    Ls: list[int] = []
    dims: list[int] = []
    for key8 in keys8:
        key9 = core.key9_from_key8(int(key8))
        L = int(lut[key9])
        cap = int(rank_s - L)
        masks.append(pts_to_mask(subspace_points_from_basis(unpack_basis(int(key8)))))
        caps.append(cap)
        Ls.append(L)
        dims.append(int(key8) & 0xF)
    cache = {
        "schema": "core_wang_cache_v1",
        "core_name": core_name,
        "pivot_mask": int(pivot_mask),
        "rank_s": int(rank_s),
        "keys8": [int(k) for k in keys8],
        "masks": masks,
        "caps": caps,
        "Ls": Ls,
        "dims": dims,
        "stats": {
            "subspace_count": len(keys8),
            "dim_counts": {str(k): int(v) for k, v in sorted(Counter(dims).items())},
            "L_counts": {str(k): int(v) for k, v in sorted(Counter(Ls).items())},
            "cap_counts": {str(k): int(v) for k, v in sorted(Counter(caps).items())},
        },
    }
    with path.open("wb") as f:
        pickle.dump(cache, f, protocol=pickle.HIGHEST_PROTOCOL)
    path.with_suffix(".summary.json").write_text(
        json.dumps({k: v for k, v in cache.items() if k not in ("keys8", "masks", "caps", "Ls", "dims")}, indent=2, sort_keys=True) + "\n"
    )
    return cache


def build_matmul_tensor_f2() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a = 3 * i + j
                b = 3 * j + k
                c = 3 * i + k
                T[a, b, c] = 1
    return T


def quotient_core_from_mask(mask: int) -> tuple[np.ndarray, dict]:
    T = build_matmul_tensor_f2()
    pivot = int(mask).bit_length() - 1
    free_bits = int(mask) ^ (1 << pivot)
    folded = T.copy()
    for i in range(9):
        if (free_bits >> i) & 1:
            folded[i] ^= T[pivot]
    folded[pivot] = 0
    keep = [i for i in range(9) if i != pivot]
    return folded[keep].astype(np.uint8), {"pivot": pivot, "free_bits": [i for i in range(9) if (free_bits >> i) & 1], "keep": keep}


def mat_rank_f2(M: np.ndarray) -> int:
    A = np.asarray(M, dtype=np.uint8).copy() & 1
    m, n = A.shape
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if int(A[i, c]):
                piv = i
                break
        if piv is None:
            continue
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for i in range(m):
            if i != r and int(A[i, c]):
                A[i] ^= A[r]
        r += 1
        if r == m:
            break
    return int(r)


def contraction_matrix(T_core: np.ndarray, q: int) -> np.ndarray:
    M = np.zeros((T_core.shape[1], T_core.shape[2]), dtype=np.uint8)
    for a in range(T_core.shape[0]):
        if (int(q) >> a) & 1:
            M ^= T_core[a]
    return M


def contraction_ranks(T_core: np.ndarray) -> dict[int, int]:
    return {q: mat_rank_f2(contraction_matrix(T_core, q)) for q in range(1, 1 << T_core.shape[0])}


def nu_values(inv_qs: Sequence[int], npoints: int = 255) -> dict[int, int]:
    return {p: int(sum(bit_dot(p, q) for q in inv_qs)) for p in range(1, npoints + 1)}


def support_from_solution(sol: dict[int, int]) -> list[int]:
    out: list[int] = []
    for p, c in sorted(sol.items()):
        out.extend([int(p)] * int(c))
    return out


def support_stats(sol: dict[int, int], c_ranks: dict[int, int], inv_qs: Sequence[int], nu: dict[int, int]) -> dict:
    ms = support_from_solution(sol)
    hit_counts: dict[int, int] = {}
    by_rank: dict[int, Counter] = {3: Counter(), 6: Counter(), 9: Counter()}
    tight_by_rank = Counter()
    below_rank = []
    for q, rk in sorted(c_ranks.items()):
        h = sum(bit_dot(a, q) for a in ms)
        hit_counts[q] = h
        if rk in by_rank:
            by_rank[rk][h] += 1
            if h == rk:
                tight_by_rank[rk] += 1
            if h < rk:
                below_rank.append({"q": int(q), "rank": int(rk), "hits": int(h)})
    sumnu = sum(int(nu[p]) * int(c) for p, c in sol.items())
    inv_hits = [hit_counts[q] for q in inv_qs]
    return {
        "support_size": len(sol),
        "total_multiplicity": len(ms),
        "max_multiplicity": max(sol.values()) if sol else 0,
        "sum_nu": int(sumnu),
        "rank9_defect_total": int(sumnu - 9 * len(inv_qs)),
        "rank9_saturated_count": int(sum(1 for h in inv_hits if h == 9)),
        "rank9_hit_histogram": {str(k): int(v) for k, v in sorted(Counter(inv_hits).items())},
        "hit_histogram_by_contraction_rank": {str(rk): {str(k): int(v) for k, v in sorted(cnt.items())} for rk, cnt in by_rank.items()},
        "tight_contractions_by_rank": {str(k): int(v) for k, v in sorted(tight_by_rank.items())},
        "below_rank_failures_head": below_rank[:20],
        "multiset_head": ms[:80],
        "solution": {str(k): int(v) for k, v in sorted(sol.items())},
    }


def multiset_bitsets(sol: dict[int, int]) -> tuple[int, dict[int, int]]:
    support_mask = 0
    extra = {}
    for p, c in sol.items():
        support_mask |= 1 << (int(p) - 1)
        if int(c) > 1:
            extra[int(p)] = int(c) - 1
    return support_mask, extra


def occupancy(mask: int, support_mask: int, extra: dict[int, int]) -> int:
    occ = (int(mask) & int(support_mask)).bit_count()
    for p, e in extra.items():
        if (int(mask) >> (p - 1)) & 1:
            occ += int(e)
    return int(occ)


def scan_wang_violations(sol: dict[int, int], cache: dict, max_report: int = 40) -> tuple[list[dict], dict]:
    support_mask, extra = multiset_bitsets(sol)
    violations = []
    by_dim = Counter()
    by_L = Counter()
    max_excess = 0
    t0 = time.time()
    for i, (m, cap) in enumerate(zip(cache["masks"], cache["caps"])):
        if not m:
            continue
        occ = occupancy(int(m), support_mask, extra)
        if occ > int(cap):
            exc = occ - int(cap)
            max_excess = max(max_excess, exc)
            by_dim[int(cache["dims"][i])] += 1
            by_L[int(cache["Ls"][i])] += 1
            if len(violations) < max_report:
                violations.append({
                    "index": int(i),
                    "key8": int(cache["keys8"][i]),
                    "dim8": int(cache["dims"][i]),
                    "L": int(cache["Ls"][i]),
                    "cap": int(cap),
                    "occupancy": int(occ),
                    "excess": int(exc),
                    "point_count": int(int(m).bit_count()),
                    "points_head": mask_to_points(int(m))[:40],
                })
    violations.sort(key=lambda v: (v["excess"], v["L"], v["occupancy"], -v["dim8"]), reverse=True)
    return violations, {
        "violation_count": int(sum(by_dim.values())),
        "violations_by_dim8": {str(k): int(v) for k, v in sorted(by_dim.items())},
        "violations_by_L": {str(k): int(v) for k, v in sorted(by_L.items())},
        "max_excess": int(max_excess),
        "elapsed_sec": round(time.time() - t0, 3),
    }


def add_wang_cut_by_index(model, xvars: dict[int, object], cache: dict, idx: int, added: set[int], records: list[dict], reason: str) -> bool:
    if int(idx) in added:
        return False
    pts = mask_to_points(int(cache["masks"][idx]))
    cap = int(cache["caps"][idx])
    model.Add(sum(xvars[p] for p in pts) <= cap)
    added.add(int(idx))
    if len(records) < 200:
        records.append({
            "index": int(idx),
            "dim8": int(cache["dims"][idx]),
            "L": int(cache["Ls"][idx]),
            "cap": cap,
            "point_count": len(pts),
            "reason": reason,
            "points_head": pts[:20],
        })
    return True


def find_key_index_by_mask_dim(cache: dict, point: int) -> Optional[int]:
    target = 1 << (int(point) - 1)
    for i, (m, d) in enumerate(zip(cache["masks"], cache["dims"])):
        if int(d) == 1 and int(m) == target:
            return i
    return None


def point_caps_from_cache(cache: dict, rank_s: int) -> dict[int, int]:
    caps = {p: int(rank_s) for p in range(1, 256)}
    for i, (m, d, cap) in enumerate(zip(cache["masks"], cache["dims"], cache["caps"])):
        if int(d) == 1 and int(m).bit_count() == 1:
            p = int(m).bit_length()
            caps[p] = min(caps[p], int(cap))
    return caps


def solve_lazy_support_problem(
    core_name: str,
    mode: str,
    rank_s: int,
    cache: dict,
    c_ranks: dict[int, int],
    inv_qs: Sequence[int],
    nu: dict[int, int],
    max_iters: int,
    solver_time: float,
    max_add_per_iter: int,
    initial_dim: int,
    include_direct_rank: bool = True,
    no_saturation: bool = False,
    objective: Optional[str] = None,
) -> dict:
    from ortools.sat.python import cp_model

    model = cp_model.CpModel()
    pcaps = point_caps_from_cache(cache, rank_s)
    x = {p: model.NewIntVar(0, int(pcaps[p]), f"x_{p}") for p in range(1, 256)}
    model.Add(sum(x.values()) == rank_s)

    added: set[int] = set()
    cut_records: list[dict] = []
    for i, d in enumerate(cache["dims"]):
        if 1 <= int(d) <= initial_dim:
            add_wang_cut_by_index(model, x, cache, i, added, cut_records, f"initial_dim<={initial_dim}")

    direct_rank_constraints = []
    if include_direct_rank:
        for q, rk in sorted(c_ranks.items()):
            if rk <= 0:
                continue
            pts = [p for p in range(1, 256) if bit_dot(p, q)]
            lb = int(rk)
            if no_saturation and q in inv_qs:
                lb = max(lb, 10)
            model.Add(sum(x[p] for p in pts) >= lb)
            direct_rank_constraints.append({"q": int(q), "rank": int(rk), "lb": int(lb)})
    elif no_saturation:
        for q in inv_qs:
            pts = [p for p in range(1, 256) if bit_dot(p, q)]
            model.Add(sum(x[p] for p in pts) >= 10)
            direct_rank_constraints.append({"q": int(q), "rank": 9, "lb": 10})

    obj_expr = sum(int(nu[p]) * x[p] for p in range(1, 256))
    if objective == "max_sum_nu":
        model.Maximize(obj_expr)
    elif objective == "min_sum_nu":
        model.Minimize(obj_expr)

    history = []
    t_all = time.time()
    final_solution = None
    final_status = None
    final_objective = None
    for it in range(1, max_iters + 1):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(solver_time)
        solver.parameters.num_search_workers = 8
        solver.parameters.random_seed = 5400 + 101 * it + len(core_name)
        t0 = time.time()
        status = solver.Solve(model)
        elapsed = time.time() - t0
        status_name = {
            cp_model.OPTIMAL: "OPTIMAL",
            cp_model.FEASIBLE: "FEASIBLE",
            cp_model.INFEASIBLE: "INFEASIBLE",
            cp_model.MODEL_INVALID: "MODEL_INVALID",
            cp_model.UNKNOWN: "UNKNOWN",
        }.get(status, str(status))
        entry = {"iteration": it, "status": status_name, "cut_count": len(added), "solve_elapsed_sec": round(elapsed, 3)}
        if status in (cp_model.INFEASIBLE, cp_model.MODEL_INVALID):
            final_status = status_name
            history.append(entry)
            break
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            final_status = status_name
            history.append(entry)
            break
        sol = {p: int(solver.Value(x[p])) for p in range(1, 256) if int(solver.Value(x[p]))}
        st = support_stats(sol, c_ranks, inv_qs, nu)
        entry["support_stats"] = {k: v for k, v in st.items() if k not in ("solution", "multiset_head")}
        entry["objective_value"] = st["sum_nu"]
        violations, scan_stats = scan_wang_violations(sol, cache, max_report=max_add_per_iter)
        entry["scan_stats"] = scan_stats
        entry["violations_head"] = violations[:10]
        if not violations:
            final_status = "COMPLETE_WANG_FEASIBLE"
            final_solution = sol
            final_objective = st["sum_nu"]
            history.append(entry)
            break
        added_now = 0
        for v in violations[:max_add_per_iter]:
            if add_wang_cut_by_index(model, x, cache, int(v["index"]), added, cut_records, f"lazy_{mode}_iter_{it}"):
                added_now += 1
        entry["lazy_cuts_added"] = int(added_now)
        history.append(entry)
        if added_now == 0:
            final_status = "STALLED_NO_NEW_CUTS"
            final_solution = sol
            final_objective = st["sum_nu"]
            break

    result = {
        "mode": mode,
        "core_name": core_name,
        "rank_s": int(rank_s),
        "include_direct_contraction_rank_constraints": bool(include_direct_rank),
        "no_saturation_constraints": bool(no_saturation),
        "objective": objective,
        "initial_wang_dim": int(initial_dim),
        "max_iters": int(max_iters),
        "solver_time_per_iter_sec": float(solver_time),
        "max_add_per_iter": int(max_add_per_iter),
        "final_status": final_status,
        "final_objective_sum_nu": final_objective,
        "final_support_stats": support_stats(final_solution, c_ranks, inv_qs, nu) if final_solution is not None else None,
        "iterations": history,
        "total_wang_cuts_added": len(added),
        "direct_rank_constraint_count": len(direct_rank_constraints),
        "cut_records_head": cut_records[:80],
        "elapsed_sec": round(time.time() - t_all, 3),
    }
    return result


def core_raw_summary(core_name: str, pivot_mask: int) -> tuple[dict, np.ndarray, dict[int, int], list[int], dict[int, int]]:
    T_core, qmeta = quotient_core_from_mask(pivot_mask)
    c_ranks = contraction_ranks(T_core)
    inv_qs = [q for q, r in sorted(c_ranks.items()) if r == 9]
    nu = nu_values(inv_qs)
    nu_counter = Counter(nu.values())
    value_examples = {}
    for p, v in sorted(nu.items()):
        value_examples.setdefault(v, []).append(p)
    summary = {
        "core_name": core_name,
        "pivot_mask": int(pivot_mask),
        "quotient_meta": qmeta,
        "contraction_rank_histogram": {str(k): int(v) for k, v in sorted(Counter(c_ranks.values()).items())},
        "invertible_q_count": len(inv_qs),
        "rank9_baseline_total_hits": int(9 * len(inv_qs)),
        "rank9_no_saturation_total_hits": int(10 * len(inv_qs)),
        "nu_distribution": {str(k): int(v) for k, v in sorted(nu_counter.items())},
        "nu_min": int(min(nu.values())),
        "nu_max": int(max(nu.values())),
        "nu_mean_num_den": [int(sum(nu.values())), 255],
        "nu_value_examples_head": {str(k): vals[:12] for k, vals in sorted(value_examples.items())},
        "top_nu_points_head": [[int(p), int(nu[p])] for p in sorted(nu, key=lambda z: (-nu[z], z))[:30]],
        "low_nu_points_head": [[int(p), int(nu[p])] for p in sorted(nu, key=lambda z: (nu[z], z))[:30]],
    }
    return summary, T_core, c_ranks, inv_qs, nu


def full_tensor_raw_summary() -> dict:
    # In the full tensor, q is a 9-bit 3x3 matrix and M(q) has rank 3*rank(q).
    def mat_from_mask(x: int) -> np.ndarray:
        return np.array([[(int(x) >> (3 * i + j)) & 1 for j in range(3)] for i in range(3)], dtype=np.uint8)
    ranks = {q: mat_rank_f2(mat_from_mask(q)) for q in range(1, 512)}
    inv_qs = [q for q, r in sorted(ranks.items()) if r == 3]
    nu = {p: int(sum(bit_dot(p, q) for q in inv_qs)) for p in range(1, 512)}
    rank_by_point = Counter()
    nu_by_rank: dict[int, Counter] = {1: Counter(), 2: Counter(), 3: Counter()}
    for p in range(1, 512):
        rp = mat_rank_f2(mat_from_mask(p))
        rank_by_point[rp] += 1
        nu_by_rank[rp][nu[p]] += 1
    return {
        "full_A_dim": 9,
        "invertible_q_count": len(inv_qs),
        "rank22_baseline_total_hits": int(9 * len(inv_qs)),
        "rank22_no_saturation_total_hits": int(10 * len(inv_qs)),
        "A_point_rank_distribution": {str(k): int(v) for k, v in sorted(rank_by_point.items())},
        "nu_distribution": {str(k): int(v) for k, v in sorted(Counter(nu.values()).items())},
        "nu_distribution_by_A_rank": {str(r): {str(k): int(v) for k, v in sorted(cnt.items())} for r, cnt in sorted(nu_by_rank.items())},
        "nu_min": int(min(nu.values())),
        "nu_max": int(max(nu.values())),
        "nu_mean_num_den": [int(sum(nu.values())), 511],
        "best_22_term_raw_upper_sum_if_repeats_ignored": int(sum(sorted(nu.values(), reverse=True)[:22])),
        "comment": "Full tensor numbers are raw support-level contraction counts only; no full Wang/Brent support optimization is done here.",
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--cores", nargs="*", default=list(CORES), choices=list(CORES))
    ap.add_argument("--cache-dir", type=Path, default=OUTDIR / "cache")
    ap.add_argument("--out", type=Path, default=OUTDIR / "trace_saturation_gate.json")
    ap.add_argument("--rebuild-cache", action="store_true")
    ap.add_argument("--skip-solves", action="store_true")
    ap.add_argument("--solver-time", type=float, default=20.0)
    ap.add_argument("--max-iters", type=int, default=80)
    ap.add_argument("--max-add-per-iter", type=int, default=2000)
    ap.add_argument("--initial-dim", type=int, default=2)
    args = ap.parse_args()

    args.out.parent.mkdir(parents=True, exist_ok=True)
    t_all = time.time()
    lut, lut_meta = load_lut(args.lut)
    result = {
        "schema": "trace_saturation_gate_v1",
        "field": "F2",
        "purpose": "Decide whether corrected tight-contraction independent-verification-record constraints are support-forced at rank 19 in codimension-one quotient cores.",
        "rank_s": int(args.rank),
        "mathematical_facts_checked": [
            "rank M(q)=9 implies |I_q|>=9 for every rank-one CPD support",
            "sum_s nu(a_s)=sum_q |I_q| over invertible contractions",
            "saturated_q_count >= #inv - (sum_nu - 9#inv)",
            "no-saturation feasibility imposes |I_q|>=10 for every invertible q plus Wang occupation cuts",
        ],
        "lut_path": str(args.lut),
        "lut_sha256": sha256_file(args.lut),
        "lut_meta_brief": {"coverage_ok": lut_meta.get("coverage_ok"), "conflict_count": lut_meta.get("conflict_count"), "subspace_count": len(lut)},
        "parameters": {
            "cores": args.cores,
            "solver_time": args.solver_time,
            "max_iters": args.max_iters,
            "max_add_per_iter": args.max_add_per_iter,
            "initial_dim": args.initial_dim,
            "skip_solves": args.skip_solves,
        },
        "cores": {},
        "full_tensor_raw_gate": full_tensor_raw_summary(),
    }

    for core_name in args.cores:
        cfg = CORES[core_name]
        print(f"\n=== {core_name} ===", flush=True)
        raw, T_core, c_ranks, inv_qs, nu = core_raw_summary(core_name, cfg["pivot_mask"])
        raw["label"] = cfg["label"]
        n_inv = int(raw["invertible_q_count"])
        raw["support_level_interpretation"] = {
            "baseline_sum_nu": raw["rank9_baseline_total_hits"],
            "no_saturation_sum_nu_threshold": raw["rank9_no_saturation_total_hits"],
            "saturation_lower_bound_formula": f"sat >= {n_inv} - (sum_nu - {9*n_inv}) = {10*n_inv} - sum_nu for this rank-19 quotient core",
        }
        cache = build_or_load_core_cache(core_name, cfg["pivot_mask"], args.rank, lut, args.cache_dir, rebuild=args.rebuild_cache)
        raw["wang_cache_stats"] = cache["stats"]
        if not args.skip_solves:
            solves = {}
            solves["max_sum_nu_wang_plus_rank"] = solve_lazy_support_problem(
                core_name, "max_sum_nu_wang_plus_rank", args.rank, cache, c_ranks, inv_qs, nu,
                args.max_iters, args.solver_time, args.max_add_per_iter, args.initial_dim,
                include_direct_rank=True, no_saturation=False, objective="max_sum_nu")
            print(f"  max_sum_nu status={solves['max_sum_nu_wang_plus_rank']['final_status']} obj={solves['max_sum_nu_wang_plus_rank']['final_objective_sum_nu']}", flush=True)
            solves["no_saturation_feasibility"] = solve_lazy_support_problem(
                core_name, "no_saturation_feasibility", args.rank, cache, c_ranks, inv_qs, nu,
                args.max_iters, args.solver_time, args.max_add_per_iter, args.initial_dim,
                include_direct_rank=True, no_saturation=True, objective=None)
            print(f"  no_saturation status={solves['no_saturation_feasibility']['final_status']}", flush=True)
            solves["min_sum_nu_wang_only"] = solve_lazy_support_problem(
                core_name, "min_sum_nu_wang_only", args.rank, cache, c_ranks, inv_qs, nu,
                max(20, args.max_iters // 2), args.solver_time, args.max_add_per_iter, args.initial_dim,
                include_direct_rank=False, no_saturation=False, objective="min_sum_nu")
            print(f"  min_wang_only status={solves['min_sum_nu_wang_only']['final_status']} obj={solves['min_sum_nu_wang_only']['final_objective_sum_nu']}", flush=True)
            raw["lazy_support_solves"] = solves
        result["cores"][core_name] = raw

    result["elapsed_sec"] = round(time.time() - t_all, 3)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    brief = {
        "out": str(args.out),
        "elapsed_sec": result["elapsed_sec"],
        "core_brief": {
            name: {
                "nu_distribution": rec["nu_distribution"],
                "max_sum_status": rec.get("lazy_support_solves", {}).get("max_sum_nu_wang_plus_rank", {}).get("final_status"),
                "max_sum": rec.get("lazy_support_solves", {}).get("max_sum_nu_wang_plus_rank", {}).get("final_objective_sum_nu"),
                "no_sat_status": rec.get("lazy_support_solves", {}).get("no_saturation_feasibility", {}).get("final_status"),
                "no_sat_saturated_count": (rec.get("lazy_support_solves", {}).get("no_saturation_feasibility", {}).get("final_support_stats") or {}).get("rank9_saturated_count"),
                "min_wang_only": rec.get("lazy_support_solves", {}).get("min_sum_nu_wang_only", {}).get("final_objective_sum_nu"),
            }
            for name, rec in result["cores"].items()
        },
        "full_raw": result["full_tensor_raw_gate"],
    }
    print(json.dumps(brief, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
