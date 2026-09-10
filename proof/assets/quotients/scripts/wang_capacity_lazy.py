#!/usr/bin/env python3
"""Exact Wang occupation/capacity experiments for T<3,3,3> over F2.

This script is an execution instrument, not a proof by itself.  It parses
Wang's certificate table for matrix_q02_n333, expands the A-side restriction
subspace orbits under GL(3,2) x GL(3,2) and transpose, and uses the resulting
lower-bound table to test finite occupation systems.

Mathematical convention
-----------------------
A rank-s exact decomposition of T has A-side projective factors a_t in F2^9\0.
If Wang's table proves that the restriction by a constraint subspace Phi <=
(F2^9)^* has rank at least L(Phi), then every rank-s decomposition satisfies

    #{t : a_t in Phi\0} <= s - L(Phi).

For s=20 this is the T-level necessary condition whose infeasibility would
prove R_F2(T_<3,3,3>) >= 21.  This is deliberately distinct from the E11-core
capacity problem: core infeasibility alone does not prove T-level rank >= 21.

The script uses a lazy CP-SAT loop.  It starts with point constraints, solves,
then checks the candidate's subset spans against the complete expanded orbit
lower-bound table and adds violated subspace cuts.
"""
from __future__ import annotations

import argparse
import ast
import json
import math
import pickle
import re
import sys
import time
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

N = 9
MASK_ALL = (1 << N) - 1

# ---------------------------------------------------------------------------
# Text-protobuf parsing
# ---------------------------------------------------------------------------

def decode_textproto_bytes(quoted: str) -> bytes:
    return ast.literal_eval(quoted).encode("latin1")


def decode_constraints(quoted: Optional[str]) -> Tuple[int, ...]:
    if not quoted:
        return tuple()
    b = decode_textproto_bytes(quoted)
    if len(b) % 2:
        raise ValueError(f"Odd constraint byte length {len(b)}")
    return tuple(b[i] | (b[i + 1] << 8) for i in range(0, len(b), 2))


@dataclass(frozen=True)
class OrbitRecord:
    index: int
    constraints: Tuple[int, ...]
    lb: int
    proof_type: str


def parse_cert(path: Path) -> List[OrbitRecord]:
    text = path.read_text(errors="replace")
    blocks = text.split("constrained_tensors {")[1:]
    out: List[OrbitRecord] = []
    for pos, block in enumerate(blocks):
        # We only need fields appearing before/inside the proof block; a full
        # text-protobuf parser would be overkill for this flat certificate.
        m = re.search(r"\n\s*index:\s*(\d+)", "\n" + block)
        index = int(m.group(1)) if m else 0
        m = re.search(r"\n\s*rank_lower_bound:\s*(-?\d+)", "\n" + block)
        if not m:
            raise ValueError(f"No rank_lower_bound in block {pos}")
        lb = int(m.group(1))
        m = re.search(r"\n\s*constraints:\s*(\".*\")", "\n" + block)
        constraints = decode_constraints(m.group(1) if m else None)
        proof_type = "none"
        for ptype, key in [
            ("flatten", "flatten_matrix_proof"),
            ("forced_product", "forced_product_proof"),
            ("degenerate", "degenerate_proof"),
            ("backtracking", "backtracking_proof"),
        ]:
            if key in block:
                proof_type = ptype
                break
        out.append(OrbitRecord(index=index, constraints=constraints, lb=lb, proof_type=proof_type))
    return out

# ---------------------------------------------------------------------------
# GF(2) matrix and row-space utilities
# ---------------------------------------------------------------------------

def poppar(x: int) -> int:
    return x.bit_count() & 1


def mat3_rows_from_mask(mask: int) -> Tuple[int, int, int]:
    return tuple((mask >> (3 * i)) & 0b111 for i in range(3))  # type: ignore


def mat3_mask_from_rows(rows: Sequence[int]) -> int:
    m = 0
    for i, row in enumerate(rows):
        for j in range(3):
            if (row >> j) & 1:
                m |= 1 << (3 * i + j)
    return m


def mat3_transpose(A: Sequence[int]) -> Tuple[int, int, int]:
    rows = []
    for i in range(3):
        r = 0
        for j in range(3):
            if (A[j] >> i) & 1:
                r |= 1 << j
        rows.append(r)
    return tuple(rows)  # type: ignore


def mat3_mul(A: Sequence[int], B: Sequence[int]) -> Tuple[int, int, int]:
    # Rows over F2.  Row i of A*B is xor of rows of B where A[i] has a 1.
    out = []
    for i in range(3):
        r = 0
        ai = A[i]
        for k in range(3):
            if (ai >> k) & 1:
                r ^= B[k]
        out.append(r)
    return tuple(out)  # type: ignore


def mat3_vec_mul(A: Sequence[int], v: int) -> int:
    out = 0
    for i in range(3):
        if poppar(A[i] & v):
            out |= 1 << i
    return out


def mat3_rank(A: Sequence[int]) -> int:
    basis = [0, 0, 0]
    rank = 0
    for row in A:
        v = row
        while v:
            p = v.bit_length() - 1
            if basis[p]:
                v ^= basis[p]
            else:
                basis[p] = v
                rank += 1
                break
    return rank


def mat3_inv(A: Sequence[int]) -> Tuple[int, int, int]:
    # Augment [A | I] in rows encoded as six-bit ints.
    rows = [(A[i] | (1 << (3 + i))) for i in range(3)]
    r = 0
    for c in range(3):
        pivot = None
        for i in range(r, 3):
            if (rows[i] >> c) & 1:
                pivot = i
                break
        if pivot is None:
            raise ValueError("singular")
        rows[r], rows[pivot] = rows[pivot], rows[r]
        for i in range(3):
            if i != r and ((rows[i] >> c) & 1):
                rows[i] ^= rows[r]
        r += 1
    inv_rows = tuple((rows[i] >> 3) & 0b111 for i in range(3))
    return inv_rows  # type: ignore


def generate_gl3() -> List[Tuple[int, int, int]]:
    mats = []
    for rows_int in range(1 << 9):
        rows = mat3_rows_from_mask(rows_int)
        if mat3_rank(rows) == 3:
            mats.append(rows)
    assert len(mats) == 168
    return mats


def basis_image_for_action(L: Sequence[int], R: Sequence[int], transpose: bool) -> Tuple[int, ...]:
    Linv = mat3_inv(L)
    Rinv = mat3_inv(R)
    if not transpose:
        Aleft = mat3_transpose(Linv)   # L^{-T}
        Bright = mat3_transpose(Rinv) # R^{-T}
        imgs = []
        for bit in range(9):
            E = [0, 0, 0]
            E[bit // 3] = 1 << (bit % 3)
            M = mat3_mul(mat3_mul(Aleft, E), Bright)
            imgs.append(mat3_mask_from_rows(M))
        return tuple(imgs)
    else:
        # Correct transpose-branch dual action from research:
        #     F -> R^{-1} F^T L^{-1}
        imgs = []
        for bit in range(9):
            E = [0, 0, 0]
            E[bit // 3] = 1 << (bit % 3)
            Et = mat3_transpose(E)
            M = mat3_mul(mat3_mul(Rinv, Et), Linv)
            imgs.append(mat3_mask_from_rows(M))
        return tuple(imgs)


def make_actions() -> List[Tuple[int, ...]]:
    gl = generate_gl3()
    actions: List[Tuple[int, ...]] = []
    seen = set()
    for L in gl:
        for R in gl:
            for tr in (False, True):
                img = basis_image_for_action(L, R, tr)
                if img not in seen:
                    seen.add(img)
                    actions.append(img)
    # For n=3 square matrix multiplication this should be 2*168^2.
    assert len(actions) == 2 * 168 * 168, len(actions)
    return actions


def transform_mask(mask: int, img: Sequence[int]) -> int:
    out = 0
    m = mask
    while m:
        lb = m & -m
        bit = lb.bit_length() - 1
        out ^= img[bit]
        m ^= lb
    return out


def rref_basis(rows: Iterable[int], n: int = N) -> Tuple[int, ...]:
    basis = [0] * n
    for row in rows:
        v = row & ((1 << n) - 1)
        while v:
            p = v.bit_length() - 1
            if basis[p]:
                v ^= basis[p]
            else:
                basis[p] = v
                break
    # Make reduced echelon form: eliminate each pivot from all other rows.
    for p in range(n):
        if basis[p]:
            for q in range(n):
                if q != p and basis[q] and ((basis[q] >> p) & 1):
                    basis[q] ^= basis[p]
    return tuple(basis[p] for p in range(n - 1, -1, -1) if basis[p])


def pack_basis(basis: Sequence[int]) -> int:
    key = len(basis)
    shift = 4
    for row in basis:
        key |= row << shift
        shift += 9
    return key


def unpack_basis(key: int) -> Tuple[int, ...]:
    d = key & 0xF
    rows = []
    x = key >> 4
    for _ in range(d):
        rows.append(x & MASK_ALL)
        x >>= 9
    return tuple(rows)


def rref_key(rows: Iterable[int], n: int = N) -> int:
    return pack_basis(rref_basis(rows, n=n))


def transform_key(rows: Sequence[int], img: Sequence[int]) -> int:
    return rref_key((transform_mask(r, img) for r in rows), n=N)


def in_rowspace(v: int, basis: Sequence[int], n: int = N) -> bool:
    x = v
    # basis is reduced, ordered descending pivots, but generic reduction works.
    # Build quick pivot dictionary by highest bit.
    piv = {b.bit_length() - 1: b for b in basis if b}
    while x:
        p = x.bit_length() - 1
        b = piv.get(p)
        if b is None:
            return False
        x ^= b
    return True


def subspace_points_from_basis(basis: Sequence[int]) -> List[int]:
    pts = [0]
    for b in basis:
        pts += [x ^ b for x in pts]
    return [x for x in pts if x]


def matrix_rank_of_mask(mask: int) -> int:
    return mat3_rank(mat3_rows_from_mask(mask))


def gaussian_binomial(n: int, k: int, q: int = 2) -> int:
    num = 1
    den = 1
    for i in range(k):
        num *= q ** n - q ** i
        den *= q ** k - q ** i
    return num // den

# ---------------------------------------------------------------------------
# Orbit table expansion and validation
# ---------------------------------------------------------------------------

def build_or_load_lut(cert: Path, cache: Path, force: bool = False, max_orbits: Optional[int] = None) -> Tuple[Dict[int, int], dict]:
    if cache.exists() and not force:
        t0 = time.time()
        with cache.open("rb") as f:
            payload = pickle.load(f)
        print(f"Loaded LUT cache {cache} in {time.time()-t0:.2f}s: {len(payload['lut'])} subspaces")
        return payload["lut"], payload["meta"]

    records = parse_cert(cert)
    if max_orbits is not None:
        records = records[:max_orbits]
    print(f"Parsed {len(records)} Wang orbit records from {cert}")
    print("Generating GL3xGL3⋊C2 action images...")
    t0 = time.time()
    actions = make_actions()
    print(f"  {len(actions)} distinct actions generated in {time.time()-t0:.2f}s")

    lut: Dict[int, int] = {}
    conflicts = []
    orbit_sizes = []
    by_dim = Counter()
    by_dim_lb = defaultdict(Counter)
    by_proof = Counter(r.proof_type for r in records)

    t_start = time.time()
    for oi, rec in enumerate(records):
        rows = rref_basis(rec.constraints, n=N)
        dim = len(rows)
        local = set()
        for img in actions:
            key = transform_key(rows, img)
            local.add(key)
        orbit_sizes.append({"index": rec.index, "dim": dim, "lb": rec.lb, "proof_type": rec.proof_type, "orbit_size": len(local)})
        for key in local:
            old = lut.get(key)
            if old is not None and old != rec.lb:
                conflicts.append({"key": key, "old_lb": old, "new_lb": rec.lb, "orbit_index": rec.index})
            lut[key] = max(old, rec.lb) if old is not None else rec.lb
        by_dim[dim] += len(local)
        by_dim_lb[dim][rec.lb] += len(local)
        if (oi + 1) % 25 == 0 or oi + 1 == len(records):
            print(f"  expanded {oi+1:3d}/{len(records)} orbits; lut={len(lut):,}; elapsed={time.time()-t_start:.1f}s")

    actual_by_dim = Counter((key & 0xF) for key in lut.keys())
    expected_by_dim = {k: gaussian_binomial(N, k) for k in range(N + 1)}
    coverage_ok = all(actual_by_dim[k] == expected_by_dim[k] for k in range(N + 1))
    meta = {
        "cert": str(cert),
        "record_count": len(records),
        "action_count": len(actions),
        "subspace_count": len(lut),
        "expected_subspace_count": sum(expected_by_dim.values()),
        "actual_by_dimension": {str(k): actual_by_dim[k] for k in range(N + 1)},
        "expected_by_dimension": {str(k): expected_by_dim[k] for k in range(N + 1)},
        "coverage_ok": coverage_ok,
        "conflict_count": len(conflicts),
        "conflicts_head": conflicts[:20],
        "orbit_sizes": orbit_sizes,
        "proof_type_distribution": dict(by_proof),
        "build_elapsed_sec": time.time() - t_start,
    }
    print("Coverage by dimension:")
    for k in range(N + 1):
        print(f"  dim {k}: actual {actual_by_dim[k]:,} expected {expected_by_dim[k]:,}")
    print(f"coverage_ok={coverage_ok}; conflicts={len(conflicts)}; total={len(lut):,}")

    cache.parent.mkdir(parents=True, exist_ok=True)
    with cache.open("wb") as f:
        pickle.dump({"lut": lut, "meta": meta}, f, protocol=pickle.HIGHEST_PROTOCOL)
    meta_path = cache.with_suffix(".meta.json")
    meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n")
    print(f"Saved LUT cache to {cache} and metadata to {meta_path}")
    return lut, meta

# ---------------------------------------------------------------------------
# Scheme loading and consistency
# ---------------------------------------------------------------------------

def load_qmm_a_factors(path: Path) -> List[int]:
    factors: List[int] = []
    current_u: Optional[List[int]] = None
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("term "):
            if current_u is not None:
                factors.append(sum(((x & 1) << i) for i, x in enumerate(current_u)))
            current_u = None
        elif line.startswith("u "):
            current_u = [int(x) for x in line.split()[1:]]
    if current_u is not None:
        factors.append(sum(((x & 1) << i) for i, x in enumerate(current_u)))
    return factors


def check_factor_multiset_against_lut(factors: Sequence[int], s: int, lut: Dict[int, int], label: str, max_report: int = 20) -> dict:
    mult = Counter(factors)
    violations = []
    t0 = time.time()
    checked = 0
    for key, lb in lut.items():
        cap = s - lb
        if cap < 0:
            occ = 0
        else:
            basis = unpack_basis(key)
            occ = 0
            for p, c in mult.items():
                if in_rowspace(p, basis, n=N):
                    occ += c
                    if occ > cap:
                        break
        if occ > cap:
            violations.append({"key": key, "dim": key & 0xF, "lb": lb, "cap": cap, "occupancy": occ, "basis": list(unpack_basis(key))})
            if len(violations) >= max_report:
                break
        checked += 1
    return {
        "label": label,
        "s": s,
        "factor_count": len(factors),
        "distinct_factors": len(mult),
        "zero_factor_count": mult.get(0, 0),
        "max_multiplicity": max(mult.values()) if mult else 0,
        "checked_until_first_reports": checked,
        "violation_count_reported": len(violations),
        "violations_head": violations,
        "elapsed_sec": time.time() - t0,
    }

# ---------------------------------------------------------------------------
# Lazy capacity solver for full T-level problem
# ---------------------------------------------------------------------------

def key_points_expr_vars(key: int, x: dict) -> List:
    pts = subspace_points_from_basis(unpack_basis(key))
    return [x[p] for p in pts]


def candidate_solution_from_solver(solver, x: dict) -> Dict[int, int]:
    sol = {}
    for p, var in x.items():
        val = solver.Value(var)
        if val:
            sol[p] = val
    return sol


def all_subset_span_keys(support: Sequence[int]) -> List[int]:
    # Enumerate unique row spaces generated by all nonempty subsets of support.
    keys = set()
    spans = {0: tuple()}  # mask over support not stored; iterative basis states.
    # Simpler incremental closure over generated bases.  For m<=23, direct bitmask
    # enumeration is acceptable and gives predictable evidence.
    m = len(support)
    # Use Gray-code-like dynamic update? Direct recurrence basis[mask] from lsb.
    basis_by_mask = {0: tuple()}
    for mask in range(1, 1 << m):
        lb = mask & -mask
        j = lb.bit_length() - 1
        prev = mask ^ lb
        b = rref_basis(list(basis_by_mask[prev]) + [support[j]], n=N)
        basis_by_mask[mask] = b
        keys.add(pack_basis(b))
    return list(keys)


def occupancy_of_key(key: int, solution: Dict[int, int]) -> int:
    basis = unpack_basis(key)
    return sum(c for p, c in solution.items() if in_rowspace(p, basis, n=N))


def find_violated_subset_cuts(solution: Dict[int, int], s: int, lut: Dict[int, int], max_cuts: int = 2000) -> Tuple[List[dict], dict]:
    support = sorted(solution)
    t0 = time.time()
    keys = all_subset_span_keys(support)
    violations = []
    missing = 0
    checked = 0
    for key in keys:
        lb = lut.get(key)
        if lb is None:
            missing += 1
            continue
        occ = occupancy_of_key(key, solution)
        cap = s - lb
        if occ > cap:
            violations.append({
                "key": key,
                "dim": key & 0xF,
                "lb": lb,
                "cap": cap,
                "occupancy": occ,
                "excess": occ - cap,
                "basis": list(unpack_basis(key)),
            })
        checked += 1
    violations.sort(key=lambda v: (v["excess"], v["lb"], v["occupancy"], -v["dim"]), reverse=True)
    stats = {
        "support_size": len(support),
        "total_multiplicity": sum(solution.values()),
        "unique_subset_spans": len(keys),
        "checked_spans": checked,
        "missing_lut_spans": missing,
        "violation_count": len(violations),
        "elapsed_sec": time.time() - t0,
        "violations_by_dim": dict(Counter(v["dim"] for v in violations)),
        "violations_by_lb": dict(Counter(v["lb"] for v in violations)),
    }
    return violations[:max_cuts], stats


def solve_lazy_T20(lut: Dict[int, int], s: int, outdir: Path, max_iters: int = 50, solver_time: float = 120.0, add_dim2: bool = True) -> dict:
    from ortools.sat.python import cp_model

    model = cp_model.CpModel()
    points = list(range(1, 1 << N))
    x = {p: model.NewIntVar(0, s, f"x_{p}") for p in points}
    model.Add(sum(x[p] for p in points) == s)

    added_keys = set()
    cut_records = []

    def add_cut(key: int, reason: str):
        if key in added_keys:
            return False
        lb = lut[key]
        cap = s - lb
        pts = subspace_points_from_basis(unpack_basis(key))
        model.Add(sum(x[p] for p in pts) <= cap)
        added_keys.add(key)
        cut_records.append({"key": key, "dim": key & 0xF, "lb": lb, "cap": cap, "point_count": len(pts), "reason": reason})
        return True

    # Always add every one-dimensional point/multiplicity constraint.
    point_cuts = 0
    dim2_cuts = 0
    for key, lb in lut.items():
        d = key & 0xF
        if d == 1:
            if add_cut(key, "all_dim1_initial"):
                point_cuts += 1
        elif add_dim2 and d == 2:
            if add_cut(key, "all_dim2_initial"):
                dim2_cuts += 1
    print(f"Initial cuts: dim1={point_cuts}, dim2={dim2_cuts}, total={len(added_keys)}")

    history = []
    final_solution = None
    final_status = None

    for it in range(1, max_iters + 1):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = solver_time
        solver.parameters.num_search_workers = 8
        solver.parameters.random_seed = 1000 + it
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
        print(f"Iteration {it}: solver status={status_name}, cuts={len(added_keys)}, solve_elapsed={elapsed:.2f}s")
        entry = {"iteration": it, "solver_status": status_name, "cut_count": len(added_keys), "solve_elapsed_sec": elapsed}
        if status in (cp_model.INFEASIBLE, cp_model.MODEL_INVALID):
            final_status = status_name
            history.append(entry)
            break
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            final_status = status_name
            history.append(entry)
            break

        sol = candidate_solution_from_solver(solver, x)
        entry["solution"] = {str(k): v for k, v in sorted(sol.items())}
        entry["support_size"] = len(sol)
        entry["max_mult"] = max(sol.values()) if sol else 0
        violations, stats = find_violated_subset_cuts(sol, s, lut, max_cuts=5000)
        entry["check_stats"] = stats
        entry["violations_head"] = violations[:20]
        print(f"  candidate support={len(sol)}, max_mult={entry['max_mult']}, subset_spans={stats['unique_subset_spans']:,}, violations={stats['violation_count']:,}, check_elapsed={stats['elapsed_sec']:.2f}s")
        if not violations:
            final_status = "CAPACITY_FEASIBLE_NO_VIOLATION_FOUND"
            final_solution = sol
            history.append(entry)
            break
        added = 0
        for v in violations:
            if add_cut(v["key"], f"lazy_iter_{it}"):
                added += 1
        entry["lazy_cuts_added"] = added
        print(f"  added {added} lazy cuts")
        history.append(entry)
        if added == 0:
            final_status = "STALLED_NO_NEW_CUTS"
            final_solution = sol
            break

    result = {
        "problem": "T-level Wang occupation capacity",
        "field": "F2",
        "rank_s": s,
        "mathematical_meaning": "Infeasibility of this T-level capacity system is a necessary-condition proof of R_F2(T_<3,3,3>) >= s+1 only when all cuts used are correct Wang subspace constraints; feasibility means the Wang occupation constraints alone do not exclude rank s.",
        "initial_all_dim1": True,
        "initial_all_dim2": add_dim2,
        "final_status": final_status,
        "final_solution": {str(k): v for k, v in sorted(final_solution.items())} if final_solution else None,
        "iterations": history,
        "cut_count": len(added_keys),
        "cuts_by_dim": dict(Counter(c["dim"] for c in cut_records)),
        "cuts_by_lb": dict(Counter(c["lb"] for c in cut_records)),
        "cut_records_head": cut_records[:100],
        "cut_records_tail": cut_records[-100:],
    }
    outdir.mkdir(parents=True, exist_ok=True)
    outpath = outdir / f"t_level_capacity_s{s}_lazy.json"
    outpath.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Saved lazy result to {outpath}")
    return result

# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cert", type=Path, default=Path("assets/quotients/data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt"))
    ap.add_argument("--cache", type=Path, default=Path("assets/quotients/data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--outdir", type=Path, default=Path("assets/quotients/data/wang_capacity"))
    ap.add_argument("--force-lut", action="store_true")
    ap.add_argument("--build-only", action="store_true")
    ap.add_argument("--check-cn122", action="store_true")
    ap.add_argument("--solve-t", type=int, default=None, help="Solve T-level capacity for rank s, e.g. 20")
    ap.add_argument("--max-iters", type=int, default=50)
    ap.add_argument("--solver-time", type=float, default=120.0)
    ap.add_argument("--no-dim2-initial", action="store_true")
    args = ap.parse_args()

    t0 = time.time()
    lut, meta = build_or_load_lut(args.cert, args.cache, force=args.force_lut)
    args.outdir.mkdir(parents=True, exist_ok=True)
    (args.outdir / "lut_meta_copy.json").write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n")
    print(f"LUT ready: {len(lut):,} subspaces; coverage_ok={meta.get('coverage_ok')} conflicts={meta.get('conflict_count')}")

    summary = {"lut_meta": meta, "actions": []}

    # Low-dimensional validation: one-dimensional orbit/rank counts.
    dim1 = [(key, lb) for key, lb in lut.items() if (key & 0xF) == 1]
    rank_lb_counts = Counter()
    for key, lb in dim1:
        row = unpack_basis(key)[0]
        rank_lb_counts[(matrix_rank_of_mask(row), lb)] += 1
    print("Dim-1 rank/LB counts:", dict(sorted(rank_lb_counts.items())))
    summary["dim1_rank_lb_counts"] = {f"rank{r}_lb{lb}": c for (r, lb), c in sorted(rank_lb_counts.items())}

    if args.check_cn122:
        qmm = Path("assets/quotients/data/cn122_3x3_r23_repro/scheme.qmm")
        factors = load_qmm_a_factors(qmm)
        check = check_factor_multiset_against_lut(factors, len(factors), lut, "cn122 full rank-23 A factors")
        print("cn122 full-scheme consistency:", json.dumps(check, indent=2)[:4000])
        summary["cn122_full_check"] = check

    if args.solve_t is not None:
        res = solve_lazy_T20(lut, args.solve_t, args.outdir, max_iters=args.max_iters, solver_time=args.solver_time, add_dim2=not args.no_dim2_initial)
        summary["lazy_result"] = {k: v for k, v in res.items() if k not in ("iterations",)}

    summary["elapsed_total_sec"] = time.time() - t0
    (args.outdir / "wang_capacity_lazy_summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(f"Summary saved to {args.outdir / 'wang_capacity_lazy_summary.json'}")


if __name__ == "__main__":
    main()
