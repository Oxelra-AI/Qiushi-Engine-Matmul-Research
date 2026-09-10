#!/usr/bin/env python3
"""Independent semantic reconstruction for the eight dim-2 Wang occupation raises.

This script deliberately rebuilds the node-local systems without importing the
research row builder.  It uses only the raw Wang LUT, orbit representatives,
and elementary quotient linear algebra over F_2.

For each load-bearing dim-2 orbit 484--491 it checks:
  1. independent row set at target L=18 matches the existing builder row-by-row;
  2. the independent CP-SAT integer model is infeasible at target 18;
  3. the same model is feasible at target 19 (near-edge positive control);
  4. a verified rank-23 full decomposition, projected modulo W and with killed
     terms dropped, satisfies every inherited row at its projected length.

The positive control is not evidence for the raise itself; it is a builder sanity
check.  The target-19 ladder is also not a theorem premise; it detects an
accidental over-tightening of the row system.
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
from typing import Dict, Iterable, List, Sequence, Tuple

try:
    from ortools.sat.python import cp_model  # type: ignore
except Exception:  # pragma: no cover
    cp_model = None

LUT_PATH = Path("assets/quotients/data/wang_f2_lb20/wang_subspace_lut.pkl")
CACHE_PATH = Path("assets/quotients/data/wang_f2_lb20/wang_orbit_closed_cache.pkl")
RANK23_PATH = Path("assets/occupation/data/pivot_fixed/pivot17_rank23_transformed_control.json")
OUTDIR = Path("assets/occupation/data/dim2_independent")
OLD_SCRIPT_DIR = Path("assets/occupation/scripts")

INDICES = [484, 485, 486, 487, 488, 489, 490, 491]
NBITS = 9


def rref_ind(rows: Iterable[int], nbits: int = NBITS) -> Tuple[int, ...]:
    """Row-reduced basis over F2 with highest-set-bit pivots.

    Implemented independently of node_local_occupation_closure.rref_basis.
    """
    basis: Dict[int, int] = {}
    for raw in rows:
        x = int(raw)
        if x == 0:
            continue
        # Reduce by current pivots from high to low.
        changed = True
        while x and changed:
            changed = False
            for piv in sorted(basis.keys(), reverse=True):
                if (x >> piv) & 1:
                    x ^= basis[piv]
                    changed = True
        if x == 0:
            continue
        piv = x.bit_length() - 1
        # Eliminate the new pivot from all existing rows.
        for q in list(basis.keys()):
            if (basis[q] >> piv) & 1:
                basis[q] ^= x
                # pivot q remains the leading bit because piv<q after reduction
        basis[piv] = x
    return tuple(basis[p] for p in sorted(basis.keys(), reverse=True))


def pack_ind(basis_rref: Sequence[int]) -> int:
    packed = 0
    for i, row in enumerate(basis_rref):
        packed |= int(row) << (NBITS * i)
    return (packed << 4) | len(basis_rref)


def reduce_mod_rref(v0: int, rref: Sequence[int]) -> int:
    v = int(v0)
    for row in rref:
        piv = int(row).bit_length() - 1
        if piv >= 0 and ((v >> piv) & 1):
            v ^= int(row)
    return v


def free_bits(rref: Sequence[int], nbits: int = NBITS) -> List[int]:
    pivots = {int(row).bit_length() - 1 for row in rref if int(row)}
    return [i for i in range(nbits) if i not in pivots]


def lift_q_ind(q: int, free: Sequence[int]) -> int:
    v = 0
    for i, bit in enumerate(free):
        if (int(q) >> i) & 1:
            v |= 1 << bit
    return v


def coord_from_remainder(rem: int, free: Sequence[int]) -> int:
    q = 0
    for i, bit in enumerate(free):
        if (int(rem) >> bit) & 1:
            q |= 1 << i
    return q


def quotient_coord(v: int, W: Sequence[int], free: Sequence[int]) -> int:
    rem = reduce_mod_rref(v, W)
    # A correct RREF reduction leaves no pivot bits; assert by reconstructing.
    q = coord_from_remainder(rem, free)
    if lift_q_ind(q, free) != rem:
        raise AssertionError(f"non-canonical remainder {rem} for v={v}, W={W}, free={free}, q={q}")
    return q


def in_span(v0: int, rref: Sequence[int]) -> bool:
    return reduce_mod_rref(v0, rref) == 0


def all_subspaces(k: int) -> Tuple[Tuple[int, ...], ...]:
    """Enumerate all RREF row spaces of F2^k.

    Uses a closure-by-adjoining-vectors construction, independent from the old
    builder's cached function.  k=7 gives 29212 spaces including 0 and full.
    """
    spaces = {tuple()}
    for v in range(1, 1 << k):
        additions = []
        for sp in spaces:
            if not in_span(v, sp):
                additions.append(rref_ind((*sp, v), k))
        spaces.update(additions)
    return tuple(sorted(spaces, key=lambda b: (len(b), b)))


def qbasis_mask(qbasis: Sequence[int]) -> int:
    mask = 0
    d = len(qbasis)
    for coeff in range(1, 1 << d):
        q = 0
        for i, row in enumerate(qbasis):
            if (coeff >> i) & 1:
                q ^= int(row)
        if q <= 0:
            raise AssertionError(f"bad quotient point {q} from basis {qbasis}")
        mask |= 1 << (q - 1)
    return mask


def popcount(x: int) -> int:
    return int(x).bit_count()


def canonical_rows_digest(rows: Sequence[Tuple[int, int]]) -> str:
    h = hashlib.sha256()
    h.update(len(rows).to_bytes(8, "little"))
    for mask, cap in rows:
        h.update(int(cap).to_bytes(2, "little", signed=True))
        h.update(int(mask).to_bytes(16, "little", signed=False))
    return h.hexdigest()


def independent_rows(W_basis: Sequence[int], lut: Dict[int, int], support_size: int) -> Tuple[List[Tuple[int, int]], Dict]:
    W = rref_ind(W_basis, NBITS)
    k = NBITS - len(W)
    free = free_bits(W, NBITS)
    constraints: Dict[int, int] = {}
    stats = Counter()
    cap_hist = Counter(); dim_hist = Counter(); pop_hist = Counter()
    for qbasis in all_subspaces(k):
        if len(qbasis) == 0 or len(qbasis) == k:
            continue
        lifts = [lift_q_ind(q, free) for q in qbasis]
        U = rref_ind((*W, *lifts), NBITS)
        lb = lut.get(pack_ind(U))
        if lb is None:
            stats["missing_lut"] += 1
            continue
        cap = int(support_size) - int(lb)
        mask = qbasis_mask(qbasis)
        if mask not in constraints or cap < constraints[mask]:
            constraints[mask] = cap
        cap_hist[cap] += 1
        dim_hist[len(qbasis)] += 1
        pop_hist[popcount(mask)] += 1
        if cap < 0:
            stats["negative_cap"] += 1
        if cap >= support_size:
            stats["tautological"] += 1
    rows = sorted(constraints.items(), key=lambda mc: (mc[1], popcount(mc[0]), mc[0]))
    meta = {
        "W_rref": list(W),
        "quotient_dim": k,
        "free_bits": list(free),
        "unique_rows": len(rows),
        "strict_subspaces": sum(1 for sp in all_subspaces(k) if 0 < len(sp) < k),
        "cap_hist": {str(k): int(v) for k, v in sorted(cap_hist.items())},
        "quotient_subspace_dim_hist": {str(k): int(v) for k, v in sorted(dim_hist.items())},
        "mask_popcount_hist": {str(k): int(v) for k, v in sorted(pop_hist.items())},
        "negative_cap_rows": int(stats["negative_cap"]),
        "tautological_source_rows": int(stats["tautological"]),
        "missing_lut_rows": int(stats["missing_lut"]),
        "row_digest": canonical_rows_digest(rows),
    }
    return rows, meta


def load_lut_and_orbits():
    with LUT_PATH.open("rb") as f:
        data = pickle.load(f)
    lut = data["lut"] if isinstance(data, dict) and "lut" in data else data
    meta = data.get("meta", {}) if isinstance(data, dict) else {}
    with CACHE_PATH.open("rb") as f:
        cache = pickle.load(f)
    orbit_by_idx = {int(o["cert_index"]): o for o in cache["orbits"]}
    return lut, meta, orbit_by_idx


def solve_cp(k: int, support_size: int, rows: Sequence[Tuple[int, int]], timeout: float, workers: int = 8) -> Dict:
    if cp_model is None:
        return {"status": "NO_ORTOOLS", "feasible": None}
    model = cp_model.CpModel()
    npts = (1 << k) - 1
    xs = [model.NewIntVar(0, support_size, f"x_{q}") for q in range(1, npts + 1)]
    model.Add(sum(xs) == support_size)
    for mask, cap in rows:
        pts = [i for i in range(npts) if (int(mask) >> i) & 1]
        if cap < 0:
            model.Add(0 <= -1)
        elif cap < support_size and pts:
            model.Add(sum(xs[i] for i in pts) <= int(cap))
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(timeout)
    solver.parameters.num_search_workers = int(workers)
    solver.parameters.random_seed = 3007
    t0 = time.time()
    st = solver.Solve(model)
    elapsed = time.time() - t0
    name = solver.StatusName(st)
    out = {"status": name, "elapsed_sec": elapsed, "conflicts": int(solver.NumConflicts()), "branches": int(solver.NumBranches())}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol = [int(solver.Value(x)) for x in xs]
        nz = [(i + 1, v) for i, v in enumerate(sol) if v]
        out.update({
            "feasible": True,
            "weight": int(sum(sol)),
            "nonzero_count": len(nz),
            "max_multiplicity": int(max(sol) if sol else 0),
            "solution_head": nz[:80],
            "violations_check": scan_counts(sol, rows)["violations"],
        })
    elif st == cp_model.INFEASIBLE:
        out["feasible"] = False
    else:
        out["feasible"] = None
    return out


def scan_counts(counts: Sequence[int], rows: Sequence[Tuple[int, int]]) -> Dict:
    violations = 0; tight = 0; max_excess = -10**9; worst = None
    for idx, (mask, cap) in enumerate(rows):
        lhs = 0
        m = int(mask)
        while m:
            low = m & -m
            i = low.bit_length() - 1
            lhs += int(counts[i])
            m ^= low
        excess = lhs - int(cap)
        if excess > 0:
            violations += 1
            if worst is None or excess > worst["excess"]:
                worst = {"row_index": idx, "lhs": lhs, "cap": int(cap), "excess": int(excess), "popcount": popcount(mask)}
        if excess == 0:
            tight += 1
        if excess > max_excess:
            max_excess = excess
    return {"violations": violations, "tight_rows": tight, "max_excess": int(max_excess), "worst": worst}


def project_rank23_control(W: Sequence[int], free: Sequence[int], rank23_path: Path) -> Dict:
    obj = json.loads(rank23_path.read_text())
    terms = obj["terms"]
    counts = [0] * 127
    killed = []
    projected_terms = []
    for t, triple in enumerate(terms):
        a = int(triple[0])
        q = quotient_coord(a, W, free)
        if q == 0:
            killed.append({"term_index": t, "A": a})
        else:
            counts[q - 1] += 1
            projected_terms.append({"term_index": t, "A": a, "q": q})
    nz = [(i + 1, v) for i, v in enumerate(counts) if v]
    return {
        "rank23_path": str(rank23_path),
        "terms_total": len(terms),
        "killed_count": len(killed),
        "projected_length": int(sum(counts)),
        "nonzero_projected_directions": len(nz),
        "max_projected_multiplicity": int(max(counts) if counts else 0),
        "killed_terms": killed,
        "counts": counts,
        "support_head": nz[:80],
    }


def compare_with_existing_builder(W: Sequence[int], lut: Dict[int, int], support_size: int, ind_rows: Sequence[Tuple[int, int]]) -> Dict:
    if str(OLD_SCRIPT_DIR) not in sys.path:
        sys.path.insert(0, str(OLD_SCRIPT_DIR))
    from node_local_occupation_closure import node_constraints as old_node_constraints  # type: ignore
    old_rows, old_meta = old_node_constraints(W, lut, support_size)
    old_sorted = sorted(old_rows, key=lambda mc: (mc[1], popcount(mc[0]), mc[0]))
    ind_sorted = list(ind_rows)
    exact = old_sorted == ind_sorted
    mismatch = None
    if not exact:
        for i, (a, b) in enumerate(zip(ind_sorted, old_sorted)):
            if a != b:
                mismatch = {"index": i, "independent": [int(a[0]), int(a[1])], "existing": [int(b[0]), int(b[1])]}
                break
        if mismatch is None and len(ind_sorted) != len(old_sorted):
            mismatch = {"lengths": [len(ind_sorted), len(old_sorted)]}
    return {
        "exact_row_match": exact,
        "independent_digest": canonical_rows_digest(ind_sorted),
        "existing_digest": canonical_rows_digest(old_sorted),
        "existing_unique_rows": len(old_sorted),
        "first_mismatch": mismatch,
        "existing_meta_subset": {
            "unique_masks": old_meta.get("unique_masks"),
            "negative_cap_rows": old_meta.get("negative_cap_rows"),
            "cap_hist": old_meta.get("cap_hist"),
        },
    }


def file_sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--outdir", type=Path, default=OUTDIR)
    ap.add_argument("--targets", default="18,19", help="support sizes for CP-SAT ladder")
    ap.add_argument("--cpsat-timeout", type=float, default=120.0)
    ap.add_argument("--write-row-files", action="store_true")
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    targets = [int(x) for x in args.targets.split(",") if x.strip()]

    lut, lut_meta, orbit_by_idx = load_lut_and_orbits()
    summary = {
        "schema": "dim2_independent_semantics_v1",
        "purpose": "independent semantic reconstruction, positive controls, and target ladder for dim-2 occupation raises 484-491",
        "lut_path": str(LUT_PATH),
        "lut_sha256": file_sha256(LUT_PATH),
        "cache_path": str(CACHE_PATH),
        "cache_sha256": file_sha256(CACHE_PATH),
        "rank23_control_path": str(RANK23_PATH),
        "rank23_control_sha256": file_sha256(RANK23_PATH),
        "indices": INDICES,
        "targets": targets,
        "results": [],
    }

    t_all = time.time()
    for idx in INDICES:
        orb = orbit_by_idx[idx]
        W_raw = [int(x) for x in orb["basis"]]
        W = rref_ind(W_raw, NBITS)
        k = NBITS - len(W)
        free = free_bits(W, NBITS)
        raw_lb = int(orb["raw_lb"])
        print(f"\n=== independent orbit {idx}: W_raw={W_raw} W={W} raw_lb={raw_lb} k={k} ===", flush=True)

        target_records = {}
        row_records = {}
        for target in sorted(set(targets + [raw_lb])):
            rows, meta = independent_rows(W, lut, target)
            compare = compare_with_existing_builder(W, lut, target, rows)
            if args.write_row_files:
                rows_path = args.outdir / f"orbit_{idx}_target_{target}_rows.json"
                rows_path.write_text(json.dumps({"rows": [[int(m), int(c)] for m, c in rows], "meta": meta}, indent=2) + "\n")
            cp = solve_cp(k, target, rows, args.cpsat_timeout)
            target_records[str(target)] = cp
            row_records[str(target)] = {"meta": meta, "compare_existing": compare}
            print(f"target {target}: rows={len(rows)} match={compare['exact_row_match']} cp={cp['status']} feas={cp.get('feasible')} elapsed={cp['elapsed_sec']:.2f}", flush=True)

        # Positive control projected from known rank-23 scheme, scanned at projected length.
        proj = project_rank23_control(W, free, RANK23_PATH)
        m = proj["projected_length"]
        rows_m, meta_m = independent_rows(W, lut, m)
        scan = scan_counts(proj["counts"], rows_m)
        proj.pop("counts")
        positive = {"projected_control": proj, "row_meta_at_projected_length": meta_m, "scan": scan, "passes": scan["violations"] == 0}
        print(f"positive: projected length={m}, killed={proj['killed_count']}, violations={scan['violations']}, max_excess={scan['max_excess']}", flush=True)

        rec = {
            "cert_index": idx,
            "W_basis_from_orbit": W_raw,
            "W_rref_independent": list(W),
            "raw_lb": raw_lb,
            "quotient_dim": k,
            "orbit_size": int(orb.get("orbit_size", -1)),
            "proof_type": orb.get("proof_type"),
            "row_records": row_records,
            "target_ladder": target_records,
            "projected_rank23_positive_control": positive,
        }
        summary["results"].append(rec)
        (args.outdir / f"orbit_{idx}_audit.json").write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n")

    summary["elapsed_sec"] = time.time() - t_all
    summary["all_target18_infeasible"] = all(r["target_ladder"].get("18", {}).get("feasible") is False for r in summary["results"])
    summary["all_target19_feasible"] = all(r["target_ladder"].get("19", {}).get("feasible") is True for r in summary["results"])
    summary["all_rows_match_existing"] = all(
        rr["compare_existing"]["exact_row_match"]
        for r in summary["results"]
        for rr in r["row_records"].values()
    )
    summary["all_projected_rank23_controls_pass"] = all(r["projected_rank23_positive_control"]["passes"] for r in summary["results"])
    out = args.outdir / "independent_semantics_summary.json"
    out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print("\nFINAL")
    print(json.dumps({
        "out": str(out),
        "elapsed_sec": summary["elapsed_sec"],
        "all_target18_infeasible": summary["all_target18_infeasible"],
        "all_target19_feasible": summary["all_target19_feasible"],
        "all_rows_match_existing": summary["all_rows_match_existing"],
        "all_projected_rank23_controls_pass": summary["all_projected_rank23_controls_pass"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
