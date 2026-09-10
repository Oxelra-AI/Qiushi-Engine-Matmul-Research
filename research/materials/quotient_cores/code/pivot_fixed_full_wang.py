#!/usr/bin/env python3
"""Pivot-fixed full Wang occupation models for T<3,3,3> over F2.

This script implements the single-object formulation suggested after the
lift-bit checks.  Fix one full A-direction p with multiplicity one.  The
remaining A-multiset is represented by variables x_a for all a != p.  Every
Wang LUT row U gives

    sum_{a in U, a != p} x_a <= (length - LB(U)) - 1_{p in U}.

For length 20 and p of matrix rank 2 or 3, x_a are Boolean and the row
span(p,a) enforces that at most one lift of each quotient direction is chosen.
Rows containing p are exactly quotient occupation rows with the pivot term
subtracted; rows not containing p are the lift-bit constraints.  Thus this is
precisely the quotient+lift system, but as one full-support problem.

The script also checks same-encoding controls, especially the transported
rank-23 scheme with pivot 17 fixed.
"""
from __future__ import annotations

import argparse
import heapq
import json
import os
import struct
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))

from extract_known_supports import parse_rank23_txt  # type: ignore
from quotient_line_caps_and_controls import (  # type: ignore
    build_t333,
    recon_full,
    gl3,
    transform_term,
)

try:
    from ortools.sat.python import cp_model  # type: ignore
except Exception:  # pragma: no cover
    cp_model = None

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/pivot_fixed"
RANK23_SRC = Path("data/flip_cpd_inspect/src/khoruzhii-flip-cpd-9eeb17f/data/schemes_paper/gg-333-rank23-rec-0-0-0-z.txt")
RANK2_CONTROL = ROOT / "workspace/data/wang_native/three_orbit_controls/rank2_quotient_rank22_control.json"
MAGIC = b"WANG512\x01"


def bit_in(words: Tuple[int, ...], p: int) -> bool:
    return bool((words[p >> 6] >> (p & 63)) & 1)


def mask_contains_any(words: Tuple[int, ...], points: Iterable[int]) -> bool:
    return any(bit_in(words, p) for p in points)


def popcount_words(words: Tuple[int, ...]) -> int:
    return sum(int(w).bit_count() for w in words)


def parse_multiset_arg(arg: str) -> List[int]:
    p = Path(arg)
    if p.exists():
        d = json.loads(p.read_text())
        if isinstance(d, list):
            return [int(x) for x in d]
        for key in ["a_multiset", "full_a_multiset", "support", "solution", "selected_points"]:
            if key in d:
                return [int(x) for x in d[key]]
        for r in reversed(d.get("rounds", [])):
            if "full_A_multiset" in r:
                return [int(x) for x in r["full_A_multiset"]]
        if "terms" in d:
            return [int(t[0]) for t in d["terms"]]
        raise ValueError(f"Cannot find multiset in {arg}")
    return [int(x) for x in arg.split(",") if x]


def load_binary_rows(path: Path, max_rows: int | None = None):
    with open(path, "rb") as f:
        magic = f.read(8)
        if magic != MAGIC:
            raise ValueError(f"bad magic {magic!r} in {path}")
        nrows = struct.unpack("<I", f.read(4))[0]
        limit = nrows if max_rows is None else min(nrows, max_rows)
        for idx in range(limit):
            cap, dim, _res = struct.unpack("<BBH", f.read(4))
            words = struct.unpack("<8Q", f.read(64))
            yield idx, int(cap), int(dim), tuple(int(w) for w in words)
        # If max_rows was used, do not require reading the rest.


def binary_header(path: Path) -> Dict:
    size = path.stat().st_size
    with open(path, "rb") as f:
        magic = f.read(8)
        nrows = struct.unpack("<I", f.read(4))[0]
    return {"path": str(path), "magic": magic.decode("latin1"), "nrows": nrows, "size_bytes": size, "expected_size_bytes": 12 + 68 * nrows, "size_matches": size == 12 + 68 * nrows}


def mult_counter(ms: List[int]) -> Counter:
    return Counter(int(x) for x in ms if int(x) != 0)


def check_multiset(binary: Path, multiset: List[int], length: int, max_report: int = 20) -> Dict:
    counts = mult_counter(multiset)
    nonzero = sorted(counts)
    viol_count = 0
    excess_total = 0
    max_excess = 0
    cap_hist = Counter()
    dim_hist = Counter()
    violations = []
    rows = 0
    t0 = time.time()
    for row_index, cap, dim, words in load_binary_rows(binary):
        rows += 1
        occ = 0
        for p, m in counts.items():
            if bit_in(words, p):
                occ += m
        cap_hist[cap] += 1
        dim_hist[dim] += 1
        if occ > cap:
            excess = occ - cap
            viol_count += 1
            excess_total += excess
            max_excess = max(max_excess, excess)
            if len(violations) < max_report:
                violations.append({"row_index": row_index, "cap": cap, "dim": dim, "occ": occ, "excess": excess, "popcount": popcount_words(words)})
    return {
        "binary": binary_header(binary),
        "length": length,
        "multiset_size": len(multiset),
        "distinct_count": len(nonzero),
        "duplicate_count": len(multiset) - len(nonzero),
        "multiplicity_hist": dict(sorted((int(k), int(v)) for k, v in Counter(counts.values()).items())),
        "max_multiplicity": max(counts.values()) if counts else 0,
        "rows_checked": rows,
        "passed": viol_count == 0,
        "violation_count": viol_count,
        "excess_total": excess_total,
        "max_excess": max_excess,
        "violation_head": violations,
        "cap_hist": dict(sorted((int(k), int(v)) for k, v in cap_hist.items())),
        "dim_hist": dict(sorted((int(k), int(v)) for k, v in dim_hist.items())),
        "elapsed_sec": time.time() - t0,
    }


def derive_rank2_pivot17_control(out: Path) -> Dict:
    """Reconstruct the full transformed rank-23 scheme used in analysis."""
    ctl = json.loads(RANK2_CONTROL.read_text())
    P_index = int(ctl["P_index"])
    Q_index = int(ctl["Q_index"])
    terms = [tuple(map(int, t)) for t in parse_rank23_txt(RANK23_SRC)]
    G = gl3()
    P = G[P_index]
    Q = G[Q_index]
    trans = [transform_term(t, P, Q) for t in terms]
    full_ok = bool(np.array_equal(recon_full(trans), build_t333()))
    selected = int(ctl["term_index"])
    rec = {
        "schema": "pivot_fixed_rank23_control_v1",
        "source": str(RANK23_SRC),
        "control_source": str(RANK2_CONTROL),
        "pivot": 17,
        "P_index": P_index,
        "Q_index": Q_index,
        "selected_term_index": selected,
        "selected_A": int(trans[selected][0]),
        "full_tensor_verified_after_transform": full_ok,
        "terms": [[int(a), int(b), int(c)] for a, b, c in trans],
        "full_a_multiset": [int(a) for a, _, _ in trans],
        "a_multiplicity_hist": dict(sorted((str(k), int(v)) for k, v in Counter(a for a, _, _ in trans).items() if v > 1)),
        "rank": len(trans),
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n")
    return rec


def row_rhs(cap: int, words: Tuple[int, ...], pivot: int, pivot_mult: int) -> int:
    return int(cap) - (pivot_mult if bit_in(words, pivot) else 0)


def add_constraint_record(model, variables, row: Dict, pivot: int, pivot_mult: int):
    rhs = row_rhs(row["cap"], row["words"], pivot, pivot_mult)
    pts = [p for p in row["points"] if p != pivot]
    if rhs < 0:
        model.Add(0 <= -1)
    elif pts:
        model.Add(sum(variables[p] for p in pts) <= rhs)
    else:
        model.Add(0 <= rhs)


def words_to_points(words: Tuple[int, ...]) -> List[int]:
    pts = []
    for wi, w0 in enumerate(words):
        w = int(w0)
        while w:
            lb = w & -w
            b = lb.bit_length() - 1
            p = wi * 64 + b
            if 1 <= p <= 511:
                pts.append(p)
            w ^= lb
    return pts


def canonical_row(idx: int, cap: int, dim: int, words: Tuple[int, ...]) -> Dict:
    return {"row_index": int(idx), "cap": int(cap), "dim": int(dim), "words": tuple(int(w) for w in words), "points": words_to_points(words)}


def initial_pair_rows(pivot: int, length: int, ub: int) -> List[Dict]:
    """Manual rows span(p,a): x_a + x_{a+p} <= ub for each pair."""
    seen = set(); rows = []
    fake_idx = -1
    for a in range(1, 512):
        if a == pivot:
            continue
        b = a ^ pivot
        if b == 0 or b == pivot:
            continue
        pair = tuple(sorted((a, b)))
        if pair in seen:
            continue
        seen.add(pair)
        words = [0] * 8
        # full row includes p, a, a+p and has cap = ub + 1 after pivot fixed
        for q in (pivot, pair[0], pair[1]):
            words[q >> 6] |= 1 << (q & 63)
        rows.append({"row_index": fake_idx, "cap": ub + 1, "dim": 2, "words": tuple(words), "points": [pivot, pair[0], pair[1]], "manual": "pivot_pair"})
        fake_idx -= 1
    return rows


def scan_violations(binary: Path, counts: Dict[int, int], max_add: int, active_keys: set | None = None, pivot: int | None = None) -> Dict:
    """Scan binary rows and return top violated rows with masks for CEGAR."""
    heap = []
    viol_count = 0
    excess_total = 0
    max_excess = 0
    cap_hist_viol = Counter()
    dim_hist_viol = Counter()
    rows_checked = 0
    t0 = time.time()
    items = [(int(p), int(m)) for p, m in counts.items() if m]
    for idx, cap, dim, words in load_binary_rows(binary):
        rows_checked += 1
        occ = 0
        for p, m in items:
            if bit_in(words, p):
                occ += m
        if occ > cap:
            viol_count += 1
            excess = occ - cap
            excess_total += excess
            max_excess = max(max_excess, excess)
            cap_hist_viol[cap] += 1
            dim_hist_viol[dim] += 1
            key = (cap, words)
            if active_keys is not None and key in active_keys:
                continue
            # Prefer high excess, then lower cap, then lower dimension and compact rows.
            score = (excess, -cap, -dim, -popcount_words(words), -idx)
            if len(heap) < max_add:
                heapq.heappush(heap, (score, idx, cap, dim, words, occ))
            elif score > heap[0][0]:
                heapq.heapreplace(heap, (score, idx, cap, dim, words, occ))
    selected = []
    for score, idx, cap, dim, words, occ in sorted(heap, reverse=True):
        selected.append({"row_index": int(idx), "cap": int(cap), "dim": int(dim), "occ": int(occ), "excess": int(occ - cap), "popcount": popcount_words(words), "words": [int(w) for w in words]})
    return {
        "rows_checked": rows_checked,
        "violation_count": viol_count,
        "excess_total": excess_total,
        "max_excess": max_excess,
        "cap_hist_violated": dict(sorted((int(k), int(v)) for k, v in cap_hist_viol.items())),
        "dim_hist_violated": dict(sorted((int(k), int(v)) for k, v in dim_hist_viol.items())),
        "selected_violations": selected,
        "elapsed_sec": time.time() - t0,
    }


def dominance_reduce(rows: List[Dict], pivot: int, pivot_mult: int, max_rows_for_pairwise: int = 12000) -> Tuple[List[Dict], Dict]:
    if len(rows) > max_rows_for_pairwise:
        return rows, {"applied": False, "reason": "too_many_rows", "rows": len(rows)}
    # Keep rows that are not strict subsets of another row with the same adjusted RHS.
    by_rhs: Dict[int, List[int]] = {}
    for i, r in enumerate(rows):
        rhs = row_rhs(r["cap"], r["words"], pivot, pivot_mult)
        by_rhs.setdefault(rhs, []).append(i)
    drop = set()
    for rhs, idxs in by_rhs.items():
        # Sort large masks first so supersets are considered early.
        idxs = sorted(idxs, key=lambda i: -popcount_words(rows[i]["words"]))
        for pos, i in enumerate(idxs):
            if i in drop:
                continue
            wi = rows[i]["words"]
            for j in idxs[:pos]:
                if j in drop:
                    continue
                wj = rows[j]["words"]
                # wi subset wj -> row i redundant.
                if all((wi[k] & ~wj[k]) == 0 for k in range(8)):
                    drop.add(i)
                    break
    kept = [r for i, r in enumerate(rows) if i not in drop]
    return kept, {"applied": True, "before": len(rows), "after": len(kept), "dropped": len(drop)}


def solve_active(rows: List[Dict], pivot: int, length: int, pivot_mult: int, time_limit: float, workers: int, hint_counts: Dict[int, int] | None = None, fixed_counts: Dict[int, int] | None = None) -> Dict:
    if cp_model is None:
        raise RuntimeError("ortools not available")
    model = cp_model.CpModel()
    ub = length - 19
    if ub < 1:
        ub = 1
    variables = {}
    for p in range(1, 512):
        if p == pivot:
            continue
        if ub == 1:
            variables[p] = model.NewBoolVar(f"x_{p}")
        else:
            variables[p] = model.NewIntVar(0, ub, f"x_{p}")
    model.Add(sum(variables.values()) == length - pivot_mult)
    if fixed_counts is not None:
        for p, var in variables.items():
            model.Add(var == int(fixed_counts.get(p, 0)))
    # Individual one-dimensional Wang rows give this upper bound; also add pair
    # constraints manually to make quotient/lift semantics explicit.
    for r in initial_pair_rows(pivot, length, ub):
        add_constraint_record(model, variables, r, pivot, pivot_mult)
    for r in rows:
        add_constraint_record(model, variables, r, pivot, pivot_mult)
    if hint_counts:
        for p, v in hint_counts.items():
            if p != pivot and p in variables:
                model.AddHint(variables[p], int(v))
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.num_search_workers = int(workers)
    solver.parameters.random_seed = 19
    t0 = time.time()
    status = solver.Solve(model)
    elapsed = time.time() - t0
    status_name = solver.StatusName(status)
    sol_counts = None
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol_counts = {p: int(solver.Value(var)) for p, var in variables.items() if int(solver.Value(var))}
        sol_counts[pivot] = pivot_mult
    return {
        "status": status_name,
        "feasible": status in (cp_model.OPTIMAL, cp_model.FEASIBLE),
        "solution_counts": sol_counts,
        "objective": solver.ObjectiveValue() if status in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None,
        "wall_time_sec": solver.WallTime(),
        "elapsed_sec": elapsed,
        "conflicts": solver.NumConflicts(),
        "branches": solver.NumBranches(),
    }


def run_cegar(args):
    OUTDIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    binary = Path(args.binary)
    header = binary_header(binary)
    pivot = int(args.pivot)
    length = int(args.length)
    pivot_mult = int(args.pivot_mult)
    ub = max(1, length - 19)

    active: List[Dict] = []
    active_keys = set()
    # Initial constraints: use only manual pair rows unless requested binary rows are small enough.
    init_cap_hist = Counter(); init_dim_hist = Counter()
    if args.initial_binary_max_cap >= 0:
        for idx, cap, dim, words in load_binary_rows(binary):
            rhs = cap - (pivot_mult if bit_in(words, pivot) else 0)
            if rhs < 0:
                r = canonical_row(idx, cap, dim, words)
            elif rhs > args.initial_binary_max_cap:
                continue
            if dim > args.initial_binary_max_dim:
                continue
            # Skip one-dimensional rows: variable domains encode them.
            if popcount_words(words) <= 1:
                continue
            key = (cap, words)
            if key not in active_keys:
                r = canonical_row(idx, cap, dim, words)
                active.append(r); active_keys.add(key)
                init_cap_hist[cap] += 1; init_dim_hist[dim] += 1
            if args.initial_row_limit and len(active) >= args.initial_row_limit:
                break
    if args.apply_dominance:
        active, dom0 = dominance_reduce(active, pivot, pivot_mult)
        active_keys = {(r["cap"], r["words"]) for r in active}
    else:
        dom0 = {"applied": False}

    fixed_counts = None
    if getattr(args, "force_multiset", ""):
        fm = parse_multiset_arg(args.force_multiset)
        fc = mult_counter(fm)
        if fc.get(pivot, 0) != pivot_mult:
            raise ValueError(f"forced multiset has pivot count {fc.get(pivot,0)} but pivot_mult={pivot_mult}")
        fc.pop(pivot, None)
        fixed_counts = {int(k): int(v) for k, v in fc.items()}

    summary = {
        "schema": "pivot_fixed_full_wang_cegar_v1",
        "binary": header,
        "pivot": pivot,
        "length": length,
        "pivot_mult": pivot_mult,
        "variable_upper_bound": ub,
        "force_multiset": getattr(args, "force_multiset", ""),
        "fixed_nonpivot_count": (sum(fixed_counts.values()) if fixed_counts is not None else None),
        "initial_binary_max_cap_rhs": args.initial_binary_max_cap,
        "initial_binary_max_dim": args.initial_binary_max_dim,
        "initial_row_limit": args.initial_row_limit,
        "initial_active_rows": len(active),
        "initial_cap_hist": dict(sorted((int(k), int(v)) for k, v in init_cap_hist.items())),
        "initial_dim_hist": dict(sorted((int(k), int(v)) for k, v in init_dim_hist.items())),
        "initial_dominance": dom0,
        "iterations": [],
        "final_status": "running",
    }
    hint = None
    for it in range(args.iterations):
        solve = solve_active(active, pivot, length, pivot_mult, args.solve_timeout, args.workers, hint, fixed_counts)
        entry = {"iteration": it, "active_rows": len(active), "solve": {k: v for k, v in solve.items() if k != "solution_counts"}}
        if not solve["feasible"]:
            if solve.get("status") == "INFEASIBLE":
                entry["status"] = "active_infeasible"
                summary["iterations"].append(entry)
                summary["final_status"] = "active_infeasible"
            else:
                entry["status"] = "active_unknown"
                summary["iterations"].append(entry)
                summary["final_status"] = "active_unknown"
            break
        counts = solve["solution_counts"]
        assert counts is not None
        selected = sorted([p for p, m in counts.items() for _ in range(m)])
        entry["candidate_multiset"] = selected
        entry["candidate_distinct_count"] = len(counts)
        entry["candidate_max_multiplicity"] = max(counts.values()) if counts else 0
        scan = scan_violations(binary, counts, args.add_per_iter, active_keys, pivot)
        entry["scan"] = {k: v for k, v in scan.items() if k != "selected_violations"}
        entry["selected_violation_rows"] = scan["selected_violations"][:10]
        summary["iterations"].append(entry)
        if scan["violation_count"] == 0:
            entry["status"] = "candidate_satisfies_checked_binary"
            summary["final_status"] = "candidate_satisfies_checked_binary"
            break
        added = 0
        for v in scan["selected_violations"]:
            words = tuple(int(w) for w in v["words"])
            key = (int(v["cap"]), words)
            if key in active_keys:
                continue
            r = canonical_row(int(v["row_index"]), int(v["cap"]), int(v["dim"]), words)
            active.append(r); active_keys.add(key); added += 1
        entry["added_rows"] = added
        if args.apply_dominance and (it + 1) % args.dominance_every == 0:
            active, dom = dominance_reduce(active, pivot, pivot_mult)
            active_keys = {(r["cap"], r["words"]) for r in active}
            entry["dominance"] = dom
        if added == 0:
            summary["final_status"] = "violations_seen_but_no_new_rows_added"
            break
        hint = counts
    if summary["final_status"] == "running":
        summary["final_status"] = "iteration_limit_reached"
    summary["final_active_rows"] = len(active)
    summary["elapsed_sec"] = time.time() - t0
    # Save active rows compactly enough for later replay.
    active_path = Path(args.out).with_suffix(".active_rows.jsonl")
    with open(active_path, "w") as f:
        for r in active:
            f.write(json.dumps({"row_index": r.get("row_index"), "cap": r["cap"], "dim": r["dim"], "words": [int(w) for w in r["words"]]}) + "\n")
    summary["active_rows_path"] = str(active_path)
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "final_status": summary["final_status"],
        "iterations": len(summary["iterations"]),
        "final_active_rows": summary["final_active_rows"],
        "elapsed_sec": summary["elapsed_sec"],
        "out": str(args.out),
        "last": summary["iterations"][-1] if summary["iterations"] else None,
    }, indent=2, sort_keys=True))


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("derive-rank2-control")
    p.add_argument("--out", type=Path, default=OUTDIR / "pivot17_rank23_transformed_control.json")

    p = sub.add_parser("check")
    p.add_argument("--binary", type=Path, required=True)
    p.add_argument("--multiset", required=True)
    p.add_argument("--length", type=int, required=True)
    p.add_argument("--out", type=Path, required=True)

    p = sub.add_parser("cegar")
    p.add_argument("--binary", type=Path, required=True)
    p.add_argument("--pivot", type=int, required=True)
    p.add_argument("--length", type=int, required=True)
    p.add_argument("--pivot-mult", type=int, default=1)
    p.add_argument("--iterations", type=int, default=20)
    p.add_argument("--solve-timeout", type=float, default=30.0)
    p.add_argument("--workers", type=int, default=8)
    p.add_argument("--add-per-iter", type=int, default=200)
    p.add_argument("--initial-binary-max-cap", type=int, default=-1, help="include rows whose adjusted rhs <= this; -1 means none")
    p.add_argument("--initial-binary-max-dim", type=int, default=9)
    p.add_argument("--initial-row-limit", type=int, default=0)
    p.add_argument("--apply-dominance", action="store_true")
    p.add_argument("--dominance-every", type=int, default=5)
    p.add_argument("--force-multiset", default="", help="optional full A multiset/counts to force while using the same CEGAR/scan machinery")
    p.add_argument("--out", type=Path, required=True)

    args = ap.parse_args()
    if args.cmd == "derive-rank2-control":
        rec = derive_rank2_pivot17_control(args.out)
        print(json.dumps({"status": "ok", "out": str(args.out), "rank": rec["rank"], "selected_A": rec["selected_A"], "verified": rec["full_tensor_verified_after_transform"], "duplicates": rec["a_multiplicity_hist"]}, indent=2, sort_keys=True))
    elif args.cmd == "check":
        ms = parse_multiset_arg(args.multiset)
        res = check_multiset(args.binary, ms, args.length)
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(res, indent=2, sort_keys=True) + "\n")
        print(json.dumps({"status": "ok", "out": str(args.out), "passed": res["passed"], "violations": res["violation_count"], "rows": res["rows_checked"], "elapsed_sec": res["elapsed_sec"]}, indent=2, sort_keys=True))
    elif args.cmd == "cegar":
        run_cegar(args)


if __name__ == "__main__":
    main()
