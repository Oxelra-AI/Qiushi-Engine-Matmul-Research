#!/usr/bin/env python3
"""analysis: all-Wang-row canonical lift-bit feasibility for one quotient support.

This is the proof-facing reconstruction of the A-side lift-bit check for a fixed
support.  It scans Wang's complete 9-dimensional subspace LUT directly.  It uses
basis membership, the analysis high-pivot quotient section, and point labels
p=1..255.  It does not use analysis exported masks.

The output records whether the support violates any q-containing full row and
whether the remaining graph/lift-bit PB system is feasible.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Sequence

ROOT = Path("research/research_record")
S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import unpack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

try:
    from ortools.sat.python import cp_model  # type: ignore
except Exception:
    cp_model = None

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUTDIR = ROOT / "workspace/data/quotient_lift"
OUTDIR.mkdir(parents=True, exist_ok=True)
PIVOTS = {"rank2": 17, "rank3": 273}
PEER_RANK2_SUPPORT = [1,3,9,33,99,128,132,144,148,160,184,189,192,198,209,215,224,249,254]


def sha_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def section_lift(qpoint: int, pivot: int) -> int:
    h = pivot.bit_length() - 1
    low = qpoint & ((1 << h) - 1)
    high = (qpoint >> h) << (h + 1)
    return low | high


def reduce_by_pairs(x: int, pairs: Sequence[tuple[int, int]]) -> int:
    y = int(x)
    for hb, b in pairs:
        if (y >> hb) & 1:
            y ^= b
            if y == 0:
                return 0
    return y


def in_span(x: int, pairs: Sequence[tuple[int, int]]) -> bool:
    return reduce_by_pairs(x, pairs) == 0


def parse_support(s: str) -> list[int]:
    return [int(x) for x in s.split(",") if x.strip()]


def build_constraints_all(lut: dict, pivot: int, support: list[int], row_limit: int | None = None, max_dim: int = 9, progress: int = 500000) -> dict:
    lifts = [(section_lift(p, pivot), section_lift(p, pivot) ^ pivot) for p in support]
    best: dict[tuple[int, int], tuple[int, dict]] = {}
    q_violations = []
    stats = Counter()
    cap_hist = Counter(); dim_hist = Counter(); active_hist = Counter(); dedup_cap_hist = Counter()
    t0 = time.time()
    for idx, (key, lb0) in enumerate(lut.items()):
        if row_limit is not None and idx >= row_limit:
            break
        if progress and idx and idx % progress == 0:
            print(f"  scanned {idx:,} rows, constraints={len(best):,}, qviol={len(q_violations)}, elapsed={time.time()-t0:.1f}s", flush=True)
        basis = unpack_basis(int(key))
        d = len(basis)
        if d > max_dim:
            stats["skipped_dim"] += 1
            continue
        lb = int(lb0)
        cap = 20 - lb
        if cap >= 20:
            stats["skipped_cap_ge_20"] += 1
            continue
        if cap < 0:
            stats["negative_cap_rows"] += 1
            if len(q_violations) < 20:
                q_violations.append({"kind": "negative_cap", "basis": list(map(int, basis)), "lb": lb, "cap": cap})
            continue
        stats["rows_used"] += 1
        cap_hist[cap] += 1; dim_hist[d] += 1
        pairs = tuple((int(b).bit_length() - 1, int(b)) for b in basis if b)
        contains_q = in_span(pivot, pairs)
        if contains_q:
            stats["q_containing"] += 1
            occ = 1
            pts = []
            for p, (a0, a1) in zip(support, lifts):
                b0 = in_span(a0, pairs); b1 = in_span(a1, pairs)
                if b0 != b1:
                    raise AssertionError(("q-containing both-lift mismatch", pivot, p, basis, b0, b1))
                if b0:
                    occ += 1; pts.append(p)
            if occ > cap:
                stats["q_violations"] += 1
                if len(q_violations) < 50:
                    q_violations.append({"kind": "q_containing", "idx": idx, "dim": d, "lb": lb, "cap20": cap, "occ_with_q": occ, "quotient_cap": cap-1, "projected_points": pts, "basis": list(map(int, basis))})
            continue
        stats["nonq"] += 1
        zmask = 0; omask = 0; active = 0
        for i, (a0, a1) in enumerate(lifts):
            b0 = in_span(a0, pairs); b1 = in_span(a1, pairs)
            if b0 and b1:
                raise AssertionError(("non-q contains both lifts", pivot, support[i], basis))
            if b0:
                zmask |= 1 << i; active += 1
            elif b1:
                omask |= 1 << i; active += 1
        if active == 0:
            stats["nonq_no_active"] += 1
            continue
        active_hist[active] += 1
        if active <= cap:
            stats["nonq_tautological"] += 1
            continue
        key2 = (zmask, omask)
        old = best.get(key2)
        if old is None or cap < old[0]:
            best[key2] = (cap, {"idx": idx, "dim": d, "lb": lb, "cap20": cap, "active": active, "basis": list(map(int, basis))})
    constraints = [(z, o, csrc[0]) for (z, o), csrc in best.items()]
    constraints.sort(key=lambda t: (t[2], (t[0]|t[1]).bit_count(), t[0], t[1]))
    for _, _, cap in constraints:
        dedup_cap_hist[cap] += 1
    return {
        "constraints": constraints,
        "source": {k: v[1] for k, v in best.items()},
        "q_violations": q_violations,
        "stats": {str(k): int(v) for k, v in sorted(stats.items())},
        "cap_hist_used": {str(k): int(v) for k, v in sorted(cap_hist.items())},
        "dim_hist_used": {str(k): int(v) for k, v in sorted(dim_hist.items())},
        "active_hist_nonq": {str(k): int(v) for k, v in sorted(active_hist.items())},
        "dedup_constraint_count": len(constraints),
        "dedup_cap_hist": {str(k): int(v) for k, v in sorted(dedup_cap_hist.items())},
    }


def solve(bundle: dict, support: list[int], time_limit: float) -> dict:
    if cp_model is None:
        return {"status": "UNKNOWN", "reason": "ortools_unavailable"}
    model = cp_model.CpModel()
    xs = [model.NewBoolVar(f"e_{p}") for p in support]
    for zmask, omask, cap in bundle["constraints"]:
        terms = []
        for i in range(len(support)):
            if (zmask >> i) & 1:
                terms.append(1 - xs[i])
            if (omask >> i) & 1:
                terms.append(xs[i])
        model.Add(sum(terms) <= int(cap))
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.num_search_workers = 8
    status = solver.Solve(model)
    rec = {"status": solver.StatusName(status), "wall_time": solver.WallTime(), "num_conflicts": solver.NumConflicts(), "num_branches": solver.NumBranches(), "constraint_count": len(bundle["constraints"])}
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        bits = [int(solver.Value(x)) for x in xs]
        rec["assignment_bits_in_support_order"] = bits
        rec["assignment"] = {str(p): bits[i] for i, p in enumerate(support)}
    return rec


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot-name", choices=["rank2", "rank3"], default="rank2")
    ap.add_argument("--support", type=str, default=",".join(map(str, PEER_RANK2_SUPPORT)))
    ap.add_argument("--row-limit", type=int, default=0)
    ap.add_argument("--max-dim", type=int, default=9)
    ap.add_argument("--time-limit", type=float, default=120.0)
    args = ap.parse_args()
    support = parse_support(args.support)
    pivot = PIVOTS[args.pivot_name]
    t0 = time.time()
    print(f"Loading LUT {LUT_PATH}", flush=True)
    lut, meta = load_lut(LUT_PATH)
    print(f"Loaded {len(lut):,} LUT rows; scanning max_dim={args.max_dim}, row_limit={args.row_limit or 'none'}", flush=True)
    bundle = build_constraints_all(lut, pivot, support, row_limit=(args.row_limit or None), max_dim=args.max_dim)
    print(json.dumps({k: bundle[k] for k in ["stats", "cap_hist_used", "dim_hist_used", "active_hist_nonq", "dedup_constraint_count", "dedup_cap_hist"]}, indent=2, sort_keys=True), flush=True)
    if bundle["q_violations"]:
        print(f"q-containing violations: {len(bundle['q_violations'])} (head stored)", flush=True)
        sol = {"status": "INFEASIBLE_BY_Q_CONTAINING_ROW"}
    else:
        print("Solving deduplicated PB lift-bit system...", flush=True)
        sol = solve(bundle, support, args.time_limit)
        print(json.dumps(sol, indent=2, sort_keys=True)[:4000], flush=True)
    head = []
    for z,o,c in bundle["constraints"][:50]:
        src = bundle["source"].get((z,o), {})
        head.append({
            "cap": c,
            "active": int((z|o).bit_count()),
            "eps0_points": [support[i] for i in range(len(support)) if (z>>i)&1],
            "eps1_points": [support[i] for i in range(len(support)) if (o>>i)&1],
            "source": src,
        })
    out = {
        "schema": "s0908_all_wang_lift_bit_feasibility_v1",
        "source_lut": str(LUT_PATH),
        "source_lut_sha256": sha_file(LUT_PATH),
        "lut_coverage_ok": meta.get("coverage_ok"),
        "pivot_name": args.pivot_name,
        "pivot": pivot,
        "support": support,
        "support_label": "peer_rank2_wang_admissible" if args.pivot_name == "rank2" and support == PEER_RANK2_SUPPORT else "custom",
        "row_limit": args.row_limit or None,
        "max_dim": args.max_dim,
        "stats": bundle["stats"],
        "cap_hist_used": bundle["cap_hist_used"],
        "dim_hist_used": bundle["dim_hist_used"],
        "active_hist_nonq": bundle["active_hist_nonq"],
        "dedup_constraint_count": bundle["dedup_constraint_count"],
        "dedup_cap_hist": bundle["dedup_cap_hist"],
        "q_violations_head": bundle["q_violations"],
        "constraints_head": head,
        "solve": sol,
        "elapsed_sec": time.time() - t0,
    }
    suffix = f"{args.pivot_name}_maxdim{args.max_dim}" + (f"_limit{args.row_limit}" if args.row_limit else "")
    out_path = OUTDIR / f"allrows_lift_bit_feasibility_{suffix}.json"
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(f"Saved {out_path} in {out['elapsed_sec']:.1f}s", flush=True)


if __name__ == "__main__":
    main()
