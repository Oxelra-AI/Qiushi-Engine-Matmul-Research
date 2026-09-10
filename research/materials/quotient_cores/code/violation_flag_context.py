#!/usr/bin/env python3
r"""analysis: flag/color contexts for complete-Wang violations of stored supports.

The target is not another list of violated rows, but the local incidence reason:
for each violated primal row U with dual flag D=U^perp, record the color counts
of the support under D, all proper subflag slacks, and whether the row is locally
primitive relative to those proper subflags.
"""
from __future__ import annotations

import json
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_all_mip import enumerate_subspace_keys  # noqa: E402
from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from flag_local_polytope import dual_perp_key8, max_n0_for_profile, dot, xor_combo  # noqa: E402
from wang_capacity_lazy import pack_basis, rref_basis, unpack_basis, in_rowspace  # noqa: E402

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/core_incidence"
RESCAN = OUTDIR / "complete_core_rescan_and_corrections.json"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"


def orthogonal_complement_basis(rows: Sequence[int], n: int = 8) -> List[int]:
    out: List[int] = []
    target = n - len(rref_basis(rows, n=n))
    for q in range(1, 1 << n):
        if all(dot(q, r) == 0 for r in rows):
            nb = list(rref_basis(out + [q], n=n))
            if len(nb) > len(out):
                out = nb
                if len(out) == target:
                    break
    if len(out) != target:
        raise RuntimeError(f"orthogonal complement rank failure: rows={rows} out={out}")
    return out


def support_color_counts(support: Sequence[int], dual_basis: Sequence[int]) -> List[int]:
    d = len(dual_basis)
    counts = [0] * (1 << d)
    for p in support:
        c = 0
        for i, q in enumerate(dual_basis):
            if dot(p, q):
                c |= 1 << i
        counts[c] += 1
    return counts


def line_L_by_annihilator_color(d: int, dual_basis: Sequence[int], L_by_primal_key: Dict[int, int]) -> Tuple[int, ...]:
    vals = []
    for r in range(1, 1 << d):
        qs = [xor_combo(dual_basis, m) for m in range(1, 1 << d) if dot(m, r) == 0]
        vals.append(int(L_by_primal_key[dual_perp_key8(qs)]))
    return tuple(vals)


def point_L_tuple(d: int, dual_basis: Sequence[int], L_by_primal_key: Dict[int, int]) -> Tuple[int, ...]:
    vals = []
    for m in range(1, 1 << d):
        q = xor_combo(dual_basis, m)
        vals.append(int(L_by_primal_key[dual_perp_key8([q])]))
    return tuple(vals)


def violation_context(v: dict, support: Sequence[int], L_by_primal_key: Dict[int, int]) -> dict:
    basisU = [int(x) for x in v["basis8"]]
    d = 8 - int(v["dim8"])
    D = orthogonal_complement_basis(basisU, n=8)
    counts = support_color_counts(support, D)
    if counts[0] != int(v["occupancy"]):
        raise RuntimeError(f"color zero count mismatch for key {v['key8']}: {counts[0]} vs {v['occupancy']}")
    point_L = point_L_tuple(d, D, L_by_primal_key)
    line_L = line_L_by_annihilator_color(d, D, L_by_primal_key) if d >= 2 else tuple()
    max_n0, witness = max_n0_for_profile(d, tuple(point_L), tuple(line_L)) if d in (2, 3) else (-1, None)
    cap = 19 - int(v["L"])

    point_slacks = []
    for m in range(1, 1 << d):
        w = sum(counts[c] for c in range(1 << d) if dot(m, c))
        point_slacks.append({
            "dual_mask": m,
            "q": xor_combo(D, m),
            "L": int(point_L[m - 1]),
            "outside_count_w": int(w),
            "slack_w_minus_L": int(w - point_L[m - 1]),
        })
    line_slacks = []
    if d >= 2:
        for r in range(1, 1 << d):
            occ = counts[0] + counts[r]
            L = int(line_L[r - 1])
            line_slacks.append({
                "annihilator_nonzero_color": r,
                "L": L,
                "occupancy_n0_plus_nr": int(occ),
                "cap": int(19 - L),
                "slack_cap_minus_occ": int((19 - L) - occ),
            })
    return {
        "key8": int(v["key8"]),
        "dim8": int(v["dim8"]),
        "L": int(v["L"]),
        "cap": cap,
        "occupancy_n0": int(v["occupancy"]),
        "excess": int(v["excess"]),
        "dual_dimension": d,
        "dual_basis": D,
        "color_counts": counts,
        "point_L": list(point_L),
        "line_L_by_annihilator_color": list(line_L),
        "proper_subflag_max_n0": int(max_n0),
        "row_adds_information_relative_to_proper_subflags": bool(max_n0 > cap) if max_n0 >= 0 else None,
        "proper_subflag_witness_at_max_n0": None if witness is None else list(witness),
        "point_slacks": point_slacks,
        "line_slacks": line_slacks,
        "minimum_proper_point_slack": min((z["slack_w_minus_L"] for z in point_slacks), default=None),
        "minimum_proper_line_slack": min((z["slack_cap_minus_occ"] for z in line_slacks), default=None),
        "same_as_selected_span": bool(v.get("same_as_selected_span", False)),
    }


def main() -> None:
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    data = json.loads(RESCAN.read_text())
    lut, meta = load_lut(LUT_PATH)
    core = CoreQuotient(1)
    print("Building core L lookup...")
    keys8 = enumerate_subspace_keys(8)
    L_by_primal_key = {int(k): int(lut[core.key9_from_key8(int(k))]) for k in keys8}

    out_supports = {}
    for name, scan in data["support_scans"].items():
        support = [int(x) for x in scan["support"]]
        contexts = [violation_context(v, support, L_by_primal_key) for v in scan["violations"]]
        by = Counter((c["dim8"], c["L"], c["dual_dimension"], c["row_adds_information_relative_to_proper_subflags"], c["minimum_proper_point_slack"], c["minimum_proper_line_slack"]) for c in contexts)
        out_supports[name] = {
            "support": support,
            "complete_violation_count": len(contexts),
            "contexts": contexts,
            "summary_by_dim_L_primitive_and_min_slacks": [
                {"dim8": k[0], "L": k[1], "dual_dimension": k[2], "row_adds_information": k[3], "min_point_slack": k[4], "min_line_slack": k[5], "count": int(v)}
                for k, v in sorted(by.items(), key=lambda kv: (kv[0][0], kv[0][1], str(kv[0][3]), kv[0][4] if kv[0][4] is not None else -99, kv[0][5] if kv[0][5] is not None else -99))
            ],
            "primitive_violation_count": sum(1 for c in contexts if c["row_adds_information_relative_to_proper_subflags"]),
        }

    result = {
        "schema": "violation_flag_context_v1",
        "field": "F2",
        "meaning": "Contexts for complete Wang violations; local primitive status does not by itself prove global infeasibility.",
        "full_lut_coverage_ok": meta.get("coverage_ok"),
        "support_contexts": out_supports,
        "elapsed_sec": time.time() - t0,
    }
    path = OUTDIR / "violation_flag_context.json"
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(path),
        "elapsed_sec": round(time.time() - t0, 3),
        "support_violation_counts": {k: v["complete_violation_count"] for k, v in out_supports.items()},
        "primitive_violation_counts": {k: v["primitive_violation_count"] for k, v in out_supports.items()},
        "base_summary": out_supports["54_base_9violation"]["summary_by_dim_L_primitive_and_min_slacks"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
