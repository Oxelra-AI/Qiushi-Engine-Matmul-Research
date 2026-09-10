#!/usr/bin/env python3
r"""analysis: five-bit signature count relaxation for the min4 shadow relation.

The min4 shadow row-combination certificate has a special form:
  * guard lambdas: 43, 53, 157, 234;
  * tensor masks nonzero only in core slices 0 and 3, both equal to h_53=396;
  * h_43 + h_53 + h_157 + h_234 = 0 over F2.

Consequently the guarded family relation depends on a direction p only through
five incidence bits against masks [9, 43, 53, 157, 234].  This script compresses
A-support variables from 255 directions to 32 signature-class counts, adds the
exact family conditions, and adds Wang occupation inequalities only for preimages
of subspaces of the 5-dimensional signature quotient.  Rows that distinguish
points inside one signature class are deliberately omitted: feasibility is only a
relaxation, not complete Wang feasibility and not B/C completion.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

S0904_SCRIPTS = Path("scripts")
if str(S0904_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(S0904_SCRIPTS))
S0908_SCRIPTS = Path("scripts")
if str(S0908_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(S0908_SCRIPTS))

from core_capacity_all_mip import enumerate_subspace_keys  # type: ignore  # noqa:E402
from core_capacity_from_wang_lut import CoreQuotient  # type: ignore  # noqa:E402
from wang_capacity_lazy import pack_basis, rref_basis, subspace_points_from_basis, unpack_basis  # type: ignore  # noqa:E402
from shadow_certificate_analysis import gf2_rank  # type: ignore  # noqa:E402

ROOT = Path("research/research_record")
LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
CERT_PATH = ROOT / "workspace/data/shadow_certificate/target_certificate.json"
OUT_PATH = ROOT / "workspace/data/shadow_certificate/signature_count_relaxation.json"
S = 19
MASKS = [9, 43, 53, 157, 234]
MASK_NAMES = ["ell9", "q43", "q53", "q157", "q234"]
GUARD_SIG_BITS = [1, 2, 3, 4]


def popparity(x: int) -> int:
    return int(x.bit_count() & 1)


def mask_rank(masks: Sequence[int], n: int = 8) -> int:
    rows = []
    for m in masks:
        rows.append([(int(m) >> i) & 1 for i in range(n)])
    return gf2_rank(np.array(rows, dtype=np.uint8))


def signature(p: int) -> int:
    sig = 0
    for i, m in enumerate(MASKS):
        if popparity(int(p) & int(m)):
            sig |= 1 << i
    return sig


def load_lut() -> Tuple[Dict[int, int], dict]:
    with LUT_PATH.open("rb") as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload["lut"].items()}, payload.get("meta", {})


def signature_class_data(classification_records: Sequence[dict]) -> dict:
    by_sig_points: Dict[int, List[int]] = defaultdict(list)
    by_sig_records: Dict[int, List[dict]] = defaultdict(list)
    rec_by_p = {int(r["p"]): r for r in classification_records}
    for p in range(1, 256):
        sig = signature(p)
        by_sig_points[sig].append(p)
        by_sig_records[sig].append(rec_by_p[p])

    classes = []
    uniform_ok = True
    for sig in range(32):
        pts = by_sig_points.get(sig, [])
        recs = by_sig_records.get(sig, [])
        kinds = sorted({r["class"] for r in recs}) if recs else []
        vals = sorted({int(r.get("forced_value", -1)) for r in recs if r["class"] == "forced"})
        F_masks = sorted({int(r.get("F_mask", -1)) for r in recs})
        hit_counts = sorted({int(r.get("hit_count", -1)) for r in recs})
        if len(kinds) != 1 or (kinds and kinds[0] == "forced" and len(vals) != 1) or len(F_masks) != 1 or len(hit_counts) != 1:
            uniform_ok = False
        cls = kinds[0] if kinds else "zero_only"
        forced_value = vals[0] if cls == "forced" and vals else None
        classes.append({
            "sig": sig,
            "bits": [(sig >> i) & 1 for i in range(5)],
            "size_nonzero": len(pts),
            "points": pts,
            "class": cls,
            "forced_value": forced_value,
            "F_mask": F_masks[0] if F_masks else None,
            "hit_count": hit_counts[0] if hit_counts else 0,
        })
    return {"uniform_by_signature": uniform_ok, "classes": classes}


def source_signature_counts(support: Sequence[int]) -> Dict[str, int]:
    c = Counter(signature(p) for p in support)
    return {str(k): int(c.get(k, 0)) for k in range(32) if c.get(k, 0)}


def enumerate_signature_subspace_rows(lut: Dict[int, int]) -> Tuple[List[dict], dict]:
    """Rows for preimages of all subspaces U <= F2^5 under the signature map."""
    core = CoreQuotient(1)  # E11 pivot in the full 9-dimensional A slot.
    keys5 = enumerate_subspace_keys(5)
    rows = []
    by_dim5 = Counter(); by_dim8 = Counter(); by_L = Counter(); by_cap = Counter()
    for key5 in keys5:
        basis5 = list(unpack_basis(int(key5)))
        # wang_capacity_lazy.subspace_points_from_basis deliberately omits the zero
        # vector for support-occupancy rows.  Here we need the actual quotient
        # subspace U <= F2^5, including signature 0, because the preimage contains
        # the whole kernel of the five-bit signature map.
        U_pts = {0}
        for b in basis5:
            U_pts |= {x ^ b for x in list(U_pts)}
        # Preimage in F2^8: all 8-bit vectors with signature in U.  The zero
        # vector is harmless for the row span; support variables later count only
        # nonzero projective directions in the corresponding signature classes.
        pts8_all = [p for p in range(256) if signature(p) in U_pts]
        basis8 = rref_basis(pts8_all, n=8)
        key8 = pack_basis(basis8)
        key9 = core.key9_from_key8(key8)
        L = int(lut[int(key9)])
        cap = S - L
        sigs = sorted(int(s) for s in U_pts)
        rec = {
            "key5": int(key5),
            "dim5": int(key5 & 0xF),
            "basis5": basis5,
            "sigs": sigs,
            "basis8": list(basis8),
            "dim8": int(key8 & 0xF),
            "key8": int(key8),
            "key9": int(key9),
            "L": L,
            "cap": int(cap),
        }
        rows.append(rec)
        by_dim5[rec["dim5"]] += 1; by_dim8[rec["dim8"]] += 1; by_L[L] += 1; by_cap[cap] += 1
    meta = {"row_count": len(rows), "by_dim5": dict(sorted(by_dim5.items())), "by_dim8": dict(sorted(by_dim8.items())), "by_L": dict(sorted(by_L.items())), "by_cap": dict(sorted(by_cap.items()))}
    return rows, meta


def guard_weight_from_counts(counts: Sequence[int], bit: int) -> int:
    return sum(int(counts[s]) for s in range(32) if (s >> bit) & 1)


def parity_from_counts(counts: Sequence[int], class_data: dict) -> int:
    classes = class_data["classes"]
    total = 0
    for rec in classes:
        if rec["class"] == "forced" and int(rec.get("forced_value") or 0) == 1:
            total ^= (int(counts[int(rec["sig"])]) & 1)
    return total


def violated_rows_for_counts(counts: Sequence[int], rows: Sequence[dict]) -> List[dict]:
    out = []
    for r in rows:
        occ = sum(int(counts[s]) for s in r["sigs"])
        if occ > int(r["cap"]):
            rr = dict(r)
            rr.update({"occupancy": int(occ), "excess": int(occ - int(r["cap"]))})
            out.append(rr)
    out.sort(key=lambda z: (z["excess"], z["L"], z["dim5"], z["occupancy"]), reverse=True)
    return out


def solve_count_model(class_data: dict, rows: Sequence[dict], min_L: int, require_family: bool = True, max_solutions: int = 50, time_limit: float = 30.0) -> dict:
    from ortools.sat.python import cp_model

    classes = class_data["classes"]
    model = cp_model.CpModel()
    y = {}
    for rec in classes:
        sig = int(rec["sig"])
        y[sig] = model.NewIntVar(0, int(rec["size_nonzero"]), f"y_{sig:02d}")
    model.Add(sum(y.values()) == S)

    # Exact family-excluded conditions for min4 in signature counts.
    if require_family:
        for bit in GUARD_SIG_BITS:
            model.Add(sum(y[sig] for sig in range(32) if (sig >> bit) & 1) == 9)
        for rec in classes:
            if rec["class"] == "free":
                model.Add(y[int(rec["sig"])] == 0)
        forced1_terms = [y[int(rec["sig"])] for rec in classes if rec["class"] == "forced" and int(rec.get("forced_value") or 0) == 1]
        # Excluded family has opposite parity to tensor_rhs=1, hence parity 0.
        k = model.NewIntVar(0, S, "forced1_half")
        model.Add(sum(forced1_terms) - 2 * k == 0)

    used_rows = []
    for r in rows:
        if int(r["L"]) < min_L:
            continue
        cap = int(r["cap"])
        if cap >= S:
            continue
        model.Add(sum(y[s] for s in r["sigs"] if s in y) <= cap)
        used_rows.append(r)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.num_search_workers = 1 if max_solutions else 8

    solutions = []
    class Collector(cp_model.CpSolverSolutionCallback):
        def __init__(self):
            super().__init__()
            self.count = 0
        def OnSolutionCallback(self):
            self.count += 1
            if len(solutions) < max_solutions:
                counts = [int(self.Value(y[s])) for s in range(32)]
                solutions.append(counts)
            if self.count >= max_solutions:
                self.StopSearch()

    if max_solutions:
        cb = Collector()
        status = solver.SearchForAllSolutions(model, cb)
        seen_count = cb.count
    else:
        status = solver.Solve(model)
        seen_count = 1 if status in (cp_model.OPTIMAL, cp_model.FEASIBLE) else 0
        if seen_count:
            solutions.append([int(solver.Value(y[s])) for s in range(32)])

    status_name = solver.StatusName(status)
    sol_records = []
    for counts in solutions:
        nonzero = {str(i): int(v) for i, v in enumerate(counts) if v}
        sol_records.append({
            "nonzero_counts": nonzero,
            "support_total": int(sum(counts)),
            "guard_weights": {MASK_NAMES[bit]: int(guard_weight_from_counts(counts, bit)) for bit in GUARD_SIG_BITS},
            "forced1_parity": int(parity_from_counts(counts, class_data)),
            "violated_signature_rows": violated_rows_for_counts(counts, used_rows)[:10],
        })
    return {"min_L": min_L, "require_family": require_family, "used_signature_rows": len(used_rows), "status": status_name, "solutions_seen_limited": int(seen_count), "solutions_recorded": sol_records}


def summarize_source_against_signature_rows(label: str, support: Sequence[int], rows: Sequence[dict], class_data: dict) -> dict:
    counts = [0] * 32
    for p in support:
        counts[signature(p)] += 1
    viol = violated_rows_for_counts(counts, rows)
    return {
        "label": label,
        "support": [int(p) for p in support],
        "signature_counts": {str(i): int(v) for i, v in enumerate(counts) if v},
        "support_total": int(sum(counts)),
        "guard_weights": {MASK_NAMES[bit]: int(guard_weight_from_counts(counts, bit)) for bit in GUARD_SIG_BITS},
        "forced1_parity": int(parity_from_counts(counts, class_data)),
        "signature_row_violation_count_all_L": len(viol),
        "signature_row_violations_by_L": dict(sorted(Counter(int(v["L"]) for v in viol).items())),
        "signature_row_violations_head": viol[:20],
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=OUT_PATH)
    ap.add_argument("--time-limit", type=float, default=30.0)
    args = ap.parse_args()

    cert_payload = json.loads(CERT_PATH.read_text())
    classification_records = cert_payload["classification"]["records"]
    class_data = signature_class_data(classification_records)
    lut, lut_meta = load_lut()
    rows, rows_meta = enumerate_signature_subspace_rows(lut)

    # Sanity checks requested by the mathematical interpretation.
    h_masks = {lab["lambda"]: lab["h_mask"] for lab in cert_payload["certificate"]["used_labels_head"] if lab.get("type") == "trace"}
    h_relation = int(h_masks.get(43, 0) ^ h_masks.get(53, 0) ^ h_masks.get(157, 0) ^ h_masks.get(234, 0))
    tensor_masks = cert_payload["certificate"].get("tensor_coeff_masks_by_slice", [])
    source_support = cert_payload["support"]

    solves = []
    for min_L in [0, 12, 13, 14, 15]:
        solves.append(solve_count_model(class_data, rows, min_L=min_L, require_family=True, max_solutions=50, time_limit=args.time_limit))

    source_rows = summarize_source_against_signature_rows("trace_inconsistent_9v", source_support, rows, class_data)

    payload = {
        "schema": "s0908_signature_count_relaxation_v1",
        "field": "F2",
        "meaning": "Five-bit signature count relaxation for the min4 guarded shadow relation. Feasibility is weaker than complete Wang support feasibility and does not imply B/C completion.",
        "masks": MASKS,
        "mask_names": MASK_NAMES,
        "mask_rank_over_F2": int(mask_rank(MASKS, n=8)),
        "signature_class_uniformity": class_data["uniform_by_signature"],
        "signature_classes": class_data["classes"],
        "class_summary": {f"{cls}:{val}": int(cnt) for (cls, val), cnt in sorted(Counter((rec["class"], rec.get("forced_value")) for rec in class_data["classes"]).items(), key=lambda kv: str(kv[0]))},
        "source_signature_counts": source_signature_counts(source_support),
        "certificate_structure": {
            "guard_lambdas": cert_payload["certificate"].get("guard_lambdas_used"),
            "tensor_coeff_masks_by_slice": tensor_masks,
            "nonzero_tensor_slices": [i for i, m in enumerate(tensor_masks) if int(m) != 0],
            "h_masks_from_used_trace_rows": {str(k): int(v) for k, v in sorted(h_masks.items())},
            "h43_xor_h53_xor_h157_xor_h234": h_relation,
            "tensor_mask_equals_h53_on_nonzero_slices": bool(all((int(tensor_masks[i]) == int(h_masks.get(53, -1))) for i in range(len(tensor_masks)) if int(tensor_masks[i]) != 0)),
        },
        "lut_meta_coverage_ok": lut_meta.get("coverage_ok"),
        "signature_subspace_rows_meta": rows_meta,
        "source_against_signature_subspace_rows": source_rows,
        "count_model_results": solves,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    concise = {
        "out": str(args.out),
        "mask_rank_over_F2": payload["mask_rank_over_F2"],
        "uniform_by_signature": payload["signature_class_uniformity"],
        "certificate_structure": payload["certificate_structure"],
        "rows_meta": rows_meta,
        "source_signature_rows_violations": {
            "count": source_rows["signature_row_violation_count_all_L"],
            "by_L": source_rows["signature_row_violations_by_L"],
        },
        "count_model_results": [{"min_L": r["min_L"], "rows": r["used_signature_rows"], "status": r["status"], "seen": r["solutions_seen_limited"], "first_solution": (r["solutions_recorded"][0] if r["solutions_recorded"] else None)} for r in solves],
    }
    print(json.dumps(concise, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
