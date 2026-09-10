#!/usr/bin/env python3
"""analysis: evaluate new trace-cut CP-SAT supports with corrected trace systems."""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import List

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import (  # noqa: E402
    ROOT,
    build_core_constraints,
    complete_core_wang_scan,
    saturation_domains,
    transversal_failures,
)
from candidate_source_qcut_scan import eval_candidate_sources  # noqa: E402
from quotient_rank_cuts import build_contractions, point_mask_for_q  # noqa: E402
from trace_compressed_support import build_compressed_system, full_system_status  # noqa: E402
from corrected_trace_instrument import contraction_rank_data  # noqa: E402
from trace_dependency_family import eval_support_local_dependency, trace_mask_correct  # noqa: E402
from dual_basis_instrument import gf2_mat_inv  # noqa: E402
from fixed_A_saturation import contraction_matrix, mat_rank_f2  # noqa: E402

OUTDIR = ROOT / "workspace/data/trace_dependency_cuts"


def load_supports(paths: List[Path]) -> List[dict]:
    out = []
    seen = set()
    for path in paths:
        d = json.loads(path.read_text())
        if "solution" in d and d["solution"].get("A_cols"):
            A = tuple(int(x) for x in d["solution"]["A_cols"])
            if A not in seen:
                seen.add(A)
                out.append({"name": f"{path.stem}_solution", "source": str(path), "A_cols": list(A)})
        for i, r in enumerate(d.get("rounds", [])):
            A0 = r.get("A_cols") or r.get("support")
            if A0:
                A = tuple(int(x) for x in A0)
                if A not in seen:
                    seen.add(A)
                    out.append({"name": f"{path.stem}_round{r.get('round', i)}", "source": str(path), "A_cols": list(A)})
    return out


def build_phi(T_core):
    phi = {}
    for q in range(1, 1 << T_core.shape[0]):
        M = contraction_matrix(T_core, q)
        if mat_rank_f2(M) == 9:
            inv = gf2_mat_inv(M)
            if inv is None:
                raise RuntimeError(q)
            phi[int(q)] = trace_mask_correct(inv)
    return phi


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--support-json", type=Path, action="append", required=True)
    ap.add_argument("--out", type=Path, default=OUTDIR / "new_support_trace_evaluation.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    supports = load_supports(args.support_json)
    lut, _ = load_lut(ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl")
    records, meta = build_core_constraints(CoreQuotient(1), lut)
    T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
    contractions_for_qscan = build_contractions(T_core)
    masks = {q: point_mask_for_q(q) for q in contractions_for_qscan}
    contractions_trace = contraction_rank_data(T_core)
    phi = build_phi(T_core)
    rank9_qs = sorted(phi)

    evals = []
    for sup in supports:
        A = [int(x) for x in sup["A_cols"]]
        print(f"evaluating {sup['name']} A={A}")
        scan = complete_core_wang_scan(sup["name"], A, 19, records, max_head=30)
        sat = saturation_domains(T_core, A)
        trans = transversal_failures(sat["sat_records"], sat["B_domains"], sat["C_domains"], 9, 9, max_report=20)
        qscan = eval_candidate_sources(sup["name"], A, contractions_for_qscan, masks, max_source_size=2, max_store=20)
        local_dep = eval_support_local_dependency(A, rank9_qs, phi, {p: None for p in range(1, 256)})
        comp = build_compressed_system(T_core, A, contractions_trace, None)
        full = full_system_status(T_core, A, contractions_trace, None)
        rec = {
            **sup,
            "distinct_A": len(set(A)),
            "complete_wang_violations": scan["complete_violation_count"],
            "max_excess": scan["max_excess"],
            "violations_by_L": scan["violations_by_full_lut_L"],
            "violations_by_dim8": scan["violations_by_dim8"],
            "violations_head": scan["violations_head"],
            "zero_domain_terms": len(sat["summary"]["zero_domain_terms"]),
            "linear_pass": sat["summary"]["linear_membership"]["necessary_linear_test_passed"],
            "affine_dim": sat["summary"]["linear_membership"].get("affine_solution_dimension_if_consistent"),
            "saturated_contractions": sat["summary"].get("saturated_contraction_count"),
            "transversal_failures": trans["failure_count_reported"],
            "quotient_rank_violations_size2": qscan["violated_guarded_instances"],
            "local_odd_dependency": local_dep,
            "compressed_trace": {k: comp[k] for k in ["q_count", "trace_functional_rank", "trace_dependency_count", "variables", "rows", "rank", "consistent"]},
            "compressed_trace_certificate": comp.get("certificate"),
            "full_trace": full,
        }
        print(f"  wang={rec['complete_wang_violations']} trans={rec['transversal_failures']} qviol={rec['quotient_rank_violations_size2']} comp_trace={rec['compressed_trace']['consistent']} full_trace={full['consistent']} sat9={comp['q_count']}")
        evals.append(rec)

    result = {
        "schema": "new_support_trace_evaluation_v1",
        "elapsed_sec": round(time.time() - t0, 3),
        "field": "F2",
        "core": "E11 quotient core",
        "support_sources": [str(p) for p in args.support_json],
        "support_count": len(evals),
        "evaluations": evals,
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(args.out), "support_count": len(evals), "elapsed_sec": result["elapsed_sec"]}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
