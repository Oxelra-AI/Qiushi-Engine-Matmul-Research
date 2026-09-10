#!/usr/bin/env python3
r"""analysis: apply corrected trace tests to already-stored distinct near-misses.

This is not a global coverage search.  It reuses existing candidate A-supports
from analysis completion records to understand what the corrected trace equations
actually remove beyond saturated-domain linear membership and before rank-one
completion.
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path
from typing import Dict, List, Sequence

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import build_matmul_tensor_f2, gf2_linear_consistency  # noqa: E402
from corrected_trace_instrument import (  # noqa: E402
    NEAR_MISS,
    contraction_rank_data,
    support_trace_condition,
    trace_rows_for_support,
)

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/corrected_trace"


def consistency_for_support(T_core: np.ndarray, contractions: Dict[int, dict], support: Sequence[int]) -> dict:
    rows_tensor, _labels_t, nvars, _ = trace_rows_for_support(T_core, support, contractions, coefficient="correct", q_filter=[])
    con_t, rank_t, _ = gf2_linear_consistency(rows_tensor, nvars)
    rows_corr, _labels, _nvars, sat_qs = trace_rows_for_support(T_core, support, contractions, coefficient="correct")
    con_c, rank_c, cert_c = gf2_linear_consistency(rows_corr, nvars)
    one_q = support_trace_condition(T_core, support, contractions)
    return {
        "tensor_only_consistent": bool(con_t),
        "tensor_only_rank": int(rank_t),
        "corrected_trace_consistent": bool(con_c),
        "corrected_trace_rank": int(rank_c),
        "corrected_trace_rows": len(rows_corr),
        "corrected_trace_added_rows": len(rows_corr) - len(rows_tensor),
        "corrected_trace_contradiction_rows": int(cert_c.bit_count()) if cert_c is not None else 0,
        "saturated_rank9_qs": sat_qs,
        "saturated_rank9_count": len(sat_qs),
        "support_single_q_failed": one_q["single_q_trace_condition_failed"],
        "support_single_q_passed": one_q["single_q_trace_condition_passed"],
        "outside_span_dim_hist": one_q["outside_span_dim_hist"],
    }


def load_candidates() -> List[dict]:
    candidates: List[dict] = []
    # Current best analysis support is explicitly included.
    candidates.append({
        "name": "L15_12violation",
        "source": "explicit analysis best near-miss",
        "A_cols": list(NEAR_MISS),
        "complete_wang_violations": 12,
        "completion_status": "INFEASIBLE in analysis repaired rank-one completion",
    })
    batch_path = ROOT / "workspace/data/completion/distinct_candidate_completion_repaired.json"
    if batch_path.exists():
        batch = json.loads(batch_path.read_text())
        completion_by_name = {rec.get("label") or rec.get("name"): rec for rec in batch.get("completion_results", [])}
        seen = {tuple(NEAR_MISS)}
        for rec in batch.get("best_analyses", []):
            support = [int(x) for x in rec.get("A_cols", [])]
            if not support or tuple(support) in seen:
                continue
            seen.add(tuple(support))
            # The completion output may not share the same name field in all records.
            candidates.append({
                "name": rec.get("name", f"candidate_{len(candidates)}"),
                "source": rec.get("source"),
                "A_cols": support,
                "complete_wang_violations": rec.get("complete_wang_violations"),
                "violations_by_L": rec.get("violations_by_L"),
                "transversal_failures": rec.get("transversal_failures"),
                "quotient_rank_violations_size2": rec.get("quotient_rank_violations_size2"),
                "saturation": rec.get("saturation"),
                "completion_status": completion_by_name.get(rec.get("name"), {}).get("status"),
            })
    return candidates


def main() -> None:
    OUTDIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    T_core = build_matmul_tensor_f2()[1:, :, :].astype(np.uint8) % 2
    contractions = contraction_rank_data(T_core)
    candidates = load_candidates()
    records = []
    for idx, cand in enumerate(candidates):
        support = [int(x) for x in cand["A_cols"]]
        res = consistency_for_support(T_core, contractions, support)
        record = {k: v for k, v in cand.items() if k != "A_cols"}
        record.update({"index": idx, "A_cols": support, "corrected_trace": res})
        records.append(record)
        print(f"{idx:02d} {record['name']}: sat9={res['saturated_rank9_count']} trace_consistent={res['corrected_trace_consistent']} one_q_fail={res['support_single_q_failed']} wang_viol={cand.get('complete_wang_violations')}")

    by_trace = {"consistent": 0, "inconsistent": 0}
    one_q_fail = 0
    sat_hist = {}
    for rec in records:
        tr = rec["corrected_trace"]
        by_trace["consistent" if tr["corrected_trace_consistent"] else "inconsistent"] += 1
        one_q_fail += int(tr["support_single_q_failed"] > 0)
        sat_hist[str(tr["saturated_rank9_count"])] = sat_hist.get(str(tr["saturated_rank9_count"]), 0) + 1
    result = {
        "schema": "corrected_trace_batch_existing_candidates_v1",
        "meaning": "Corrected trace equations tested only on previously stored near-misses; all candidates remain Wang-inadmissible, so this is local evidence about the B/C compatibility filter, not a rank lower bound.",
        "candidate_count": len(records),
        "summary": {
            "corrected_trace_consistent": by_trace["consistent"],
            "corrected_trace_inconsistent": by_trace["inconsistent"],
            "support_level_one_q_fail_candidate_count": one_q_fail,
            "saturated_rank9_count_hist": sat_hist,
        },
        "records": records,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    out = OUTDIR / "corrected_trace_existing_candidates.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(out), "summary": result["summary"], "elapsed_sec": result["elapsed_sec"]}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
