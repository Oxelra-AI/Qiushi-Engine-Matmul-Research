#!/usr/bin/env python3
r"""analysis: label unresolved pencil-envelope budgets by their actual Wang row.

analysis marked candidate support line/budget pairs outside the simple block
pencil construction envelope.  This script does NOT classify them as infeasible.
It filters them through the labelled D^perp Wang occupation row first.  Many
outside-envelope budgets are already rejected by Wang because c00 > 19-L(D^perp);
only Wang-surviving labelled cases are meaningful local pencil questions.
"""
from __future__ import annotations

import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from all_types_wang_comparison import compute_dperp_key9, contraction_matrix, gf2_rank  # noqa: E402

ROOT = Path("research/research_record")
IN = ROOT / "workspace/data/pencil_repair/candidate_block_envelope_scan.json"
OUTDIR = ROOT / "workspace/data/core_incidence"


def build_e11_core() -> np.ndarray:
    T = np.zeros((8, 9, 9), dtype=np.uint8)
    idx = 0
    for i in range(3):
        for j in range(3):
            if i == 0 and j == 0:
                continue
            for k in range(3):
                # Same convention as analysis scripts: B coordinate 3*j+k,
                # C/output coordinate 3*i+k.
                T[idx, 3*j+k, 3*i+k] = 1
            idx += 1
    return T


def status_from_slack(slack: int) -> str:
    if slack < 0:
        return "already_rejected_by_Wang_Dperp"
    if slack == 0:
        return "Wang_Dperp_tight_survives"
    return "Wang_Dperp_slack_survives"


def main() -> None:
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    data = json.loads(IN.read_text())
    lut, meta = load_lut(ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl")
    core = CoreQuotient(1)
    T = build_e11_core()
    crank = {q: gf2_rank(contraction_matrix(T, q)) for q in range(1, 256)}

    support_results: Dict[str, dict] = {}
    global_counter = Counter()
    surviving_questions = []

    for support_name, rec in data["results"].items():
        examples = rec.get("outside_examples_head", [])
        if len(examples) != int(rec.get("outside_block_envelope_count", len(examples))):
            raise RuntimeError(f"{support_name}: only head examples are stored; cannot safely classify all outside budgets")
        labelled = []
        by_key = Counter()
        for ex in examples:
            line = tuple(int(x) for x in ex["line"])
            q1, q2, q3 = line
            ranks = [int(crank[q]) for q in line]
            key9 = compute_dperp_key9(q1, q2, core)
            L = int(lut[key9])
            c00, c10, c01, c11 = [int(x) for x in ex["colors"]]
            budget = [c10, c01, c11]
            cap = 19 - L
            slack = cap - c00
            status = status_from_slack(slack)
            item = {
                "line": list(line),
                "rank_type_ordered": ranks,
                "rank_type_sorted": sorted(ranks),
                "colors_c00_c10_c01_c11": [c00, c10, c01, c11],
                "budget_c10_c01_c11": budget,
                "Dperp_key9": int(key9),
                "Dperp_L": L,
                "Dperp_cap_c00_max": cap,
                "Dperp_c00": c00,
                "Dperp_slack": slack,
                "Dperp_status": status,
                "outside_block_envelope": True,
            }
            labelled.append(item)
            key = (tuple(sorted(ranks)), tuple(budget), L, status)
            by_key[key] += 1
            global_counter[(support_name,) + key] += 1
            if slack >= 0:
                surviving_questions.append({"support": support_name, **item})
        support_results[support_name] = {
            "support": rec.get("support"),
            "outside_block_envelope_count": rec.get("outside_block_envelope_count"),
            "labelled_outside_count": len(labelled),
            "by_rank_budget_L_status": [
                {
                    "rank_type_sorted": list(k[0]),
                    "budget_c10_c01_c11": list(k[1]),
                    "Dperp_L": int(k[2]),
                    "Dperp_status": str(k[3]),
                    "count": int(v),
                }
                for k, v in sorted(by_key.items(), key=lambda kv: (kv[0][0], kv[0][1], kv[0][2], kv[0][3]))
            ],
            "labelled_outside_records": labelled,
            "wang_rejected_count": sum(1 for z in labelled if z["Dperp_slack"] < 0),
            "wang_surviving_count": sum(1 for z in labelled if z["Dperp_slack"] >= 0),
        }

    out = {
        "schema": "pencil_budget_wang_filter_v1",
        "source": str(IN),
        "meaning": "Outside the analysis block envelope is not infeasibility. A local pencil question is meaningful only after the labelled Dperp Wang row is satisfied.",
        "full_lut_coverage_ok": meta.get("coverage_ok"),
        "support_results": support_results,
        "surviving_labelled_local_questions": surviving_questions,
        "surviving_count": len(surviving_questions),
        "elapsed_sec": time.time() - t0,
    }
    path = OUTDIR / "pencil_budget_wang_filter.json"
    path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(path),
        "elapsed_sec": round(time.time() - t0, 3),
        "by_support": {
            k: {"outside": v["labelled_outside_count"], "wang_rejected": v["wang_rejected_count"], "wang_surviving": v["wang_surviving_count"]}
            for k, v in support_results.items()
        },
        "surviving_count": len(surviving_questions),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
