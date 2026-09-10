#!/usr/bin/env python3
r"""analysis: recompute trace-certificate cross-coverage with saturation guards.

analysis's `trace_certificate_family_cuts.py` cross-applied certificate
consequences to stored supports without checking whether the target support
actually saturates every rank-9 contraction in the certificate guard.  This
script repairs the statistic only at the reporting/evaluation layer.  The CP-SAT
encoding used the guards, so this does not invalidate those searches.
"""
from __future__ import annotations

import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from complete_core_and_transversal import ROOT  # noqa: E402
from trace_dependency_family import dot8, load_candidate_supports  # noqa: E402

OUTDIR = ROOT / "workspace/data/neighborhood_repair"
CERTCUT_PATH = ROOT / "workspace/data/trace_dependency_cuts/trace_certificate_family_cuts_augmented.json"
AUG_EVAL_PATH = ROOT / "workspace/data/trace_dependency_cuts/aug_separator_support_trace_evaluation.json"
SEP_PATHS = [
    ROOT / "workspace/data/trace_dependency_cuts/separator_L15_certcuts_6r_180s.json",
    ROOT / "workspace/data/trace_dependency_cuts/separator_L15_augcertcuts_4r_240s.json",
]


def support_weight(A: Sequence[int], q: int) -> int:
    return sum(1 for p in A if dot8(int(q), int(p)))


def add_support(supports: List[dict], seen: set, name: str, A: Sequence[int], source: str, complete_wang_violations=None) -> None:
    if not A:
        return
    tup = tuple(sorted(int(p) for p in A))
    if len(tup) != 19 or len(set(tup)) != 19:
        return
    if tup in seen:
        return
    seen.add(tup)
    supports.append({
        "name": name,
        "A_cols": list(tup),
        "source": source,
        "complete_wang_violations": complete_wang_violations,
    })


def load_targets(cert_data: dict) -> List[dict]:
    supports: List[dict] = []
    seen = set()
    for rec in load_candidate_supports():
        add_support(supports, seen, rec.get("name", f"stored_{len(supports)}"), rec.get("A_cols", []), rec.get("source", "load_candidate_supports"), rec.get("complete_wang_violations"))
    if AUG_EVAL_PATH.exists():
        data = json.loads(AUG_EVAL_PATH.read_text())
        for ev in data.get("evaluations", []):
            add_support(supports, seen, ev.get("name", f"aug_eval_{len(supports)}"), ev.get("A_cols", []), str(AUG_EVAL_PATH), ev.get("complete_wang_violations"))
    for path in SEP_PATHS:
        if not path.exists():
            continue
        data = json.loads(path.read_text())
        for r in data.get("rounds", []):
            if "A_cols" in r:
                add_support(supports, seen, f"{path.stem}_round{r.get('round')}", r.get("A_cols", []), str(path), r.get("complete_wang_violations"))
    for cert in cert_data.get("certificates", []):
        if "source_support" in cert:
            add_support(supports, seen, f"cert_source_{cert.get('cert_index')}_{cert.get('source_name')}", cert.get("source_support", []), "certificate_source_support", cert.get("source_complete_wang_violations"))
    return supports


def consequence_on_active_cert(cert: dict, A: Sequence[int]) -> dict:
    by_p = {int(r["p"]): r for r in cert["class_records"]}
    cnt = Counter()
    forced_sum = 0
    local_inconsistent_examples = []
    free_examples = []
    forced_examples = []
    for p0 in A:
        p = int(p0)
        rec = by_p[p]
        cls = rec["class"]
        cnt[cls] += 1
        if cls == "forced":
            forced_sum ^= int(rec.get("forced_value", 0))
            if len(forced_examples) < 5:
                forced_examples.append({"p": p, "forced_value": int(rec.get("forced_value", 0))})
        elif cls == "inconsistent":
            if len(local_inconsistent_examples) < 5:
                local_inconsistent_examples.append({"p": p, "witness": rec.get("witness"), "witness_size": rec.get("witness_size")})
        elif cls == "free":
            if len(free_examples) < 5:
                free_examples.append(p)
    pure_parity_applicable = (cnt.get("free", 0) == 0 and cnt.get("inconsistent", 0) == 0)
    parity_hit = bool(pure_parity_applicable and forced_sum != int(cert.get("tensor_rhs_parity", 0)))
    local_hit = bool(cnt.get("inconsistent", 0) > 0)
    return {
        "support_class_counts": {str(k): int(v) for k, v in sorted(cnt.items())},
        "forced_sum": int(forced_sum),
        "tensor_rhs_parity": int(cert.get("tensor_rhs_parity", 0)),
        "pure_parity_applicable": pure_parity_applicable,
        "pure_parity_hit": parity_hit,
        "local_inconsistent_hit": local_hit,
        "hit": bool(parity_hit or local_hit),
        "hit_type": "local_inconsistent" if local_hit else ("pure_parity" if parity_hit else "none"),
        "local_inconsistent_examples": local_inconsistent_examples,
        "free_examples": free_examples,
        "forced_examples": forced_examples,
    }


def main() -> None:
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    cert_data = json.loads(CERTCUT_PATH.read_text())
    certs = cert_data.get("certificates", [])
    targets = load_targets(cert_data)
    records = []
    target_summaries = []
    cert_summaries = defaultdict(lambda: {"active_targets": 0, "hit_targets": 0, "local_hits": 0, "parity_hits": 0})
    for ti, target in enumerate(targets):
        A = [int(p) for p in target["A_cols"]]
        active_count = 0
        hit_count = 0
        local_hits = 0
        parity_hits = 0
        active_guard_size_hist = Counter()
        inactive_examples = []
        for ci, cert in enumerate(certs):
            G = [int(q) for q in cert.get("guard_qs", [])]
            weights = {q: support_weight(A, q) for q in G}
            active = all(w == 9 for w in weights.values())
            if not active:
                if len(inactive_examples) < 3:
                    inactive_examples.append({"cert_index": ci, "guard_qs": G, "guard_weights": weights})
                continue
            active_count += 1
            active_guard_size_hist[len(G)] += 1
            ev = consequence_on_active_cert(cert, A)
            cert_summaries[ci]["active_targets"] += 1
            if ev["hit"]:
                hit_count += 1
                cert_summaries[ci]["hit_targets"] += 1
                if ev["local_inconsistent_hit"]:
                    local_hits += 1
                    cert_summaries[ci]["local_hits"] += 1
                if ev["pure_parity_hit"]:
                    parity_hits += 1
                    cert_summaries[ci]["parity_hits"] += 1
                records.append({
                    "target_index": ti,
                    "target_name": target.get("name"),
                    "target_complete_wang_violations": target.get("complete_wang_violations"),
                    "cert_index": ci,
                    "cert_name": cert.get("source_name"),
                    "guard_qs": G,
                    "guard_weights": weights,
                    **ev,
                })
        target_summaries.append({
            "target_index": ti,
            "target_name": target.get("name"),
            "source": target.get("source"),
            "complete_wang_violations": target.get("complete_wang_violations"),
            "A_cols": A,
            "active_certificate_count": active_count,
            "hit_certificate_count": hit_count,
            "local_inconsistent_hit_count": local_hits,
            "pure_parity_hit_count": parity_hits,
            "active_guard_size_hist": {str(k): int(v) for k, v in sorted(active_guard_size_hist.items())},
            "inactive_guard_examples": inactive_examples,
        })
    payload = {
        "schema": "guarded_trace_certificate_coverage_v1",
        "elapsed_sec": round(time.time() - t0, 3),
        "field": "F2",
        "core": "E11 quotient core",
        "certificate_file": str(CERTCUT_PATH),
        "meaning": "Cross-certificate support consequences recomputed with target saturation guards. A certificate only applies to a target support if every guard contraction q has support weight w(q)=9 on that target.",
        "certificate_count": len(certs),
        "target_count": len(targets),
        "hit_record_count": len(records),
        "target_summaries": target_summaries,
        "hit_records": records,
        "summary": {
            "targets_with_active_certificate": sum(1 for t in target_summaries if t["active_certificate_count"] > 0),
            "targets_hit_guarded": sum(1 for t in target_summaries if t["hit_certificate_count"] > 0),
            "targets_hit_by_local_inconsistent": sum(1 for t in target_summaries if t["local_inconsistent_hit_count"] > 0),
            "targets_hit_by_pure_parity": sum(1 for t in target_summaries if t["pure_parity_hit_count"] > 0),
            "deduplicated_targets_with_active_certificate": sum(1 for t in target_summaries if t["active_certificate_count"] > 0),
            "deduplicated_targets_hit_guarded": sum(1 for t in target_summaries if t["hit_certificate_count"] > 0),
            "deduplicated_targets_hit_by_local_inconsistent": sum(1 for t in target_summaries if t["local_inconsistent_hit_count"] > 0),
            "deduplicated_targets_hit_by_pure_parity": sum(1 for t in target_summaries if t["pure_parity_hit_count"] > 0),
            "cert_summaries": {str(k): v for k, v in sorted(cert_summaries.items())},
        },
    }
    out = OUTDIR / "guarded_trace_certificate_coverage.json"
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "certificate_count": len(certs),
        "target_count": len(targets),
        "summary": payload["summary"],
        "elapsed_sec": payload["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
