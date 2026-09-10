#!/usr/bin/env python3
"""Batch extraction of corrected 3x3-shadow certificates for named near supports."""
from __future__ import annotations

import itertools
import json
import sys
from pathlib import Path
from typing import List, Sequence

S0908 = Path("scripts")
if str(S0908) not in sys.path:
    sys.path.insert(0, str(S0908))

from shadow_certificate_analysis import (  # type: ignore
    L15,
    TRACE_INCONSISTENT_9V,
    TRACE_CONSISTENT_9V,
    find_tight_rank9,
    build_labelled_shadow_system,
    gf2_rref_augmented_with_combo,
    extract_shadow_certificate,
    classify_all_directions,
    apply_classification_to_support,
    weights_for_guard,
)

OUT = Path("data/shadow_certificate/shadow_certificate_batch.json")


def consistency(support: Sequence[int], qs: Sequence[int]):
    A, b, _ = build_labelled_shadow_system(support, qs)
    c, r, ra, cert = gf2_rref_augmented_with_combo(A, b)
    return c, r, ra, cert


def find_first_minimal_q_subset(support: Sequence[int], tight: Sequence[int], max_k: int | None = None):
    for k in range(1, (max_k or len(tight)) + 1):
        checked = 0
        examples = []
        for sub in itertools.combinations(tight, k):
            checked += 1
            c, r, ra, cert = consistency(support, sub)
            if not c:
                examples.append(list(sub))
                if len(examples) >= 5:
                    break
        if examples:
            # Count all at this k for small spaces.
            total_bad = 0
            total = 0
            for sub in itertools.combinations(tight, k):
                total += 1
                c, _, _, _ = consistency(support, sub)
                if not c:
                    total_bad += 1
            return {"size": k, "examples": examples, "checked_until_first": checked, "total": total, "total_inconsistent": total_bad}
    return None


def analyze(label: str, support: Sequence[int], other_supports):
    tight = find_tight_rank9(support)
    c, r, ra, _ = consistency(support, tight)
    out = {"label": label, "support": list(map(int, support)), "tight_rank9": tight, "tight_count": len(tight), "full_consistent": bool(c), "rank": int(r), "augmented_rank": int(ra)}
    if not c:
        mini = find_first_minimal_q_subset(support, tight)
        out["minimal_subset"] = mini
        chosen = mini["examples"][0] if mini else tight
        for cname, qs in [("minimal", chosen), ("full", tight)]:
            cert = extract_shadow_certificate(support, qs)
            cert["source_support_label"] = label
            cert["certificate_label"] = f"{label}_{cname}"
            cls = classify_all_directions(cert)
            apps = []
            for olab, osup in other_supports:
                app = apply_classification_to_support(cls, osup)
                app["label"] = olab
                app["guard_weights"] = weights_for_guard(osup, cls["guard_lambdas"])
                app["guard_saturated"] = all(v == 9 for v in app["guard_weights"].values())
                apps.append(app)
            out[f"certificate_{cname}"] = {
                "guard": cert.get("guard_lambdas_used"),
                "row_count": cert.get("certificate_row_count"),
                "type_counts": cert.get("type_counts"),
                "tensor_rhs": cert.get("tensor_rhs"),
                "trace_rhs": cert.get("trace_rhs"),
                "classification_counts": cls["class_counts"],
                "forced_value_counts": cls["forced_value_counts"],
                "self_application": next(a for a in apps if a["label"] == label),
                "cross_applications": apps,
                "certificate_full": cert,
                "classification_records": cls["records"],
            }
    return out


def main():
    supports = [
        ("L15", L15),
        ("trace_inconsistent_9v", TRACE_INCONSISTENT_9V),
        ("trace_consistent_9v", TRACE_CONSISTENT_9V),
    ]
    results = []
    for lab, sup in supports:
        results.append(analyze(lab, sup, supports))
    payload = {"schema": "s0908_shadow_certificate_batch_v1", "field": "F2", "supports": results}
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    brief = []
    for r in results:
        b = {k: r[k] for k in ["label", "tight_count", "full_consistent", "rank", "augmented_rank"]}
        if "minimal_subset" in r:
            b["minimal_subset"] = r["minimal_subset"]
            b["minimal_cert"] = {k: r["certificate_minimal"][k] for k in ["guard", "row_count", "type_counts", "tensor_rhs", "classification_counts", "forced_value_counts", "self_application"]}
        brief.append(b)
    print(json.dumps({"out": str(OUT), "brief": brief}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
