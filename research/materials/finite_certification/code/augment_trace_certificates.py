#!/usr/bin/env python3
"""analysis: augment corrected trace-certificate cut library with new supports."""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import List

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from trace_certificate_cuts import (  # noqa: E402
    build_e11_core_tensor,
    build_phi_vectors,
    build_trace_system,
    evaluate_on_support,
    extract_certificate,
)
from fixed_A_saturation import gf2_linear_consistency  # noqa: E402
from trace_dependency_family import load_candidate_supports  # noqa: E402

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/trace_dependency_cuts"
BASE = OUTDIR / "trace_certificate_family_cuts.json"


def extract_supports_from_json(path: Path) -> List[dict]:
    d = json.loads(path.read_text())
    out = []
    if "solution" in d and d["solution"].get("A_cols"):
        out.append({"name": f"{path.stem}_solution", "source": str(path), "A_cols": [int(x) for x in d["solution"]["A_cols"]], "complete_wang_violations": d["solution"].get("complete_wang_violations")})
    for i, r in enumerate(d.get("rounds", [])):
        A = r.get("A_cols") or r.get("support")
        if A:
            out.append({"name": f"{path.stem}_round{r.get('round', i)}", "source": str(path), "A_cols": [int(x) for x in A], "complete_wang_violations": r.get("complete_wang_violations")})
    for i, r in enumerate(d.get("evaluations", [])):
        A = r.get("A_cols")
        if A:
            out.append({"name": f"{path.stem}_{r.get('name', i)}", "source": str(path), "A_cols": [int(x) for x in A], "complete_wang_violations": r.get("complete_wang_violations")})
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", type=Path, default=BASE)
    ap.add_argument("--extra-support-json", type=Path, action="append", required=True)
    ap.add_argument("--out", type=Path, default=OUTDIR / "trace_certificate_family_cuts_augmented.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    base = json.loads(args.base.read_text())
    T_core = build_e11_core_tensor()
    phi = build_phi_vectors(T_core)
    existing_supports = {tuple(c["source_support"]): c for c in base.get("certificates", []) if c.get("source_support")}
    certs = list(base.get("certificates", []))

    extras = []
    for p in args.extra_support_json:
        extras.extend(extract_supports_from_json(p))
    added = []
    skipped = []
    for cand in extras:
        A = [int(x) for x in cand["A_cols"]]
        key = tuple(A)
        if key in existing_supports:
            skipped.append({"name": cand.get("name"), "reason": "support_already_has_certificate"})
            continue
        rows, labels, nvars = build_trace_system(T_core, A)
        ok, rank, cert_mask = gf2_linear_consistency(rows, nvars)
        if ok or cert_mask is None:
            skipped.append({"name": cand.get("name"), "reason": "corrected_trace_consistent", "rows": len(rows), "rank": int(rank)})
            continue
        cert = extract_certificate(labels, int(cert_mask), T_core, phi)
        self_eval = evaluate_on_support(cert, A)
        rec = {
            "cert_index": len(certs),
            "source_candidate_index": None,
            "source_name": cand.get("name"),
            "source": cand.get("source"),
            "source_complete_wang_violations": cand.get("complete_wang_violations"),
            "source_support": A,
            "full_trace_system_rows": len(rows),
            "full_trace_system_rank": int(rank),
            "source_self_evaluation": self_eval,
            **cert,
        }
        certs.append(rec)
        existing_supports[key] = rec
        added.append({"name": cand.get("name"), "guard_qs": len(cert["guard_qs"]), "class_summary": cert["class_summary"], "self": self_eval})
        print(f"added {cand.get('name')}: guard={len(cert['guard_qs'])} classes={cert['class_summary']} self={self_eval}")

    # Recompute a lightweight cross summary against old stored candidates plus extras.
    target_map = []
    seen = set()
    for c in load_candidate_supports() + extras:
        A = tuple(int(x) for x in c["A_cols"])
        if A in seen:
            continue
        seen.add(A)
        target_map.append(c)
    cross_hits = []
    for ci, cert in enumerate(certs):
        for tj, target in enumerate(target_map):
            ev = evaluate_on_support(cert, target["A_cols"])
            if ev["pure_parity_contradiction"] or ev["has_local_inconsistent_direction_under_guard"]:
                cross_hits.append({
                    "cert_index": ci,
                    "cert_name": cert.get("source_name"),
                    "target_index": tj,
                    "target_name": target.get("name"),
                    "target_complete_wang_violations": target.get("complete_wang_violations"),
                    **ev,
                })

    out = {
        **base,
        "schema": "trace_certificate_family_cuts_augmented_v1",
        "base_file": str(args.base),
        "extra_support_files": [str(p) for p in args.extra_support_json],
        "elapsed_sec": round(time.time() - t0, 3),
        "certificate_count": len(certs),
        "certificates": certs,
        "augmentation": {"added": added, "skipped": skipped},
        "cross_application_records": cross_hits,
        "cross_summary": {
            "stored_plus_extra_support_count": len(target_map),
            "cross_records": len(cross_hits),
            "targets_hit": len(set(r["target_name"] for r in cross_hits)),
            "certs_with_hits": len(set(r["cert_index"] for r in cross_hits)),
        },
    }
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(args.out),
        "base_count": len(base.get("certificates", [])),
        "certificate_count": len(certs),
        "added": added,
        "skipped": skipped,
        "cross_summary": out["cross_summary"],
        "elapsed_sec": out["elapsed_sec"],
    }, indent=2, sort_keys=True)[:5000])


if __name__ == "__main__":
    main()
