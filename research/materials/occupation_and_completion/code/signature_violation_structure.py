#!/usr/bin/env python3
r"""Analyze complete-Wang rows that are invisible to the analysis five-bit signature quotient.

The min4 count abstraction keeps only the five incidence bits against
[9,43,53,157,234].  The analysis source support satisfies every Wang row that is
a preimage of a signature subspace, yet violates nine complete E11 Wang rows at
L=12.  This script describes those violating rows by their image in the signature
quotient and compares each row with the corresponding larger preimage row.
"""
from __future__ import annotations

import json
import pickle
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, List, Sequence

S0904_SCRIPTS = Path("scripts")
if str(S0904_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(S0904_SCRIPTS))
S0908_SCRIPTS = Path("scripts")
if str(S0908_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(S0908_SCRIPTS))

from shadow_guided_support_search import build_or_load_records  # type: ignore  # noqa:E402
from wang_capacity_lazy import pack_basis, rref_basis, subspace_points_from_basis, unpack_basis  # type: ignore  # noqa:E402
from core_capacity_from_wang_lut import CoreQuotient  # type: ignore  # noqa:E402
from shadow_certificate_analysis import popparity  # type: ignore  # noqa:E402

ROOT = Path("research/research_record")
COUNT_PATH = ROOT / "workspace/data/shadow_certificate/signature_count_relaxation.json"
OUT = ROOT / "workspace/data/shadow_certificate/signature_violation_structure.json"
MASKS = [9, 43, 53, 157, 234]
S = 19


def signature(p: int) -> int:
    sig = 0
    for i, m in enumerate(MASKS):
        if popparity(int(p) & int(m)):
            sig |= 1 << i
    return sig


def subspace_points_including_zero(basis: Sequence[int]) -> List[int]:
    pts = [0]
    for b in basis:
        pts += [x ^ b for x in pts]
    return sorted(set(pts))


def source_support() -> List[int]:
    data = json.loads(COUNT_PATH.read_text())
    return [int(p) for p in json.loads(Path("data/shadow_certificate/target_certificate.json").read_text())["support"]]


def find_record_by_key8(records, key8: int):
    for r in records:
        if int(r["key8"]) == int(key8):
            return r
    raise KeyError(key8)


def main() -> None:
    records, meta = build_or_load_records()
    core = CoreQuotient(1)
    rec_by_key = {int(r["key8"]): r for r in records}
    support = source_support()
    support_set = set(support)
    sig_counts = Counter(signature(p) for p in support)

    violations = []
    for rec in records:
        pts = [int(p) for p in rec["pts"] if p]
        occ_pts = sorted(p for p in pts if p in support_set)
        occ = len(occ_pts)
        if occ > int(rec["cap"]):
            sig_image_basis = rref_basis([signature(p) for p in pts], n=5)
            sig_image_pts = subspace_points_including_zero(sig_image_basis)
            preimage_pts_all = [p for p in range(256) if signature(p) in set(sig_image_pts)]
            preimage_basis8 = rref_basis(preimage_pts_all, n=8)
            preimage_key8 = pack_basis(preimage_basis8)
            pre_rec = rec_by_key[int(preimage_key8)]
            pre_occ = sum(sig_counts[s] for s in sig_image_pts)
            sig_occ = Counter(signature(p) for p in occ_pts)
            violations.append({
                "key8": int(rec["key8"]),
                "basis8": list(unpack_basis(int(rec["key8"]))),
                "dim8": int(rec["dim8"]),
                "L": int(rec["L"]),
                "cap": int(rec["cap"]),
                "occupancy": occ,
                "excess": int(occ - int(rec["cap"])),
                "support_points_in_row": occ_pts,
                "support_signature_counts_in_row": dict(sorted(sig_occ.items())),
                "signature_image_basis": list(sig_image_basis),
                "signature_image_dim": len(sig_image_basis),
                "signature_image_points": sig_image_pts,
                "preimage_key8": int(preimage_key8),
                "preimage_basis8": list(preimage_basis8),
                "preimage_dim8": int(preimage_key8 & 0xF),
                "preimage_L": int(pre_rec["L"]),
                "preimage_cap": int(pre_rec["cap"]),
                "source_occupancy_in_preimage": int(pre_occ),
                "preimage_row_violated_by_source": bool(pre_occ > int(pre_rec["cap"])),
            })
    violations.sort(key=lambda r: (r["L"], r["dim8"], r["key8"]))

    payload = {
        "schema": "s0908_signature_violation_structure_v1",
        "field": "F2",
        "meaning": "For the analysis source support, the complete-Wang violations are rows that distinguish directions inside five-bit signature classes; their signature-preimage rows are not violated.",
        "masks": MASKS,
        "support": support,
        "source_signature_counts": dict(sorted(sig_counts.items())),
        "record_meta_count": meta.get("count"),
        "violation_count": len(violations),
        "violations_by_L": dict(sorted(Counter(v["L"] for v in violations).items())),
        "violations": violations,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(OUT),
        "violation_count": len(violations),
        "violations_by_L": payload["violations_by_L"],
        "brief": [{k: v[k] for k in ["dim8", "L", "cap", "occupancy", "signature_image_dim", "preimage_dim8", "preimage_L", "preimage_cap", "source_occupancy_in_preimage", "preimage_row_violated_by_source"]} for v in violations],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
