#!/usr/bin/env python3
r"""analysis: orbit profiles of low-slack/violated Wang rows for near-miss supports.

This asks whether the recently found near-misses are failing by a small number
of row orbits under the E11 table-preserving stabilizer, rather than by isolated
rows.  It profiles the full orbit closures of violated complete-Wang rows for
several supports:

* the analysis base trace-consistent 9-violation support;
* the analysis L>=15 overlap-cut separator candidate;
* the analysis L>=14 overlap-cut separator candidate.

The output is intended to guide global proof-producing subsystems: row-orbit
closures are valid only because analysis separately verified complete core Wang
L-invariance under the generated group.
"""
from __future__ import annotations

import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient  # noqa: E402
from complete_core_and_transversal import ROOT, build_core_constraints  # noqa: E402
from distinct_trace_cut_cpsat import generate_stabilizer_permutations  # noqa: E402
from cert_trace_separator import full_violation_scan, points_for_rec  # noqa: E402
from wang_invariance_check import basis_images_from_perm, transform_key8  # noqa: E402
from neighborhood_repair import DEFAULT_SUPPORT, points_bitset  # noqa: E402

OUTDIR = ROOT / "workspace/data/transported_overlap"


def load_lut(path: Path):
    with path.open("rb") as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload["lut"].items()}, payload.get("meta", {})


def load_support_from_separator(path: Path, round_index: int = 0) -> List[int] | None:
    if not path.exists():
        return None
    data = json.loads(path.read_text())
    rounds = data.get("rounds", [])
    for r in rounds:
        if int(r.get("round", -1)) == round_index and r.get("A_cols"):
            return [int(p) for p in r["A_cols"]]
    if data.get("solution", {}).get("A_cols"):
        return [int(p) for p in data["solution"]["A_cols"]]
    return None


def row_orbit(seed_key: int, basis_images_list: Sequence[Sequence[int]]) -> Tuple[int, ...]:
    return tuple(sorted({transform_key8(int(seed_key), imgs) for imgs in basis_images_list}))


def orbit_closure(keys: Iterable[int], basis_images_list: Sequence[Sequence[int]]) -> Tuple[set[int], List[dict]]:
    cache: Dict[int, Tuple[int, ...]] = {}
    closure: set[int] = set()
    orbit_records = []
    for key in sorted(set(int(k) for k in keys)):
        if key in cache:
            orb = cache[key]
        else:
            orb = row_orbit(key, basis_images_list)
            for z in orb:
                cache[z] = orb
        closure.update(orb)
        orbit_records.append({"seed_key8": int(key), "orbit_size": len(orb), "orbit_rep_key8": int(min(orb))})
    # Deduplicate orbit records by representative.
    by_rep = {}
    for r in orbit_records:
        by_rep.setdefault(r["orbit_rep_key8"], r)
    return closure, sorted(by_rep.values(), key=lambda r: (r["orbit_rep_key8"], r["seed_key8"]))


def support_slack_records(records: Sequence[dict], A: Sequence[int], slack_values: set[int]) -> List[dict]:
    Ab = points_bitset(A)
    out = []
    for rec in records:
        L = int(rec["L"])
        cap = 19 - L
        if cap >= 19:
            continue
        ptsb = 0
        for p in points_for_rec(rec):
            ptsb |= 1 << (p - 1)
        occ = (Ab & ptsb).bit_count()
        slack = cap - occ
        if slack in slack_values:
            rr = dict(rec)
            rr.update({"cap": cap, "occupancy": occ, "slack": slack})
            out.append(rr)
    return out


def summarize_key_set(keys: Iterable[int], L_by_key: Dict[int, int]) -> dict:
    keys = set(int(k) for k in keys)
    by_L = Counter(int(L_by_key[k]) for k in keys)
    by_dim = Counter(int(k & 0xF) for k in keys)
    return {
        "count": len(keys),
        "by_L": {str(k): int(v) for k, v in sorted(by_L.items())},
        "by_dim8": {str(k): int(v) for k, v in sorted(by_dim.items())},
    }


def main() -> None:
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    lut, _ = load_lut(ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl")
    core = CoreQuotient(1)
    records, meta = build_core_constraints(core, lut)
    L_by_key = {int(r["key8"]): int(r["L"]) for r in records}
    rec_by_key = {int(r["key8"]): r for r in records}
    perms = [tuple(int(x) for x in p) for p in generate_stabilizer_permutations(include_transpose=True)]
    basis_images_list = [basis_images_from_perm(p) for p in perms]

    supports = [
        {"name": "base_trace_consistent_9viol", "source": "analysis/54", "A_cols": list(DEFAULT_SUPPORT)},
    ]
    for name, path in [
        ("L15_overlap_cert_round0", OUTDIR / "overlap_cut_separator_L15_cert_3r_180s.json"),
        ("L14_overlap_cert_round0", OUTDIR / "overlap_cut_separator_L14_cert_2r_240s.json"),
    ]:
        A = load_support_from_separator(path, 0)
        if A:
            supports.append({"name": name, "source": str(path), "A_cols": A})

    support_records = []
    closure_sets = {}
    for srec in supports:
        A = [int(p) for p in srec["A_cols"]]
        scan = full_violation_scan(A, records, s=19)
        viol_keys = [int(v["key8"]) for v in scan["violations"]]
        viol_closure, viol_orbits = orbit_closure(viol_keys, basis_images_list)
        closure_sets[srec["name"]] = viol_closure
        slack0 = support_slack_records(records, A, {0})
        slack0_keys = [int(r["key8"]) for r in slack0]
        slack0_closure, slack0_orbits = orbit_closure(slack0_keys, basis_images_list)
        support_records.append({
            "name": srec["name"],
            "source": srec["source"],
            "A_cols": A,
            "complete_wang_scan": {k: v for k, v in scan.items() if k != "violations"},
            "violation_key_count": len(viol_keys),
            "violation_keys_head": viol_keys[:50],
            "violation_orbit_count": len(viol_orbits),
            "violation_orbits": viol_orbits,
            "violation_orbit_closure_summary": summarize_key_set(viol_closure, L_by_key),
            "slack0_key_count": len(slack0_keys),
            "slack0_orbit_count": len(slack0_orbits),
            "slack0_orbit_closure_summary": summarize_key_set(slack0_closure, L_by_key),
        })

    pairwise = []
    names = [r["name"] for r in support_records]
    for i, ni in enumerate(names):
        for nj in names[i+1:]:
            A = closure_sets[ni]
            B = closure_sets[nj]
            pairwise.append({
                "a": ni,
                "b": nj,
                "violation_orbit_closure_intersection": len(A & B),
                "union": len(A | B),
                "a_only": len(A - B),
                "b_only": len(B - A),
            })

    union_all = set()
    for s in closure_sets.values():
        union_all |= s
    result = {
        "schema": "violation_orbit_profile_v1",
        "field": "F2",
        "core": "E11 quotient core",
        "meaning": "Profiles whole-stabilizer orbit closures of violated complete-Wang rows for current near-miss basins. Row-orbit cuts preserve point incidences and are valid under the analysis Wang-invariance certificate.",
        "group_order": len(perms),
        "complete_core_table_meta": meta,
        "support_records": support_records,
        "pairwise_violation_closure_overlap": pairwise,
        "union_violation_orbit_closure_summary": summarize_key_set(union_all, L_by_key),
        "elapsed_sec": round(time.time() - t0, 3),
    }
    out = OUTDIR / "violation_orbit_profile.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "support_brief": [{"name": r["name"], "viol": r["violation_key_count"], "viol_orbits": r["violation_orbit_count"], "closure": r["violation_orbit_closure_summary"]} for r in support_records],
        "union": result["union_violation_orbit_closure_summary"],
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True)[:6000])


if __name__ == "__main__":
    main()
