#!/usr/bin/env python3
"""analysis: whole-support symmetry accounting for E11 distinct supports.

The analysis six point classes are useful descriptors, but a 19-point support is
acted on by one stabilizer element at a time.  This script computes canonical
whole-support representatives under the 1152-element E11 stabilizer and compares
them with six point-class profiles for stored near-misses.
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

from distinct_trace_cut_cpsat import generate_stabilizer_permutations  # noqa: E402
from orbit_structure import bit8_to_mat3x3, gl3f2_elements, mat3x3_to_8bit, apply_conj  # noqa: E402
from trace_dependency_family import load_candidate_supports  # noqa: E402

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/trace_dependency_cuts"


def compute_point_orbits(perms: Sequence[Sequence[int]]) -> List[List[int]]:
    unseen = set(range(1, 256))
    orbits = []
    while unseen:
        p0 = min(unseen)
        orb = {perm[p0] for perm in perms}
        # close under the generated full list (one pass is enough because perms is the full group)
        orbits.append(sorted(orb))
        unseen -= orb
    return sorted(orbits, key=lambda o: (len(o), min(o)))


def orbit_profile(A: Sequence[int], orbits: Sequence[Sequence[int]]) -> Tuple[int, ...]:
    idx = {}
    for i, orb in enumerate(orbits):
        for p in orb:
            idx[int(p)] = i
    c = Counter(idx[int(p)] for p in A)
    return tuple(int(c[i]) for i in range(len(orbits)))


def canonical_support(A: Sequence[int], perms: Sequence[Sequence[int]]) -> Tuple[int, ...]:
    S = [int(p) for p in A]
    return min(tuple(sorted(perm[p] for p in S)) for perm in perms)


def load_new_supports() -> List[dict]:
    out = []
    for path in [
        OUTDIR / "cpsat_L15_certcuts_180s.json",
        OUTDIR / "separator_L15_certcuts_6r_180s.json",
        OUTDIR / "separator_L15_augcertcuts_4r_240s.json",
        OUTDIR / "new_support_trace_evaluation.json",
        OUTDIR / "aug_separator_support_trace_evaluation.json",
    ]:
        if not path.exists():
            continue
        try:
            d = json.loads(path.read_text())
        except Exception:
            continue
        if d.get("solution", {}).get("A_cols"):
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
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    perms = generate_stabilizer_permutations(include_transpose=True)
    point_orbits = compute_point_orbits(perms)
    print(f"group maps={len(perms)} point_orbits={[len(o) for o in point_orbits]}")

    raw = load_candidate_supports() + load_new_supports()
    seen = set()
    supports = []
    for r in raw:
        A = tuple(int(x) for x in r.get("A_cols", []))
        if len(A) != 19 or len(set(A)) != 19:
            continue
        if A in seen:
            continue
        seen.add(A)
        supports.append(r)

    records = []
    for r in supports:
        A = [int(x) for x in r["A_cols"]]
        prof = orbit_profile(A, point_orbits)
        can = canonical_support(A, perms)
        stab_size = sum(1 for perm in perms if tuple(sorted(perm[p] for p in A)) == tuple(sorted(A)))
        records.append({
            "name": r.get("name"),
            "source": r.get("source"),
            "complete_wang_violations": r.get("complete_wang_violations"),
            "A_cols": A,
            "point_orbit_profile": list(prof),
            "canonical_support": list(can),
            "stabilizer_size_within_E11_group": int(stab_size),
            "support_orbit_size": int(len(perms) // max(1, stab_size)),
        })

    by_profile = defaultdict(list)
    for rec in records:
        by_profile[tuple(rec["point_orbit_profile"])].append(rec)
    profile_summaries = []
    for prof, recs in sorted(by_profile.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        cset = {tuple(r["canonical_support"]) for r in recs}
        wvals = sorted({str(r.get("complete_wang_violations")) for r in recs})
        profile_summaries.append({
            "profile": list(prof),
            "support_count_in_sample": len(recs),
            "distinct_whole_support_orbits_in_sample": len(cset),
            "wang_violation_values_in_sample": wvals,
            "example_names": [r["name"] for r in recs[:6]],
        })

    multi_profile_examples = [s for s in profile_summaries if s["distinct_whole_support_orbits_in_sample"] > 1]
    result = {
        "schema": "whole_support_symmetry_accounting_v1",
        "elapsed_sec": round(time.time() - t0, 3),
        "meaning": "Point-orbit profiles are descriptors only; whole supports are quotiented by one stabilizer element acting on all selected points.",
        "group_order": len(perms),
        "point_orbit_sizes": [len(o) for o in point_orbits],
        "point_orbits": point_orbits,
        "support_count": len(records),
        "profile_count_in_sample": len(by_profile),
        "profiles_with_multiple_whole_support_orbits": len(multi_profile_examples),
        "profile_summaries": profile_summaries,
        "support_records": records,
    }
    out = OUTDIR / "whole_support_symmetry_accounting.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "support_count": len(records),
        "profile_count": len(by_profile),
        "profiles_with_multiple_whole_support_orbits": len(multi_profile_examples),
        "top_profile_examples": profile_summaries[:5],
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True)[:5000])


if __name__ == "__main__":
    main()
