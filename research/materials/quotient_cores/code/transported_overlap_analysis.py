#!/usr/bin/env python3
r"""analysis: transport the certified d=3 local Wang exclusion globally.

analysis produced a DRAT-verified pure-Wang local exclusion around the
trace-consistent 9-violation support S: there is no complete-Wang-admissible
19-point distinct E11 support S' with |S∩S'| >= 16.  Because the E11 stabilizer
acts on the whole support and preserves the core Wang occupation table, this
transports to every whole-support image gS:

    every complete-Wang-admissible S' satisfies |S'∩gS| <= 15.

This script builds the transported centers using the actual induced stabilizer
permutations, compares all stored near-misses to the certified neighborhood
union, and writes the overlap data for later global searches.  It deliberately
keeps point-level supports; point-orbit counts are not used as a substitute for
whole-support action.
"""
from __future__ import annotations

import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from distinct_trace_cut_cpsat import generate_stabilizer_permutations  # noqa: E402
from trace_dependency_family import load_candidate_supports  # noqa: E402
from support_symmetry_discipline import load_new_supports, canonical_support  # noqa: E402

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/transported_overlap"
BASE_SUPPORT = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]
D_CERTIFIED = 3
OVERLAP_MAX_CERTIFIED = 19 - D_CERTIFIED - 1  # no support with >=16 overlap, so <=15
D3_META = ROOT / "workspace/data/neighborhood_repair/cnf/current_support_repair_d3.meta.json"
D3_STATUS = ROOT / "workspace/data/neighborhood_repair/cnf/current_support_repair_d3.status.json"


def clean_support(A: Iterable[int]) -> Tuple[int, ...] | None:
    vals = tuple(sorted(int(x) for x in A))
    if len(vals) != 19 or len(set(vals)) != 19 or vals[0] < 1 or vals[-1] > 255:
        return None
    return vals


def support_bitset(A: Sequence[int]) -> int:
    b = 0
    for p in A:
        b |= 1 << (int(p) - 1)
    return b


def transported_centers(perms: Sequence[Sequence[int]], base: Sequence[int]) -> List[Tuple[int, ...]]:
    centers = {tuple(sorted(int(perm[p]) for p in base)) for perm in perms}
    return sorted(centers)


def load_all_stored_supports() -> List[dict]:
    raw = []
    raw.extend(load_candidate_supports())
    raw.extend(load_new_supports())
    raw.append({
        "name": "current_best_trace_consistent_9viol_base",
        "source": "explicit analysis base support",
        "A_cols": list(BASE_SUPPORT),
        "complete_wang_violations": 9,
    })
    # Include any supports embedded in neighborhood outputs if future feasible runs appear.
    for path in (ROOT / "workspace/data/neighborhood_repair").glob("repair_d*_*.json"):
        try:
            d = json.loads(path.read_text())
        except Exception:
            continue
        sol = d.get("solve", {})
        A = sol.get("A_cols") or d.get("A_cols")
        if A:
            raw.append({
                "name": f"{path.stem}_solution",
                "source": str(path),
                "A_cols": A,
                "complete_wang_violations": sol.get("complete_wang_scan", {}).get("complete_violation_count"),
            })
    out = []
    seen = set()
    for i, r in enumerate(raw):
        A = clean_support(r.get("A_cols", []))
        if A is None:
            continue
        if A in seen:
            continue
        seen.add(A)
        rr = dict(r)
        rr["A_cols"] = list(A)
        rr.setdefault("name", f"support_{i}")
        out.append(rr)
    return out


def main() -> None:
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    perms = generate_stabilizer_permutations(include_transpose=True)
    centers = transported_centers(perms, BASE_SUPPORT)
    center_bits = [support_bitset(c) for c in centers]
    base_bit = support_bitset(BASE_SUPPORT)
    base_stab = sum(1 for perm in perms if tuple(sorted(int(perm[p]) for p in BASE_SUPPORT)) == tuple(sorted(BASE_SUPPORT)))
    d3_meta = json.loads(D3_META.read_text()) if D3_META.exists() else {}
    d3_status = json.loads(D3_STATUS.read_text()) if D3_STATUS.exists() else {}

    supports = load_all_stored_supports()
    records = []
    by_max = Counter()
    covered = 0
    uncovered = 0
    canonical_clusters = defaultdict(list)
    for r in supports:
        A = tuple(int(x) for x in r["A_cols"])
        Abit = support_bitset(A)
        overlaps = [int((Abit & cb).bit_count()) for cb in center_bits]
        maxov = max(overlaps) if overlaps else 0
        num_max = sum(1 for z in overlaps if z == maxov)
        direct = int((Abit & base_bit).bit_count())
        nearest_indices = [i for i, z in enumerate(overlaps) if z == maxov][:5]
        can = canonical_support(A, perms)
        rec = {
            "name": r.get("name"),
            "source": r.get("source"),
            "A_cols": list(A),
            "complete_wang_violations": r.get("complete_wang_violations"),
            "direct_overlap_with_base": direct,
            "max_transported_overlap_with_base_orbit": maxov,
            "exchange_distance_to_base_orbit": 19 - maxov,
            "covered_by_certified_radius3_union_if_it_were_admissible": bool(maxov >= 16),
            "number_of_centers_attaining_max_overlap": num_max,
            "nearest_center_examples": [list(centers[i]) for i in nearest_indices],
            "canonical_support": list(can),
        }
        records.append(rec)
        by_max[maxov] += 1
        if maxov >= 16:
            covered += 1
        else:
            uncovered += 1
        canonical_clusters[tuple(can)].append(rec["name"])

    uncovered_records = [r for r in records if not r["covered_by_certified_radius3_union_if_it_were_admissible"]]
    covered_records = [r for r in records if r["covered_by_certified_radius3_union_if_it_were_admissible"]]
    result = {
        "schema": "transported_overlap_analysis_v1",
        "field": "F2",
        "core": "E11 quotient core",
        "rank_s": 19,
        "base_support": BASE_SUPPORT,
        "mathematical_consequence": "The d=3 DRAT-verified local pure-Wang exclusion around S implies every complete-Wang-admissible distinct support S' satisfies |S'∩S|<=15; applying one induced E11 stabilizer element to the whole center gives |S'∩gS|<=15 for every center gS.",
        "not_used": "Point-orbit counts are not used; each transported center is a whole-support image under one stabilizer element.",
        "certified_overlap_cut": {
            "d_certified": D_CERTIFIED,
            "excluded_condition": "|S'∩gS| >= 16",
            "linear_cut": "sum_{p in gS} x_p <= 15",
            "overlap_max": OVERLAP_MAX_CERTIFIED,
            "d3_meta_path": str(D3_META),
            "d3_status_path": str(D3_STATUS),
            "d3_cnf_sha256": d3_meta.get("cnf_sha256"),
            "d3_drat_sha256": d3_status.get("hashes", {}).get(str(D3_STATUS).replace(".status.json", ".drat")),
            "d3_drat_trim_verified": bool(d3_status.get("drat_trim_log_parse", {}).get("contains_verified")),
        },
        "group": {
            "permutation_count": len(perms),
            "unique_transported_center_count": len(centers),
            "base_support_stabilizer_size_in_generated_group": base_stab,
            "orbit_size_from_stabilizer": len(perms) // max(1, base_stab),
        },
        "stored_support_summary": {
            "support_count": len(records),
            "covered_by_certified_radius3_union": covered,
            "outside_certified_radius3_union": uncovered,
            "max_overlap_histogram": {str(k): int(v) for k, v in sorted(by_max.items())},
            "whole_support_orbit_count_in_sample": len(canonical_clusters),
        },
        "covered_records": covered_records,
        "uncovered_records": uncovered_records,
        "all_records": records,
        "centers": [list(c) for c in centers],
        "elapsed_sec": round(time.time() - t0, 3),
    }
    out = OUTDIR / "transported_overlap_analysis.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "group": result["group"],
        "stored_support_summary": result["stored_support_summary"],
        "covered_names_head": [r["name"] for r in covered_records[:12]],
        "uncovered_names_head": [r["name"] for r in uncovered_records[:12]],
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
