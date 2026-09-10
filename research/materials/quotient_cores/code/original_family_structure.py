#!/usr/bin/env python3
"""analysis: reconstruct lift-obstruction graph-family structure from original rows.

analysis grouped the deduplicated lift-bit inequalities retained by
build_constraints_all.  That is globally sound but loses alternative source-row
provenance, so it cannot decide whether one genuine quotient graph family was
already lift-infeasible before cross-family coupling.

This script scans Wang's complete full-tensor LUT directly for the analysis
12-point pivot-17 obstruction A, keeps every original q-avoiding source row that
rejects at least one lift assignment on A, groups these rows by their quotient
projection U=pi(W), and accumulates the rejected assignment union per family and
per source dimension.  It does not deduplicate across families.
"""
from __future__ import annotations

import hashlib
import json
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence

ROOT = Path("research/research_record")
OUT = ROOT / "workspace/data/quotient_lift/original_family_structure_rank2_A12.json"
SCRIPTS = ROOT / "workspace/scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
from lift_bit_feasibility_allrows import (  # type: ignore
    LUT_PATH,
    PIVOTS,
    in_span,
    load_lut,
    section_lift,
    sha_file,
)

S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import unpack_basis  # type: ignore

PIVOT = PIVOTS["rank2"]
A = [9, 33, 99, 160, 184, 189, 192, 209, 215, 224, 249, 254]
N = len(A)
NASSIGN = 1 << N
UNIVERSE = (1 << NASSIGN) - 1


def sha_obj(obj) -> str:
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def quotient_project(a: int, pivot: int = PIVOT) -> int:
    if a == 0 or a == pivot:
        return 0
    h = pivot.bit_length() - 1
    if (a >> h) & 1:
        a ^= pivot
    low = a & ((1 << h) - 1)
    high = (a >> (h + 1)) << h
    return low | high


def subspace_nonzero_points(basis: Sequence[int]) -> list[int]:
    pts = [0]
    for b in basis:
        pts += [x ^ int(b) for x in pts]
    return [x for x in pts if x]


def quotient_umask_from_basis(basis: Sequence[int], pivot: int = PIVOT) -> int:
    mask = 0
    for v in subspace_nonzero_points(basis):
        p = quotient_project(v, pivot)
        if p:
            mask |= 1 << p
    return mask


def reject_mask_for_constraint(z: int, o: int, cap: int, n: int = N) -> int:
    rm = 0
    for assn in range(1 << n):
        occ = 0
        for i in range(n):
            b = (assn >> i) & 1
            if ((z >> i) & 1) and b == 0:
                occ += 1
            elif ((o >> i) & 1) and b == 1:
                occ += 1
        if occ > cap:
            rm |= 1 << assn
    return rm


def bits(assn: int, n: int = N) -> list[int]:
    return [(assn >> i) & 1 for i in range(n)]


def points_from_umask(umask: int) -> list[int]:
    return [p for p in range(1, 256) if (umask >> p) & 1]


def strip_family(f: dict) -> dict:
    out = {k: v for k, v in f.items() if k != "reject_mask"}
    out["covered_assignments"] = int(f["reject_mask"].bit_count())
    out["infeasible_alone"] = f["reject_mask"] == UNIVERSE
    out["cap_hist"] = {str(k): int(v) for k, v in sorted(f["cap_hist"].items())}
    out["active_hist"] = {str(k): int(v) for k, v in sorted(f["active_hist"].items())}
    out["source_dim_hist"] = {str(k): int(v) for k, v in sorted(f["source_dim_hist"].items())}
    return out


def scan_original_families() -> dict:
    t0 = time.time()
    print(f"Loading LUT {LUT_PATH}...", flush=True)
    lut, meta = load_lut(LUT_PATH)
    lifts = [(section_lift(p, PIVOT), section_lift(p, PIVOT) ^ PIVOT) for p in A]
    stats = Counter()
    full_cap_hist = Counter()
    relevant_cap_hist = Counter()
    relevant_active_hist = Counter()
    relevant_dim_hist = Counter()
    q_violations = []
    families: dict[int, dict] = {}
    exact_dim_masks = [0] * 10
    exact_dim_row_counts = [0] * 10
    exact_dim_unique_ineq: list[set[tuple[int, int, int]]] = [set() for _ in range(10)]
    reject_cache: dict[tuple[int, int, int], int] = {}

    for idx, (key, lb0) in enumerate(lut.items()):
        if idx and idx % 500000 == 0:
            print(
                f"  scanned {idx:,}/{len(lut):,}; relevant={stats['relevant_nonq_rows']:,}; "
                f"families={len(families):,}; elapsed={time.time()-t0:.1f}s",
                flush=True,
            )
        basis = unpack_basis(int(key))
        d = len(basis)
        lb = int(lb0)
        cap = 20 - lb
        if cap >= 20:
            stats["skipped_cap_ge_20"] += 1
            continue
        if cap < 0:
            stats["negative_cap_rows"] += 1
            continue
        stats["rows_used"] += 1
        full_cap_hist[cap] += 1
        pairs = tuple((int(b).bit_length() - 1, int(b)) for b in basis if b)
        contains_q = in_span(PIVOT, pairs)
        if contains_q:
            stats["q_containing"] += 1
            occ = 1
            pts = []
            for p, (a0, a1) in zip(A, lifts):
                b0 = in_span(a0, pairs)
                b1 = in_span(a1, pairs)
                if b0 != b1:
                    raise AssertionError(("q-containing mismatch", idx, p, basis, b0, b1))
                if b0:
                    occ += 1
                    pts.append(p)
            if occ > cap:
                stats["q_violations"] += 1
                if len(q_violations) < 20:
                    q_violations.append(
                        {
                            "idx": idx,
                            "dim": d,
                            "lb": lb,
                            "cap20": cap,
                            "occ_with_q": occ,
                            "projected_points": pts,
                            "basis9": [int(x) for x in basis],
                        }
                    )
            continue

        stats["nonq"] += 1
        zmask = 0
        omask = 0
        active = 0
        for i, (a0, a1) in enumerate(lifts):
            b0 = in_span(a0, pairs)
            b1 = in_span(a1, pairs)
            if b0 and b1:
                raise AssertionError(("non-q contains both lifts", idx, A[i], basis))
            if b0:
                zmask |= 1 << i
                active += 1
            elif b1:
                omask |= 1 << i
                active += 1
        if active == 0:
            stats["nonq_no_active"] += 1
            continue
        stats["nonq_active"] += 1
        if active <= cap:
            stats["nonq_tautological"] += 1
            continue

        stats["relevant_nonq_rows"] += 1
        relevant_cap_hist[cap] += 1
        relevant_active_hist[active] += 1
        relevant_dim_hist[d] += 1
        key3 = (zmask, omask, cap)
        rm = reject_cache.get(key3)
        if rm is None:
            rm = reject_mask_for_constraint(zmask, omask, cap)
            reject_cache[key3] = rm
        exact_dim_masks[d] |= rm
        exact_dim_row_counts[d] += 1
        exact_dim_unique_ineq[d].add(key3)
        umask = quotient_umask_from_basis(basis)
        if umask == 0:
            raise AssertionError(("q-avoiding nonzero row projected to zero", idx, basis))
        upts = points_from_umask(umask)
        active_points = [p for p in A if p in set(upts)]
        if len(active_points) != active:
            raise AssertionError(("active/projection mismatch", idx, active, active_points, basis, zmask, omask))
        fam = families.get(umask)
        if fam is None:
            fam = {
                "quotient_umask": int(umask),
                "quotient_dim": int(d),
                "quotient_size": int((1 << d) - 1),
                "active_points": active_points,
                "row_count": 0,
                "unique_ineq_count": 0,
                "reject_mask": 0,
                "cap_hist": Counter(),
                "active_hist": Counter(),
                "source_dim_hist": Counter(),
                "row_head": [],
                "unique_ineqs": set(),
            }
            families[umask] = fam
        fam["row_count"] += 1
        fam["reject_mask"] |= rm
        fam["cap_hist"][cap] += 1
        fam["active_hist"][active] += 1
        fam["source_dim_hist"][d] += 1
        fam["unique_ineqs"].add(key3)
        if len(fam["row_head"]) < 8:
            fam["row_head"].append(
                {
                    "idx": idx,
                    "source_basis9": [int(x) for x in basis],
                    "source_dim": int(d),
                    "source_lb": int(lb),
                    "source_cap20": int(cap),
                    "active": int(active),
                    "eps0_points": [A[i] for i in range(N) if (zmask >> i) & 1],
                    "eps1_points": [A[i] for i in range(N) if (omask >> i) & 1],
                    "reject_count": int(rm.bit_count()),
                }
            )

    # Normalize unique counts and sort families by coverage.
    fam_records = []
    for fam in families.values():
        fam["unique_ineq_count"] = len(fam.pop("unique_ineqs"))
        fam_records.append(strip_family(fam))
    fam_records.sort(
        key=lambda f: (
            not f["infeasible_alone"],
            -f["covered_assignments"],
            -f["row_count"],
            f["quotient_dim"],
            f["quotient_umask"],
        )
    )
    prefix = 0
    dim_prefix = []
    for D in range(1, 9):
        prefix |= exact_dim_masks[D]
        survivors = [a for a in range(NASSIGN) if ((prefix >> a) & 1) == 0]
        dim_prefix.append(
            {
                "max_source_dim": D,
                "original_relevant_row_count": int(sum(exact_dim_row_counts[: D + 1])),
                "unique_inequality_count": int(sum(len(exact_dim_unique_ineq[d]) for d in range(D + 1))),
                "covered_assignments": int(prefix.bit_count()),
                "uncovered_assignments": int(NASSIGN - prefix.bit_count()),
                "all_covered": prefix == UNIVERSE,
                "survivor_assignment_head": [
                    {"assignment_int": int(a), "bits_in_A_order": bits(a)} for a in survivors[:16]
                ],
            }
        )
    union_all = 0
    for fam in families.values():
        union_all |= fam["reject_mask"]
    single = [f for f in fam_records if f["infeasible_alone"]]
    top = [{k: v for k, v in f.items() if k != "reject_mask"} for f in fam_records[:30]]
    out = {
        "schema": "s0908_original_family_structure_v1",
        "purpose": "Recompute graph-family lift-obstruction structure using every original Wang source row before cross-family (zmask,omask) deduplication.",
        "source_lut": str(LUT_PATH),
        "source_lut_sha256": sha_file(LUT_PATH),
        "lut_coverage_ok": meta.get("coverage_ok"),
        "pivot_name": "rank2",
        "pivot": PIVOT,
        "section": "analysis high-pivot section, native quotient bit p",
        "cut_points_A": A,
        "assignment_count": NASSIGN,
        "stats": {str(k): int(v) for k, v in sorted(stats.items())},
        "full_cap_hist_used": {str(k): int(v) for k, v in sorted(full_cap_hist.items())},
        "relevant_original_cap_hist": {str(k): int(v) for k, v in sorted(relevant_cap_hist.items())},
        "relevant_original_active_hist": {str(k): int(v) for k, v in sorted(relevant_active_hist.items())},
        "relevant_original_dim_hist": {str(k): int(v) for k, v in sorted(relevant_dim_hist.items())},
        "unique_rejecting_inequality_count_global": len(reject_cache),
        "q_containing_violation_count": int(stats.get("q_violations", 0)),
        "q_containing_violations_head": q_violations,
        "original_family_count_with_rejecting_rows": len(fam_records),
        "single_original_graph_family_infeasible_count": len(single),
        "single_original_graph_family_infeasible_head": single[:20],
        "top_original_graph_families_by_assignment_coverage": top,
        "dimension_prefix_cover_original_rows": dim_prefix,
        "global_union_all_original_graph_rows": {
            "covered_assignments": int(union_all.bit_count()),
            "all_covered": union_all == UNIVERSE,
            "uncovered_assignments": int(NASSIGN - union_all.bit_count()),
        },
        "comparison_with": {
            "grouped_after_cross_family_dedup_path": "data/quotient_lift/obstruction_structure.json",
            "qualification": "analysis single-family/family-cover claims were about the provenance-reduced deduplicated inequalities. This file uses original source-row family unions.",
        },
        "interpretation": {
            "family_mechanism": (
                "At least one complete original graph family already rejects all lift assignments on A; within-family compatibility should be studied as a scalable primitive."
                if single
                else "No original graph family rejects all assignments on A; the corrected original-row scan supports a genuine cross-family shared-lift-bit obstruction for this A."
            ),
            "dimension_prefix_status": "Dimension prefix coverage is now computed from original source rows in the complete LUT; uncovered assignments are genuine relative to those rows, not artifacts of cross-family deduplication.",
        },
        "top_original_graph_families_sha256": sha_obj(top),
        "elapsed_sec": time.time() - t0,
    }
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    return out


def main() -> None:
    out = scan_original_families()
    print(
        json.dumps(
            {
                "status": "ok",
                "relevant_original_rows": out["stats"].get("relevant_nonq_rows"),
                "unique_rejecting_inequalities": out["unique_rejecting_inequality_count_global"],
                "families": out["original_family_count_with_rejecting_rows"],
                "single_family_infeasible_count": out["single_original_graph_family_infeasible_count"],
                "dimension_prefix_cover": out["dimension_prefix_cover_original_rows"],
                "global_all_covered": out["global_union_all_original_graph_rows"],
                "elapsed_sec": out["elapsed_sec"],
            },
            indent=2,
            sort_keys=True,
        ),
        flush=True,
    )
    print("saved", OUT, flush=True)


if __name__ == "__main__":
    main()
