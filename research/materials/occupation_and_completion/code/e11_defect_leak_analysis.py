#!/usr/bin/env python3
"""Defect/leak-budget analysis for E11 core decompositions over F2.

This script tests the stronger block-spread consequence suggested after analysis.
For a fixed slice s with c active terms, write the active v,w matrices as
9 x c matrices and split them into contiguous 3-coordinate blocks.  If the
slice equations hold exactly, with own block R_j x C_i equal to I_3 and all
off-blocks zero, then

    dim span{v_t mod R_j : t in S_s} + dim span{w_t mod C_i : t in S_s} <= c-3.

For c=3 this is the analysis purity lemma; for c=4 it implies half-purity:
either all active v_t are confined to R_j or all active w_t are confined to C_i.

The first purpose is a soundness test on the 519 exact rank-21 E11 core pool.
The second purpose is a candidate-level measurement on the same-W two-deletion
rank-19 near-miss surfaces used in analysis.  That second measurement uses the
inherited v,w factors from the rank-21 decompositions; it is not a proof about
all possible completions of the same A-support.
"""
from __future__ import annotations

import argparse
import collections
import json
import sys
import time
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
import e11_shadow_filter as shadow  # noqa: E402

GROUP = [0b000000111, 0b000111000, 0b111000000]
FULL9 = 0x1FF


def slice_block(s: int) -> Tuple[int, int]:
    """Core slice s -> (row group j, column group i)."""
    a = s + 1
    return a % 3, a // 3


def row_to_terms(row: Sequence[int]) -> List[Tuple[int, int, int]]:
    r = len(row) // 3
    return [(int(row[3*t]), int(row[3*t+1]), int(row[3*t+2])) for t in range(r)]


def rank_int(rows: Iterable[int]) -> int:
    basis: Dict[int, int] = {}
    r = 0
    for x0 in rows:
        x = int(x0)
        while x:
            p = x.bit_length() - 1
            if p in basis:
                x ^= basis[p]
            else:
                basis[p] = x
                r += 1
                break
    return r


def bitrow(row: Sequence[int]) -> int:
    x = 0
    for i, b in enumerate(row):
        if int(b) & 1:
            x |= 1 << i
    return x


def consistent_int(rows: List[int], rhs: List[int], nvars: int) -> Tuple[bool, int, int]:
    rA = rank_int(rows)
    rB = rank_int([row | ((int(b) & 1) << nvars) for row, b in zip(rows, rhs)])
    return rA == rB, rA, rB


def shadow_summary_for_support(us: List[int], inv_lams: List[int]) -> dict:
    nvars = 9 * len(us)
    tensor_rows, tensor_rhs = shadow.build_tensor_shadow_rows(us)
    tight = [lam for lam in inv_lams if sum(shadow.dot8(lam, u) for u in us) == 9]
    rows = [bitrow(r) for r in tensor_rows]
    rhs = list(tensor_rhs)
    for lam in tight:
        tr, tb = shadow.add_trace_rows(us, [lam], transpose_coeff=False)
        rows.extend(bitrow(r) for r in tr)
        rhs.extend(tb)
    ok, rA, rB = consistent_int(rows, rhs, nvars)
    return {"ok": ok, "rank": rA, "aug_rank": rB, "tight_count": len(tight), "tight": tight}


def extract_group(mask: int, g: int) -> int:
    """Extract group g of a 9-bit mask as a compact 3-bit mask."""
    return (int(mask) >> (3*g)) & 0b111


def project_outside_group(mask: int, g: int) -> int:
    """Project a 9-bit vector modulo group g, returned as a compact 6-bit mask."""
    out = 0
    pos = 0
    for h in range(3):
        if h == g:
            continue
        bits = extract_group(mask, h)
        for k in range(3):
            if (bits >> k) & 1:
                out |= 1 << pos
            pos += 1
    return out


def mat3_from_block_terms(terms: List[Tuple[int, int, int]], active: List[int], j: int, i: int) -> int:
    """Return a 9-bit row-major 3x3 matrix for block R_j x C_i."""
    m = 0
    for t in active:
        _, v, w = terms[t]
        vb = extract_group(v, j)
        wb = extract_group(w, i)
        for r in range(3):
            if (vb >> r) & 1:
                for c in range(3):
                    if (wb >> c) & 1:
                        m ^= 1 << (3*r + c)
    return m


I3_MASK = (1 << 0) | (1 << 4) | (1 << 8)


def analyze_terms(terms: List[Tuple[int, int, int]], check_slice_equations: bool = False) -> dict:
    """Analyze defect/leak properties of one candidate list of terms."""
    R = len(terms)
    slice_records = []
    capacity_fail = 0
    defect_fail = 0
    half_purity_fail = 0
    cap3_purity_fail = 0
    own_rank_fail = 0
    slice_equation_fail = 0
    full_pure_slices = []

    for s in range(8):
        j_s, i_s = slice_block(s)
        active = [t for t, (u, _v, _w) in enumerate(terms) if (int(u) >> s) & 1]
        c = len(active)
        caps_fail_here = c < 3
        if caps_fail_here:
            capacity_fail += 1

        v_own = [extract_group(terms[t][1], j_s) for t in active]
        w_own = [extract_group(terms[t][2], i_s) for t in active]
        v_leak = [project_outside_group(terms[t][1], j_s) for t in active]
        w_leak = [project_outside_group(terms[t][2], i_s) for t in active]
        rv_own = rank_int(v_own)
        rw_own = rank_int(w_own)
        lv = rank_int(v_leak)
        lw = rank_int(w_leak)
        budget = c - 3
        defect_ok = (c >= 3 and lv + lw <= budget)
        half_ok = not (c == 4 and lv > 0 and lw > 0)
        cap3_ok = not (c == 3 and (lv != 0 or lw != 0))
        own_rank_ok = (c >= 3 and rv_own == 3 and rw_own == 3)

        if c >= 3 and not defect_ok:
            defect_fail += 1
        if not half_ok:
            half_purity_fail += 1
        if not cap3_ok:
            cap3_purity_fail += 1
        if c >= 3 and not own_rank_ok:
            own_rank_fail += 1
        if lv == 0 and lw == 0 and c >= 3:
            full_pure_slices.append(s)

        eq_ok = None
        if check_slice_equations:
            eq_ok = True
            for j in range(3):
                for i in range(3):
                    m = mat3_from_block_terms(terms, active, j, i)
                    target = I3_MASK if (j == j_s and i == i_s) else 0
                    if m != target:
                        eq_ok = False
            if not eq_ok:
                slice_equation_fail += 1

        slice_records.append({
            "s": s,
            "block": [j_s, i_s],
            "active_terms": active,
            "c": c,
            "own_v_rank": rv_own,
            "own_w_rank": rw_own,
            "leak_v_rank": lv,
            "leak_w_rank": lw,
            "leak_sum": lv + lw,
            "budget": budget,
            "capacity_ok": not caps_fail_here,
            "defect_ok": defect_ok,
            "half_purity_ok": half_ok,
            "cap3_purity_ok": cap3_ok,
            "own_rank_ok": own_rank_ok,
            "v_pure": lv == 0,
            "w_pure": lw == 0,
            "fully_pure": lv == 0 and lw == 0,
            "slice_equations_ok": eq_ok,
        })

    # Pairwise sharing among fully pure slices: no term should serve two such slices
    pure_shared_terms = []
    if len(full_pure_slices) >= 2:
        for t, (u, _v, _w) in enumerate(terms):
            ss = [s for s in full_pure_slices if (int(u) >> s) & 1]
            if len(ss) >= 2:
                pure_shared_terms.append({"term": t, "slices": ss})

    return {
        "rank_terms": R,
        "caps": [rec["c"] for rec in slice_records],
        "total_a_weight": sum(rec["c"] for rec in slice_records),
        "min_capacity": min(rec["c"] for rec in slice_records),
        "max_capacity": max(rec["c"] for rec in slice_records),
        "capacity_fail_slices": capacity_fail,
        "defect_fail_slices": defect_fail,
        "half_purity_fail_slices": half_purity_fail,
        "cap3_purity_fail_slices": cap3_purity_fail,
        "own_rank_fail_slices": own_rank_fail,
        "slice_equation_fail_slices": slice_equation_fail if check_slice_equations else None,
        "full_pure_slices": full_pure_slices,
        "pure_shared_terms": pure_shared_terms,
        "slice_records": slice_records,
        "all_defect_conditions_ok": (capacity_fail == 0 and defect_fail == 0 and half_purity_fail == 0 and cap3_purity_fail == 0 and own_rank_fail == 0 and not pure_shared_terms),
    }


def accumulate_profile_hists(analysis: dict, hists: dict):
    hists["capacity_profile"][tuple(sorted(analysis["caps"]))] += 1
    hists["total_weight"][analysis["total_a_weight"]] += 1
    hists["min_capacity"][analysis["min_capacity"]] += 1
    for rec in analysis["slice_records"]:
        c = rec["c"]
        lv = rec["leak_v_rank"]
        lw = rec["leak_w_rank"]
        hists["by_capacity_leak"][(c, lv, lw)] += 1
        hists["leak_sum_slack"][(c, lv + lw, rec["budget"] - (lv + lw))] += 1
        if c == 4:
            if lv == 0 and lw == 0:
                side = "both_pure"
            elif lv == 0:
                side = "v_pure_only"
            elif lw == 0:
                side = "w_pure_only"
            else:
                side = "both_leak_violation"
            hists["cap4_side"][side] += 1
        if c == 5:
            hists["cap5_leak_pair"][(lv, lw)] += 1


def json_counter(counter: collections.Counter, key_as_tuple: bool = True) -> dict:
    items = sorted(counter.items(), key=lambda kv: (str(kv[0]), kv[1]))
    if key_as_tuple:
        return {str(k): int(v) for k, v in items}
    return {str(k): int(v) for k, v in items}


def analyze_pool(pool: np.ndarray, max_exact_rows: int = 519) -> dict:
    hists = {
        "capacity_profile": collections.Counter(),
        "total_weight": collections.Counter(),
        "min_capacity": collections.Counter(),
        "by_capacity_leak": collections.Counter(),
        "leak_sum_slack": collections.Counter(),
        "cap4_side": collections.Counter(),
        "cap5_leak_pair": collections.Counter(),
    }
    failures = []
    heads = []
    exact_failures = []
    for idx, row in enumerate(pool):
        terms = row_to_terms(row)
        check_eq = idx < max_exact_rows
        analysis = analyze_terms(terms, check_slice_equations=check_eq)
        accumulate_profile_hists(analysis, hists)
        if idx < 8:
            heads.append({
                "row": idx,
                "caps": analysis["caps"],
                "total_a_weight": analysis["total_a_weight"],
                "slice_leaks": [(r["c"], r["leak_v_rank"], r["leak_w_rank"]) for r in analysis["slice_records"]],
                "full_pure_slices": analysis["full_pure_slices"],
            })
        if not analysis["all_defect_conditions_ok"]:
            failures.append({
                "row": idx,
                "caps": analysis["caps"],
                "total_a_weight": analysis["total_a_weight"],
                "capacity_fail_slices": analysis["capacity_fail_slices"],
                "defect_fail_slices": analysis["defect_fail_slices"],
                "half_purity_fail_slices": analysis["half_purity_fail_slices"],
                "cap3_purity_fail_slices": analysis["cap3_purity_fail_slices"],
                "own_rank_fail_slices": analysis["own_rank_fail_slices"],
                "pure_shared_terms": analysis["pure_shared_terms"][:5],
            })
        if check_eq and analysis["slice_equation_fail_slices"]:
            exact_failures.append({"row": idx, "slice_equation_fail_slices": analysis["slice_equation_fail_slices"]})
    return {
        "pool_rows": int(pool.shape[0]),
        "rank": int(pool.shape[1] // 3),
        "all_rows_defect_ok": len(failures) == 0,
        "defect_failure_count": len(failures),
        "defect_failure_head": failures[:10],
        "exact_slice_equation_rows_checked": int(min(max_exact_rows, pool.shape[0])),
        "exact_slice_equation_failure_head": exact_failures[:10],
        "histograms": {name: json_counter(counter) for name, counter in hists.items()},
        "head_profiles": heads,
    }


def analyze_same_w_deletions(pool: np.ndarray) -> dict:
    inv_lams = shadow.invertible_lambda_masks()
    total = 0
    unique_supports = set()
    shadow_ok = 0
    shadow_fail = 0
    h_shadow_ok = collections.Counter()
    h_all = collections.Counter()
    survivor_categories = collections.Counter()
    survivor_leak_hist = collections.Counter()
    survivor_head = []
    survivor_violation_head = []
    survivor_pass_head = []
    combined_cleared_by_shadow_or_defect = 0
    combined_cleared_by_shadow_capacity_or_defect = 0

    for idx, row in enumerate(pool):
        terms = row_to_terms(row)
        groups = collections.defaultdict(list)
        for t, (_u, _v, w) in enumerate(terms):
            groups[int(w)].append(t)
        for w, inds in groups.items():
            if len(inds) < 2:
                continue
            for aa in range(len(inds)):
                for bb in range(aa + 1, len(inds)):
                    i_del = inds[aa]
                    j_del = inds[bb]
                    rem_terms = [terms[t] for t in range(len(terms)) if t not in (i_del, j_del)]
                    us = [u for u, _v, _w in rem_terms]
                    total += 1
                    unique_supports.add(tuple(sorted(us)))
                    sh = shadow_summary_for_support(us, inv_lams)
                    an = analyze_terms(rem_terms, check_slice_equations=False)
                    capacity_ok = an["capacity_fail_slices"] == 0
                    defect_budget_ok = an["defect_fail_slices"] == 0
                    half_ok = an["half_purity_fail_slices"] == 0
                    cap3_ok = an["cap3_purity_fail_slices"] == 0
                    own_rank_ok = an["own_rank_fail_slices"] == 0
                    pure_share_ok = len(an["pure_shared_terms"]) == 0
                    defect_all_ok = defect_budget_ok and half_ok and cap3_ok and own_rank_ok and pure_share_ok
                    if sh["ok"]:
                        shadow_ok += 1
                    else:
                        shadow_fail += 1
                    h_all[(sh["ok"], capacity_ok, defect_all_ok, an["defect_fail_slices"], an["half_purity_fail_slices"], an["cap3_purity_fail_slices"], an["own_rank_fail_slices"], len(an["pure_shared_terms"]))] += 1
                    if (not sh["ok"]) or (not defect_all_ok):
                        combined_cleared_by_shadow_or_defect += 1
                    if (not sh["ok"]) or (not capacity_ok) or (not defect_all_ok):
                        combined_cleared_by_shadow_capacity_or_defect += 1
                    if sh["ok"]:
                        h_shadow_ok[(capacity_ok, defect_all_ok, an["min_capacity"], an["total_a_weight"], an["defect_fail_slices"], an["half_purity_fail_slices"], an["cap3_purity_fail_slices"], an["own_rank_fail_slices"], len(an["pure_shared_terms"]))] += 1
                        if not capacity_ok:
                            category = "capacity_fail"
                        elif not defect_budget_ok:
                            category = "defect_budget_fail"
                        elif not half_ok:
                            category = "half_purity_fail"
                        elif not cap3_ok:
                            category = "cap3_purity_fail"
                        elif not own_rank_ok:
                            category = "own_rank_fail"
                        elif not pure_share_ok:
                            category = "pure_share_fail"
                        else:
                            category = "passes_shadow_and_inherited_defect"
                        survivor_categories[category] += 1
                        for rec in an["slice_records"]:
                            survivor_leak_hist[(rec["c"], rec["leak_v_rank"], rec["leak_w_rank"])] += 1
                        rec_summary = {
                            "pool_row": idx,
                            "deleted_terms": [i_del, j_del],
                            "deleted_w": int(w),
                            "remaining_u": us,
                            "shadow": {k: sh[k] for k in ["ok", "rank", "aug_rank", "tight_count", "tight"]},
                            "category": category,
                            "caps": an["caps"],
                            "total_a_weight": an["total_a_weight"],
                            "defect_fail_slices": an["defect_fail_slices"],
                            "half_purity_fail_slices": an["half_purity_fail_slices"],
                            "cap3_purity_fail_slices": an["cap3_purity_fail_slices"],
                            "own_rank_fail_slices": an["own_rank_fail_slices"],
                            "pure_shared_terms_head": an["pure_shared_terms"][:5],
                            "slice_leaks": [(r["c"], r["leak_v_rank"], r["leak_w_rank"], r["budget"], r["defect_ok"]) for r in an["slice_records"]],
                        }
                        if len(survivor_head) < 12:
                            survivor_head.append(rec_summary)
                        if category != "passes_shadow_and_inherited_defect" and len(survivor_violation_head) < 12:
                            survivor_violation_head.append(rec_summary)
                        if category == "passes_shadow_and_inherited_defect" and len(survivor_pass_head) < 12:
                            survivor_pass_head.append(rec_summary)

    return {
        "same_w_deletion_pairs_scanned": total,
        "unique_remaining_u_multisets": len(unique_supports),
        "shadow_ok_count": shadow_ok,
        "shadow_fail_count": shadow_fail,
        "combined_cleared_by_shadow_or_inherited_defect": combined_cleared_by_shadow_or_defect,
        "combined_cleared_by_shadow_capacity_or_inherited_defect": combined_cleared_by_shadow_capacity_or_defect,
        "shadow_ok_survivor_categories": json_counter(survivor_categories),
        "shadow_ok_detailed_hist": json_counter(h_shadow_ok),
        "all_deletion_shadow_defect_hist": json_counter(h_all),
        "shadow_ok_slice_leak_hist": json_counter(survivor_leak_hist),
        "shadow_ok_head": survivor_head,
        "shadow_ok_violation_head": survivor_violation_head,
        "shadow_ok_pass_head": survivor_pass_head,
        "interpretation_warning": "Defect/leak tests on deletion surfaces use the inherited v,w factors after deleting two equal-w terms from exact rank-21 decompositions. They are candidate-level evidence and do not exclude every possible B/C completion of the same A-support.",
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pool", type=Path, default=Path("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy"))
    ap.add_argument("--out", type=Path, default=Path("data/block_spread/defect_leak_analysis.json"))
    args = ap.parse_args()
    t0 = time.time()
    pool = np.load(args.pool)
    pool_result = analyze_pool(pool)
    deletion_result = analyze_same_w_deletions(pool)
    result = {
        "purpose": "soundness and empirical profile of the E11 defect/leak-budget lemma",
        "field": "F2",
        "convention": "T[3i+j, 3j+k, 3i+k]=1; E11 core slice s=a-1 occupies R_{a mod 3} x C_{a//3}; R,C masks [7,56,448]",
        "lemma": {
            "statement": "For exact slice equations with c active terms, dim span(v_t mod own row group) + dim span(w_t mod own column group) <= c-3.",
            "cap3": "both leak dimensions are zero, recovering analysis purity",
            "cap4": "at least one leak dimension is zero (half-purity)",
            "role": "necessary condition and parameterization guide, not sufficient for rank-19 completion",
        },
        "rank21_pool": pool_result,
        "same_w_deletions": deletion_result,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "status": "ok",
        "out": str(args.out),
        "pool_all_rows_defect_ok": pool_result["all_rows_defect_ok"],
        "pool_defect_failure_count": pool_result["defect_failure_count"],
        "pool_total_weight_hist_head": list(pool_result["histograms"]["total_weight"].items())[:10],
        "pool_by_capacity_leak_head": list(pool_result["histograms"]["by_capacity_leak"].items())[:20],
        "deletion_pairs": deletion_result["same_w_deletion_pairs_scanned"],
        "deletion_shadow_ok": deletion_result["shadow_ok_count"],
        "shadow_ok_survivor_categories": deletion_result["shadow_ok_survivor_categories"],
        "combined_cleared_by_shadow_or_inherited_defect": deletion_result["combined_cleared_by_shadow_or_inherited_defect"],
        "combined_cleared_by_shadow_capacity_or_inherited_defect": deletion_result["combined_cleared_by_shadow_capacity_or_inherited_defect"],
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
