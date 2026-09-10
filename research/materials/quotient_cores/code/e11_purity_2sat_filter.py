#!/usr/bin/env python3
"""Purity-side 2-SAT filter for E11 core A-supports.

This is a this investigation implementation inspired by the accompanying mathematical analysis,
using the defect/leak lemma from research_record analysis.

For each slice s we use variables B_s, C_s meaning that all active B-side
(v) factors lie in the slice row group R_j, respectively all active C-side (w)
factors lie in the slice column group C_i.  For capacity 3, both are forced;
for capacity 4, B_s OR C_s is forced.  If a nonzero term is active in two
slices with different row groups, those slices cannot both be B-pure; if their
column groups differ, they cannot both be C-pure.

The cap-5 extension uses cap-3 pure slices to give lower bounds on the leak
excess of a neighboring slice: if a cap-5 slice shares with cap-3 slices from
both non-own row groups, its B-excess is at least 2 and hence C-pure is forced;
analogously for columns.  More generally, if cap-3 sharing lower bounds exceed
c-3, the support is rejected.

All conclusions here are necessary support-level tests for nonzero rank-one
terms.  They do not certify existence of B/C completions.
"""
from __future__ import annotations

import argparse
import collections
import json
import random
import sys
import time
from itertools import combinations
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
import e11_shadow_filter as shadow  # noqa: E402

NS = 8


def slice_block(s: int) -> Tuple[int, int]:
    a = s + 1
    return a % 3, a // 3


SLICE_BLOCKS = [slice_block(s) for s in range(NS)]
CROSS_PAIRS = [
    (a, b) for a, b in combinations(range(NS), 2)
    if SLICE_BLOCKS[a][0] != SLICE_BLOCKS[b][0] and SLICE_BLOCKS[a][1] != SLICE_BLOCKS[b][1]
]
LATIN_TRIPLES = [
    tri for tri in combinations(range(NS), 3)
    if len({SLICE_BLOCKS[s][0] for s in tri}) == 3 and len({SLICE_BLOCKS[s][1] for s in tri}) == 3
]


def row_to_terms(row: Sequence[int]) -> List[Tuple[int, int, int]]:
    r = len(row) // 3
    return [(int(row[3*t]), int(row[3*t+1]), int(row[3*t+2])) for t in range(r)]


def support_capacities(us: Sequence[int]) -> List[int]:
    return [sum((int(u) >> s) & 1 for u in us) for s in range(NS)]


def support_sharing(us: Sequence[int]) -> set[Tuple[int, int]]:
    out = set()
    for u0 in us:
        u = int(u0)
        active = [s for s in range(NS) if (u >> s) & 1]
        for a, b in combinations(active, 2):
            out.add((a, b) if a < b else (b, a))
    return out


def lit_name(lit: int) -> str:
    v = abs(lit) - 1
    side = 'B' if v % 2 == 0 else 'C'
    s = v // 2
    return ('' if lit > 0 else '~') + f'{side}{s}'


def solve_2sat(clauses: List[List[int]], nvars: int = 16) -> Tuple[bool, Optional[List[bool]], dict]:
    """Implication-graph 2-SAT with unit clauses allowed."""
    # Encode unit x as (x or x).  Literal integer convention: +/- (var+1).
    adj = [[] for _ in range(2 * nvars)]
    radj = [[] for _ in range(2 * nvars)]

    def idx(lit: int) -> int:
        v = abs(lit) - 1
        is_pos = lit > 0
        # index 2*v = false literal, 2*v+1 = true literal
        return 2*v + (1 if is_pos else 0)

    def neg_idx(i: int) -> int:
        return i ^ 1

    for cl in clauses:
        if len(cl) == 1:
            a = cl[0]; b = cl[0]
        elif len(cl) == 2:
            a, b = cl
        else:
            raise ValueError(f"non-2 clause {cl}")
        ia, ib = idx(a), idx(b)
        nia, nib = neg_idx(ia), neg_idx(ib)
        # ~a -> b; ~b -> a
        adj[nia].append(ib); radj[ib].append(nia)
        adj[nib].append(ia); radj[ia].append(nib)

    order = []
    seen = [False] * (2 * nvars)
    sys.setrecursionlimit(10000)

    def dfs(v):
        seen[v] = True
        for w in adj[v]:
            if not seen[w]:
                dfs(w)
        order.append(v)

    for v in range(2 * nvars):
        if not seen[v]:
            dfs(v)

    comp = [-1] * (2 * nvars)

    def rdfs(v, c):
        comp[v] = c
        for w in radj[v]:
            if comp[w] < 0:
                rdfs(w, c)

    c = 0
    for v in reversed(order):
        if comp[v] < 0:
            rdfs(v, c); c += 1

    for v in range(nvars):
        if comp[2*v] == comp[2*v + 1]:
            # Extract a small witness variable; not necessarily a minimal UNSAT core.
            return False, None, {"conflict_var": v, "conflict_name": ('B' if v % 2 == 0 else 'C') + str(v//2), "components": c}

    assignment = [False] * nvars
    for v in range(nvars):
        assignment[v] = comp[2*v] < comp[2*v + 1]
    return True, assignment, {"components": c}


def build_purity_clauses(us: Sequence[int], extended: bool = False) -> dict:
    caps = support_capacities(us)
    sharing = support_sharing(us)
    clauses: List[List[int]] = []
    reasons = []
    hard_reject_reasons = []

    # Basic capacity is independent of 2-SAT and strictly support-level.
    bad_caps = [s for s, c in enumerate(caps) if c < 3]
    if bad_caps:
        hard_reject_reasons.append({"type": "capacity_lt3", "slices": bad_caps, "caps": [caps[s] for s in bad_caps]})

    def B(s: int) -> int:
        return 2*s + 1

    def C(s: int) -> int:
        return 2*s + 2

    for s, c in enumerate(caps):
        if c == 3:
            clauses.append([B(s)]); reasons.append({"clause": [B(s)], "type": "cap3_B_unit", "slice": s})
            clauses.append([C(s)]); reasons.append({"clause": [C(s)], "type": "cap3_C_unit", "slice": s})
        elif c == 4:
            clauses.append([B(s), C(s)]); reasons.append({"clause": [B(s), C(s)], "type": "cap4_half_purity", "slice": s})

    for s1, s2 in sorted(sharing):
        j1, i1 = SLICE_BLOCKS[s1]
        j2, i2 = SLICE_BLOCKS[s2]
        if j1 != j2:
            clauses.append([-B(s1), -B(s2)])
            reasons.append({"clause": [-B(s1), -B(s2)], "type": "shared_diff_row_not_both_B", "pair": [s1, s2]})
        if i1 != i2:
            clauses.append([-C(s1), -C(s2)])
            reasons.append({"clause": [-C(s1), -C(s2)], "type": "shared_diff_col_not_both_C", "pair": [s1, s2]})

    ext_units = []
    ext_excess_rejects = []
    if extended:
        cap3_slices = [s for s, c in enumerate(caps) if c == 3]
        # For each slice, cap3 sharing gives row/column leak dimension lower bounds.
        for s, c in enumerate(caps):
            if c < 5:
                continue
            j_s, i_s = SLICE_BLOCKS[s]
            row_groups = set()
            col_groups = set()
            for r in cap3_slices:
                if r == s:
                    continue
                pair = (r, s) if r < s else (s, r)
                if pair not in sharing:
                    continue
                j_r, i_r = SLICE_BLOCKS[r]
                if j_r != j_s:
                    row_groups.add(j_r)
                if i_r != i_s:
                    col_groups.add(i_r)
            lbB = len(row_groups)
            lbC = len(col_groups)
            budget = c - 3
            if lbB + lbC > budget:
                ext_excess_rejects.append({"slice": s, "capacity": c, "row_leak_lb": lbB, "col_leak_lb": lbC, "budget": budget})
            # If one side already uses the whole budget, the other side must be pure.
            if lbB == budget and budget > 0:
                clauses.append([C(s)])
                unit = {"clause": [C(s)], "type": "cap3_sharing_forces_C_pure", "slice": s, "capacity": c, "row_leak_lb": lbB, "budget": budget}
                reasons.append(unit); ext_units.append(unit)
            if lbC == budget and budget > 0:
                clauses.append([B(s)])
                unit = {"clause": [B(s)], "type": "cap3_sharing_forces_B_pure", "slice": s, "capacity": c, "col_leak_lb": lbC, "budget": budget}
                reasons.append(unit); ext_units.append(unit)
        if ext_excess_rejects:
            hard_reject_reasons.append({"type": "cap3_sharing_excess_lb_exceeds_budget", "witnesses": ext_excess_rejects[:8], "count": len(ext_excess_rejects)})

    sat, assignment, solver_info = solve_2sat(clauses)
    # Obstruction summaries for UNSAT cases.
    cross_obs = []
    latin_obs = []
    for s1, s2 in CROSS_PAIRS:
        if (s1, s2) not in sharing:
            continue
        if (caps[s1] == 3 and caps[s2] == 4) or (caps[s2] == 3 and caps[s1] == 4):
            cross_obs.append([s1, s2])
    for tri in LATIN_TRIPLES:
        if all(caps[s] <= 4 for s in tri) and all(((a, b) if a < b else (b, a)) in sharing for a, b in combinations(tri, 2)):
            latin_obs.append(list(tri))

    return {
        "caps": caps,
        "total_weight": sum(caps),
        "sharing_count": len(sharing),
        "sharing": [list(p) for p in sorted(sharing)],
        "clauses": clauses,
        "reasons_head": reasons[:50],
        "n_clauses": len(clauses),
        "capacity_ok": not bad_caps,
        "hard_reject": bool(hard_reject_reasons),
        "hard_reject_reasons": hard_reject_reasons,
        "twosat_sat": sat,
        "twosat_assignment": None if assignment is None else {('B' if v % 2 == 0 else 'C') + str(v//2): bool(val) for v, val in enumerate(assignment)},
        "solver_info": solver_info,
        "cross_cap3_cap4_obstructions": cross_obs,
        "latin_triple_obstructions": latin_obs,
        "extended_units": ext_units,
        "rejects_support": bool(hard_reject_reasons) or not sat,
    }


def bitrow(row: Sequence[int]) -> int:
    x = 0
    for i, b in enumerate(row):
        if int(b) & 1:
            x |= 1 << i
    return x


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


def consistent_int(rows: List[int], rhs: List[int], nvars: int):
    rA = rank_int(rows)
    rB = rank_int([row | ((int(b)&1) << nvars) for row, b in zip(rows, rhs)])
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


def analyze_pool(pool: np.ndarray) -> dict:
    base_hist = collections.Counter()
    ext_hist = collections.Counter()
    failures = []
    ext_failures = []
    for idx, row in enumerate(pool):
        terms = row_to_terms(row)
        us = [u for u, _v, _w in terms]
        base = build_purity_clauses(us, extended=False)
        ext = build_purity_clauses(us, extended=True)
        base_hist[(base["capacity_ok"], base["twosat_sat"], base["rejects_support"], min(base["caps"]), base["total_weight"])] += 1
        ext_hist[(ext["capacity_ok"], ext["twosat_sat"], ext["rejects_support"], min(ext["caps"]), ext["total_weight"], len(ext["extended_units"]))] += 1
        if base["rejects_support"]:
            failures.append({"row": idx, **{k: base[k] for k in ["caps", "total_weight", "capacity_ok", "twosat_sat", "cross_cap3_cap4_obstructions", "latin_triple_obstructions"]}})
        if ext["rejects_support"]:
            ext_failures.append({"row": idx, **{k: ext[k] for k in ["caps", "total_weight", "capacity_ok", "twosat_sat", "hard_reject_reasons", "extended_units"]}})
    return {
        "rows": int(pool.shape[0]),
        "rank": int(pool.shape[1] // 3),
        "base_all_pass": len(failures) == 0,
        "base_failure_head": failures[:10],
        "extended_all_pass": len(ext_failures) == 0,
        "extended_failure_head": ext_failures[:10],
        "base_hist": {str(k): int(v) for k, v in sorted(base_hist.items(), key=lambda kv: str(kv[0]))},
        "extended_hist": {str(k): int(v) for k, v in sorted(ext_hist.items(), key=lambda kv: str(kv[0]))},
    }


def analyze_same_w_deletions(pool: np.ndarray) -> dict:
    inv_lams = shadow.invertible_lambda_masks()
    total = 0
    unique = set()
    hist = collections.Counter()
    survivor_hist = collections.Counter()
    survivor_head = []
    strict_support_reject_examples = []
    passes_shadow_support_head = []
    shadow_ok_count = 0
    shadow_ok_base_reject = 0
    shadow_ok_ext_reject = 0
    shadow_ok_capacity_reject = 0
    shadow_ok_base_2sat_reject = 0
    shadow_ok_ext_extra_reject = 0
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
                    i_del, j_del = inds[aa], inds[bb]
                    rem = [terms[t] for t in range(len(terms)) if t not in (i_del, j_del)]
                    us = [u for u, _v, _w in rem]
                    total += 1
                    unique.add(tuple(sorted(us)))
                    sh = shadow_summary_for_support(us, inv_lams)
                    base = build_purity_clauses(us, extended=False)
                    ext = build_purity_clauses(us, extended=True)
                    key = (sh["ok"], base["capacity_ok"], base["twosat_sat"], base["rejects_support"], ext["twosat_sat"], ext["rejects_support"], min(base["caps"]), base["total_weight"])
                    hist[key] += 1
                    if sh["ok"]:
                        shadow_ok_count += 1
                        if not base["capacity_ok"]:
                            shadow_ok_capacity_reject += 1
                        if base["capacity_ok"] and (not base["twosat_sat"]):
                            shadow_ok_base_2sat_reject += 1
                        if base["rejects_support"]:
                            shadow_ok_base_reject += 1
                        if ext["rejects_support"]:
                            shadow_ok_ext_reject += 1
                        if (not base["rejects_support"]) and ext["rejects_support"]:
                            shadow_ok_ext_extra_reject += 1
                        if base["rejects_support"]:
                            if len(strict_support_reject_examples) < 12:
                                strict_support_reject_examples.append({
                                    "pool_row": idx,
                                    "deleted_terms": [i_del, j_del],
                                    "deleted_w": int(w),
                                    "remaining_u": us,
                                    "shadow": {k: sh[k] for k in ["ok", "rank", "aug_rank", "tight_count", "tight"]},
                                    "base": {k: base[k] for k in ["caps", "total_weight", "capacity_ok", "twosat_sat", "hard_reject_reasons", "cross_cap3_cap4_obstructions", "latin_triple_obstructions", "n_clauses"]},
                                    "extended": {k: ext[k] for k in ["twosat_sat", "hard_reject_reasons", "extended_units"]},
                                })
                        else:
                            if len(passes_shadow_support_head) < 12:
                                passes_shadow_support_head.append({
                                    "pool_row": idx,
                                    "deleted_terms": [i_del, j_del],
                                    "deleted_w": int(w),
                                    "remaining_u": us,
                                    "shadow": {k: sh[k] for k in ["ok", "rank", "aug_rank", "tight_count", "tight"]},
                                    "base": {k: base[k] for k in ["caps", "total_weight", "capacity_ok", "twosat_sat", "n_clauses", "twosat_assignment"]},
                                    "extended": {k: ext[k] for k in ["twosat_sat", "hard_reject_reasons", "extended_units", "rejects_support"]},
                                })
                    if len(survivor_head) < 20:
                        survivor_head.append({
                            "pool_row": idx,
                            "deleted_terms": [i_del, j_del],
                            "shadow_ok": sh["ok"],
                            "caps": base["caps"],
                            "base_reject": base["rejects_support"],
                            "ext_reject": ext["rejects_support"],
                            "cross_obs": base["cross_cap3_cap4_obstructions"],
                            "latin_obs": base["latin_triple_obstructions"],
                        })
                    if sh["ok"]:
                        survivor_hist[(base["capacity_ok"], base["twosat_sat"], base["rejects_support"], ext["twosat_sat"], ext["rejects_support"], min(base["caps"]), base["total_weight"])] += 1
    return {
        "same_w_deletion_pairs_scanned": total,
        "unique_remaining_u_multisets": len(unique),
        "shadow_ok_count": shadow_ok_count,
        "shadow_fail_count": total - shadow_ok_count,
        "shadow_ok_base_support_reject_count": shadow_ok_base_reject,
        "shadow_ok_extended_support_reject_count": shadow_ok_ext_reject,
        "shadow_ok_capacity_reject_count": shadow_ok_capacity_reject,
        "shadow_ok_base_2sat_reject_count": shadow_ok_base_2sat_reject,
        "shadow_ok_extended_extra_reject_count": shadow_ok_ext_extra_reject,
        "shadow_ok_pass_base_support_count": shadow_ok_count - shadow_ok_base_reject,
        "shadow_ok_pass_extended_support_count": shadow_ok_count - shadow_ok_ext_reject,
        "all_hist": {str(k): int(v) for k, v in sorted(hist.items(), key=lambda kv: str(kv[0]))},
        "shadow_ok_hist": {str(k): int(v) for k, v in sorted(survivor_hist.items(), key=lambda kv: str(kv[0]))},
        "shadow_ok_strict_support_reject_examples": strict_support_reject_examples,
        "shadow_ok_pass_support_examples": passes_shadow_support_head,
        "records_head": survivor_head,
    }


def random_low_weight_test(n_samples: int = 2000, seed: int = 6) -> dict:
    rng = random.Random(seed)
    points_by_weight = {w: [u for u in range(1, 256) if int(u).bit_count() == w] for w in range(1, 9)}
    # Bias toward the low total-weight rank-19 regime by drawing from weights 1,2,3.
    valid = 0
    base_reject = 0
    ext_reject = 0
    weight_hist = collections.Counter()
    reject_by_weight = collections.Counter()
    pass_examples = []
    for _ in range(n_samples):
        # choose a target total weight between 27 and 40, then greedily sample distinct points.
        target = rng.randint(27, 40)
        # Start with 19 weight-1/2/3 choices adjusted to target; rejection sampling is simple here.
        for _attempt in range(200):
            us = []
            total = 0
            available = set(range(1, 256))
            for t in range(19):
                remaining = 19 - t
                min_needed = remaining - 1
                max_allowed = target - total - min_needed
                possible_weights = [w for w in [1, 2, 3, 4] if w <= max_allowed and points_by_weight[w]]
                if not possible_weights:
                    break
                w = rng.choice(possible_weights)
                candidates = [u for u in points_by_weight[w] if u in available]
                if not candidates:
                    break
                u = rng.choice(candidates)
                available.remove(u); us.append(u); total += w
            if len(us) == 19 and total == target:
                break
        else:
            continue
        base = build_purity_clauses(us, extended=False)
        if not base["capacity_ok"]:
            continue
        valid += 1
        ext = build_purity_clauses(us, extended=True)
        weight_hist[target] += 1
        if base["rejects_support"]:
            base_reject += 1
            reject_by_weight[(target, 'base')] += 1
        if ext["rejects_support"]:
            ext_reject += 1
            reject_by_weight[(target, 'ext')] += 1
        if (not ext["rejects_support"]) and len(pass_examples) < 5:
            pass_examples.append({"u": us, "caps": base["caps"], "total_weight": target, "base_clauses": base["n_clauses"], "extended_units": ext["extended_units"]})
    return {
        "samples_requested": n_samples,
        "valid_capacity_supports": valid,
        "base_reject_count": base_reject,
        "extended_reject_count": ext_reject,
        "base_reject_rate": None if valid == 0 else base_reject / valid,
        "extended_reject_rate": None if valid == 0 else ext_reject / valid,
        "weight_hist": {str(k): int(v) for k, v in sorted(weight_hist.items())},
        "reject_by_weight": {str(k): int(v) for k, v in sorted(reject_by_weight.items(), key=lambda kv: str(kv[0]))},
        "pass_examples": pass_examples,
        "warning": "Random low-weight samples are not Wang-filtered and are only a calibration of the 2-SAT obstruction, not a complete support-frontier count.",
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pool', type=Path, default=Path('data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy'))
    ap.add_argument('--out', type=Path, default=Path('data/block_spread/purity_2sat_filter.json'))
    ap.add_argument('--random-samples', type=int, default=3000)
    args = ap.parse_args()
    t0 = time.time()
    pool = np.load(args.pool)
    result = {
        "purpose": "support-level purity-side 2-SAT filter for E11 core, with cap-5 cap3-sharing extension",
        "field": "F2",
        "slice_blocks": {str(s): list(SLICE_BLOCKS[s]) for s in range(NS)},
        "cross_pairs": [list(p) for p in CROSS_PAIRS],
        "latin_triples": [list(t) for t in LATIN_TRIPLES],
        "logic": {
            "B_s": "slice s is B/v-pure: active v factors lie in its row group",
            "C_s": "slice s is C/w-pure: active w factors lie in its column group",
            "cap3": "B_s and C_s forced",
            "cap4": "B_s or C_s forced",
            "sharing": "shared nonzero term between different row groups forbids both B-pure; different column groups forbids both C-pure",
            "cap5_extension": "cap3 sharing in both non-own row groups forces C-pure for a cap5 slice; column analogue forces B-pure; excess lower bound exceeding c-3 rejects",
        },
        "rank21_pool": analyze_pool(pool),
        "same_w_deletions": analyze_same_w_deletions(pool),
        "random_low_weight_calibration": random_low_weight_test(args.random_samples) if args.random_samples else None,
        "interpretation": "UNSAT/capacity rejection is a strict necessary support-level obstruction under nonzero term semantics. Passing the filter does not imply B/C completion. The same-W deletion family is local, not a global cover of rank-19 supports.",
        "elapsed_sec": round(time.time() - t0, 3),
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    sd = result["same_w_deletions"]
    print(json.dumps({
        "status": "ok",
        "out": str(args.out),
        "rank21_base_all_pass": result["rank21_pool"]["base_all_pass"],
        "rank21_extended_all_pass": result["rank21_pool"]["extended_all_pass"],
        "same_w_pairs": sd["same_w_deletion_pairs_scanned"],
        "same_w_shadow_ok": sd["shadow_ok_count"],
        "shadow_ok_capacity_reject": sd["shadow_ok_capacity_reject_count"],
        "shadow_ok_base_2sat_reject": sd["shadow_ok_base_2sat_reject_count"],
        "shadow_ok_extended_extra_reject": sd["shadow_ok_extended_extra_reject_count"],
        "shadow_ok_pass_base": sd["shadow_ok_pass_base_support_count"],
        "shadow_ok_pass_extended": sd["shadow_ok_pass_extended_support_count"],
        "random_valid": None if result["random_low_weight_calibration"] is None else result["random_low_weight_calibration"]["valid_capacity_supports"],
        "random_base_reject_rate": None if result["random_low_weight_calibration"] is None else result["random_low_weight_calibration"]["base_reject_rate"],
        "random_extended_reject_rate": None if result["random_low_weight_calibration"] is None else result["random_low_weight_calibration"]["extended_reject_rate"],
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
