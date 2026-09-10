#!/usr/bin/env python3
r"""analysis: evaluate quotient-rank aggregate cuts on known E11-core A-lists.

This is a candidate-local scan: for each indexed A multiset, only source
contractions that are actually saturated in that A-list are used as guards.  For
each saturated source pair S={q1,q2}, side B/C, and target t, it checks

    sum_{p: t(p)=1 and q1(p)=q2(p)=0} x_p >= rank(pi_W side_space(L(t)))

where W is the sum of the source side spaces.  The target t itself need not be
saturated.  A true fixed-A decomposition must pass all such guarded inequalities.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from complete_core_and_transversal import ROOT  # noqa: E402
from quotient_rank_cuts import (  # noqa: E402
    build_contractions,
    count_on_mask,
    counts_from_A,
    load_candidate_As,
    point_mask_for_q,
    projection_rank_mod_space,
    sum_basis,
)

OUTDIR = ROOT / "workspace/data/quotient_rank_cuts"
ALLMASK = (1 << 255) - 1


def eval_candidate(
    name: str,
    A: Sequence[int],
    contractions: Dict[int, dict],
    masks: Dict[int, int],
    max_store: int = 80,
) -> dict:
    counts = counts_from_A(A)
    nonzero_q = [q for q, c in contractions.items() if int(c["rank"]) > 0]
    weights = {q: count_on_mask(counts, masks[q]) for q in nonzero_q}
    saturated = [q for q in nonzero_q if weights[q] == int(contractions[q]["rank"])]
    violations = []
    by_side = Counter()
    by_req = Counter()
    by_pair_rank = Counter()
    by_target_rank = Counter()
    guard_pairs_scanned = 0
    nontrivial_instances = 0
    # caches local to this candidate; count lhs depends on candidate but req/outside do not.
    W_cache: Dict[Tuple[str, int, int], Tuple[Tuple[int, ...], int, int]] = {}
    req_cache: Dict[Tuple[str, int, int, int], Tuple[int, int, int]] = {}

    for q1, q2 in combinations(saturated, 2):
        guard_pairs_scanned += 1
        q1, q2 = sorted((int(q1), int(q2)))
        union = masks[q1] | masks[q2]
        for side in ("B", "C"):
            side_key = "B_space" if side == "B" else "C_space"
            wk = (side, q1, q2)
            if wk not in W_cache:
                W = sum_basis([contractions[q1][side_key], contractions[q2][side_key]], 9)
                W_cache[wk] = (W, len(W), union)
            W, Wdim, union = W_cache[wk]
            if Wdim >= 9:
                continue
            for target in nonzero_q:
                rk = (side, q1, q2, int(target))
                if rk not in req_cache:
                    req = projection_rank_mod_space(contractions[target][side_key], W, 9)
                    outside = masks[target] & (~union) & ALLMASK
                    req_cache[rk] = (int(req), int(outside), int(outside.bit_count()))
                req, outside, outside_size = req_cache[rk]
                if req <= 0:
                    continue
                nontrivial_instances += 1
                lhs = count_on_mask(counts, outside)
                if lhs < req:
                    by_side[side] += 1
                    by_req[req] += 1
                    by_pair_rank[(int(contractions[q1]["rank"]), int(contractions[q2]["rank"]))] += 1
                    by_target_rank[int(contractions[target]["rank"])] += 1
                    if len(violations) < max_store:
                        violations.append({
                            "side": side,
                            "sources": [q1, q2],
                            "source_ranks": [int(contractions[q1]["rank"]), int(contractions[q2]["rank"])],
                            "source_weights": [weights[q1], weights[q2]],
                            "W_dim": Wdim,
                            "target": int(target),
                            "target_rank": int(contractions[target]["rank"]),
                            "target_weight": weights[int(target)],
                            "target_saturated": weights[int(target)] == int(contractions[int(target)]["rank"]),
                            "requirement": req,
                            "outside_lhs": int(lhs),
                            "outside_point_count": outside_size,
                            "outside_points_in_candidate": [int(p) for p, c in sorted(counts.items()) if c and ((outside >> (int(p)-1)) & 1)],
                        })
    return {
        "name": name,
        "term_count": len(A),
        "distinct_A_points": len(counts),
        "multiplicity_hist": {str(k): int(v) for k, v in sorted(Counter(counts.values()).items())},
        "saturated_contraction_count": len(saturated),
        "saturated_by_rank": {str(k): int(v) for k, v in sorted(Counter(int(contractions[q]["rank"]) for q in saturated).items())},
        "guard_source_pairs_scanned": guard_pairs_scanned,
        "nontrivial_guarded_instances": nontrivial_instances,
        "violated_guarded_instances": sum(by_side.values()),
        "violations_by_side": dict(by_side),
        "violations_by_requirement": {str(k): int(v) for k, v in sorted(by_req.items())},
        "violations_by_source_pair_rank": {f"{a},{b}": int(v) for (a,b), v in sorted(by_pair_rank.items())},
        "violations_by_target_rank": {str(k): int(v) for k, v in sorted(by_target_rank.items())},
        "violations_head": violations,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-store", type=int, default=80)
    ap.add_argument("--out", type=Path, default=OUTDIR / "candidate_quotient_cut_scan.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

    t0 = time.time()
    T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
    contractions = build_contractions(T_core)
    masks = {q: point_mask_for_q(q) for q in contractions}
    candidates = load_candidate_As()
    print(f"Loaded {len(candidates)} candidate/control A-lists")

    results = []
    for i, (name, A) in enumerate(candidates.items(), 1):
        st = time.time()
        rec = eval_candidate(name, A, contractions, masks, max_store=int(args.max_store))
        rec["elapsed_sec"] = round(time.time() - st, 3)
        results.append(rec)
        print(json.dumps({
            "idx": i,
            "name": name,
            "sat": rec["saturated_contraction_count"],
            "guard_pairs": rec["guard_source_pairs_scanned"],
            "nontriv": rec["nontrivial_guarded_instances"],
            "viol": rec["violated_guarded_instances"],
            "by_side": rec["violations_by_side"],
            "sec": rec["elapsed_sec"],
        }, sort_keys=True))

    highlight_names = [
        "cn122_E11_core_rank21_genuine",
        "v2_round5",
        "v2_long_round14",
        "v2_long_round17",
        "v2_long_round18",
    ]
    highlights = {r["name"]: r for r in results if r["name"] in highlight_names or r["violated_guarded_instances"] == 0}
    result = {
        "schema": "candidate_quotient_cut_scan_v1",
        "field": "F2",
        "core": "E11",
        "rule": "candidate-local pair-source quotient-rank inequalities with saturated source guards and no target-saturation guard",
        "candidate_count": len(candidates),
        "rank_distribution": {str(k): int(v) for k, v in sorted(Counter(c["rank"] for c in contractions.values()).items())},
        "results": results,
        "highlights": highlights,
        "total_elapsed_sec": round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Saved {args.out}")


if __name__ == "__main__":
    main()
