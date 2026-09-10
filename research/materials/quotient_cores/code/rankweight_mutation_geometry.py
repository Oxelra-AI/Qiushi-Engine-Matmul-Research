#!/usr/bin/env python3
"""Sample rank-weight-feasible 19-point E11-core A-supports near a known support.

The aim is to test whether tight rank-weight contractions usually produce real
B/C factor-domain restrictions, or whether scalar rank-weight feasibility mostly
leaves the factor problem unconstrained.  This complements
`tight_rank_geometry_pilot.py` by generating supports through local swaps rather
than relying on a generic CP-SAT solve.
"""
from __future__ import annotations

import argparse, importlib.util, json, random, sys, time
from collections import Counter
from pathlib import Path

THIS = Path(__file__).resolve()
PILOT_PATH = THIS.parent / "tight_rank_geometry_pilot.py"
spec = importlib.util.spec_from_file_location("tight_pilot", PILOT_PATH)
tight = importlib.util.module_from_spec(spec)
assert spec and spec.loader
spec.loader.exec_module(tight)  # type: ignore


def rank_req_by_q():
    return {q: 3 * tight.matmul_rank3_from_mask(q) for q in range(1, 256)}


def counts_for_support(support):
    S = list(map(int, support))
    return {q: sum(tight.poppar(q & p) for p in S) for q in range(1, 256)}


def feasible_counts(counts, reqs):
    return all(counts[q] >= reqs[q] for q in reqs)


def tight_rank_hist(counts, reqs):
    hist = Counter()
    for q, req in reqs.items():
        if counts[q] == req:
            hist[tight.matmul_rank3_from_mask(q)] += 1
    return dict(sorted(hist.items()))


def margin_hist(counts, reqs):
    return dict(sorted(Counter(counts[q] - reqs[q] for q in reqs).items()))


def walk(seed_support, steps, burn, collect, seed):
    rng = random.Random(seed)
    reqs = rank_req_by_q()
    support = set(map(int, seed_support))
    counts = counts_for_support(support)
    if not feasible_counts(counts, reqs):
        raise ValueError("seed support is not rank-weight feasible")
    outside = set(range(1, 256)) - support
    collected = []
    accepted = 0
    attempted = 0
    seen = {tuple(sorted(support))}
    for step in range(1, steps + 1):
        attempted += 1
        out = rng.choice(tuple(support))
        inn = rng.choice(tuple(outside))
        new_counts = {}
        ok = True
        for q in range(1, 256):
            delta = tight.poppar(q & inn) - tight.poppar(q & out)
            val = counts[q] + delta
            if val < reqs[q]:
                ok = False
                break
            new_counts[q] = val
        if ok:
            support.remove(out); support.add(inn)
            outside.remove(inn); outside.add(out)
            counts.update(new_counts)
            accepted += 1
            key = tuple(sorted(support))
            if step > burn and key not in seen:
                seen.add(key)
                collected.append(list(key))
                if len(collected) >= collect:
                    break
    return collected, {"attempted": attempted, "accepted": accepted, "acceptance_rate": accepted / max(1, attempted), "seen_count": len(seen)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--outdir", type=Path, default=Path("data/tight_rank_geometry"))
    ap.add_argument("--steps", type=int, default=50000)
    ap.add_argument("--burn", type=int, default=1000)
    ap.add_argument("--collect", type=int, default=40)
    ap.add_argument("--seed", type=int, default=90804)
    ap.add_argument("--analyze", type=int, default=20)
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)

    seed_support = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]
    core_slices = tight.build_core_tensor()
    reqs = rank_req_by_q()
    seed_counts = counts_for_support(seed_support)
    print("seed feasible", feasible_counts(seed_counts, reqs), "tight", tight_rank_hist(seed_counts, reqs), "margin", margin_hist(seed_counts, reqs))

    samples, walk_meta = walk(seed_support, args.steps, args.burn, args.collect, args.seed)
    print("walk_meta", json.dumps(walk_meta, sort_keys=True), "samples", len(samples))

    records = []
    summaries = []
    supports_to_analyze = [seed_support] + samples[:args.analyze]
    for i, sup in enumerate(supports_to_analyze):
        label = "seed_L15_near_support" if i == 0 else f"swap_rankweight_sample_{i-1}"
        counts = counts_for_support(sup)
        rec = tight.analyze_A_support(label, sup, core_slices, None, max_tight_records=10)
        records.append(rec)
        summary = {
            "label": label,
            "support": sup,
            "A_weight_hist": rec["A_weight_hist"],
            "tight_rank_hist_from_counts": tight_rank_hist(counts, reqs),
            "margin_hist": margin_hist(counts, reqs),
            "tight_count": rec["rank_weight"]["tight_count"],
            "tight_by_matrix_rank": rec["rank_weight"]["tight_by_matrix_rank"],
            "domain_hist": rec["domain_summary"]["term_domain_dims_hist"],
            "zero_terms": len(rec["domain_summary"]["zero_domain_terms"]),
            "linear": rec["linear_membership"]["necessary_linear_test_passed"],
            "affine_dim": rec["linear_membership"]["affine_solution_dimension_if_consistent"],
            "trans_fail": rec["transversal_test"]["failure_count_reported"],
        }
        summaries.append(summary)
        print("summary", json.dumps({k: summary[k] for k in summary if k != "support"}, sort_keys=True))

    aggregate = {
        "analyzed_count": len(summaries),
        "linear_pass_count": sum(1 for s in summaries if s["linear"]),
        "any_domain_restriction_count": sum(1 for s in summaries if s["domain_hist"] != {"B9_C9": 19}),
        "zero_terms_count": sum(1 for s in summaries if s["zero_terms"] > 0),
        "trans_fail_count": sum(1 for s in summaries if s["trans_fail"] > 0),
        "tight_hist_over_samples": dict(sorted(Counter(s["tight_count"] for s in summaries).items())),
        "tight_rank_hist_over_samples": dict(sorted(Counter(str(s["tight_by_matrix_rank"]) for s in summaries).items())),
        "domain_hist_over_samples": dict(sorted(Counter(str(s["domain_hist"]) for s in summaries).items())),
    }
    payload = {
        "schema": "rankweight_mutation_geometry_v1",
        "field": "F2",
        "purpose": "Local-swap sampling of 19-point supports satisfying all scalar rank-weight inequalities, followed by tight-contraction domain analysis.",
        "seed_support": seed_support,
        "walk_meta": walk_meta,
        "sample_supports": samples,
        "summaries": summaries,
        "aggregate": aggregate,
        "records": records,
        "limits": [
            "These supports satisfy only scalar rank-weight inequalities, not the complete Wang occupation table unless separately checked.",
            "Domain/linear/transversal passes are necessary fixed-A conditions only, not rank-one decompositions.",
        ],
    }
    out = args.outdir / "rankweight_mutation_geometry.json"
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(out), "walk_meta": walk_meta, "aggregate": aggregate}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
