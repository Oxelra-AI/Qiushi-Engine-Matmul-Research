#!/usr/bin/env python3
r"""Fast normalized torsion-layer scan for finite-order termwise aligned weights.

For exponent modulus d, independent translations of P,Q,R do not change the
support partition, only the labels.  Thus we set P0=Q0=R0=0 and scan d^6
patterns instead of d^9.  We first deduplicate raw partitions, then canonicalize
under S_3^3 only once per raw partition.
"""
from __future__ import annotations

import argparse
import importlib.util
import itertools
import json
import time
from collections import Counter, defaultdict
from pathlib import Path

HELPER_PATH = Path(__file__).resolve().with_name("d2_torsion_layers.py")
spec = importlib.util.spec_from_file_location("d2helper", HELPER_PATH)
h = importlib.util.module_from_spec(spec)
spec.loader.exec_module(h)


def partition_mod_d(P, Q, R, d):
    blocks = defaultdict(list)
    for a, b, c in h.TRIPLES:
        blocks[((P[a] - Q[b]) % d, (Q[b] - R[c]) % d)].append((a, b, c))
    return tuple(sorted((tuple(sorted(v)) for v in blocks.values() if v), key=lambda B: (len(B), B)))


def block_signature(B):
    return tuple(B)


def analyze_pattern_cached(P, Q, R, partition, lb_tables, block_cache):
    out = {
        "P_exponents_normalized": list(P),
        "Q_exponents_normalized": list(Q),
        "R_exponents_normalized": list(R),
        "central_normalized": len(set(P)) == 1 and len(set(Q)) == 1 and len(set(R)) == 1,
        "block_sizes": h.partition_shape(partition),
        "num_blocks": len(partition),
        "by_input_table": {},
    }
    for name, table in lb_tables.items():
        blocks = []
        for B in partition:
            key = (name, block_signature(B))
            if key not in block_cache:
                block_cache[key] = h.analyze_block(B, table)
            blocks.append(block_cache[key])
        blocks = sorted(blocks, key=lambda r: (-r["certified_lb"], -r["support_size"], r["support"]))
        out["by_input_table"][name] = {
            "certified_block_lb_sum": int(sum(b["certified_lb"] for b in blocks)),
            "flattening_lb_sum": int(sum(b["flattening_lb"] for b in blocks)),
            "koszul_lb_sum": int(sum(b["best_koszul_lb"] for b in blocks)),
            "rectangular_subtensor_lb_sum": int(sum(b["best_rectangular_subtensor_lb"] for b in blocks)),
            "blocks": blocks,
        }
    return out


def scan_d(d: int, keep: int):
    t0 = time.time()
    raw_parts = {}
    vals = range(d)
    normalized_total = d ** 6
    norm_shape_hist = Counter()
    norm_central = 0
    norm_noncentral = 0
    for p1, p2, q1, q2, r1, r2 in itertools.product(vals, repeat=6):
        P = (0, p1, p2)
        Q = (0, q1, q2)
        R = (0, r1, r2)
        part = partition_mod_d(P, Q, R, d)
        norm_shape_hist[tuple(h.partition_shape(part))] += 1
        if len(set(P)) == 1 and len(set(Q)) == 1 and len(set(R)) == 1:
            norm_central += 1
            continue
        norm_noncentral += 1
        if part not in raw_parts:
            raw_parts[part] = {"representative": (P, Q, R), "normalized_count": 0}
        raw_parts[part]["normalized_count"] += 1

    canonical = {}
    for part, rec in raw_parts.items():
        can = h.canonical_partition(part)
        if can not in canonical:
            canonical[can] = {"representative": rec["representative"], "normalized_count": 0, "partition": part}
        canonical[can]["normalized_count"] += rec["normalized_count"]

    block_cache = {}
    reps = []
    hist_by_table = {name: Counter() for name in h.LB_TABLES}
    low_by_table = {name: [] for name in h.LB_TABLES}
    source_hist_by_table = {name: Counter() for name in h.LB_TABLES}
    for can, rec in canonical.items():
        P, Q, R = rec["representative"]
        pat = analyze_pattern_cached(P, Q, R, rec["partition"], h.LB_TABLES, block_cache)
        pat["normalized_count"] = rec["normalized_count"]
        pat["raw_count_d9_patterns"] = rec["normalized_count"] * (d ** 3)
        pat["canonical_support_partition"] = [[list(t) for t in B] for B in can]
        reps.append(pat)
        for name in h.LB_TABLES:
            s = pat["by_input_table"][name]["certified_block_lb_sum"]
            hist_by_table[name][s] += pat["raw_count_d9_patterns"]
            if s <= 22:
                low_by_table[name].append(pat)
            for b in pat["by_input_table"][name]["blocks"]:
                source_hist_by_table[name][b["certified_lb_source"]] += 1

    reps.sort(key=lambda r: (
        min(v["certified_block_lb_sum"] for v in r["by_input_table"].values()),
        r["block_sizes"],
        r["P_exponents_normalized"], r["Q_exponents_normalized"], r["R_exponents_normalized"],
    ))
    min_by_table = {name: (min([r["by_input_table"][name]["certified_block_lb_sum"] for r in reps]) if reps else None) for name in h.LB_TABLES}

    return {
        "purpose": f"Fast normalized modulo-{d} torsion-layer scan for finite-order termwise aligned De Groote weights of T333.",
        "d": d,
        "normalization": "P0=Q0=R0=0; multiply normalized counts by d^3 for raw exponent-pattern counts.",
        "important_correction": "Merged multiplicative blocks are bounded directly.  Direct-sum additivity is used only for actual support-hypergraph components satisfying the JT86 dimension <=2 condition.",
        "normalized_patterns_total": normalized_total,
        "normalized_central_patterns": norm_central,
        "normalized_noncentral_patterns": norm_noncentral,
        "raw_exponent_patterns_total_d9": d ** 9,
        "raw_central_patterns_d9": norm_central * d ** 3,
        "raw_noncentral_patterns_d9": norm_noncentral * d ** 3,
        "unique_raw_partitions_before_S3_cubed": len(raw_parts),
        "canonical_noncentral_partition_count_up_to_S3_cubed": len(reps),
        "normalized_partition_shape_histogram_all": {str(k): int(v) for k, v in sorted(norm_shape_hist.items())},
        "declared_input_tables": {name: {str(k): int(v) for k, v in sorted(tab.items())} for name, tab in h.LB_TABLES.items()},
        "certified_sum_histograms_by_input_table_raw_d9_counts": {name: {str(k): int(v) for k, v in sorted(hist.items())} for name, hist in hist_by_table.items()},
        "minimum_certified_sum_by_input_table": min_by_table,
        "patterns_with_sum_le22_by_input_table": {name: len(vals) for name, vals in low_by_table.items()},
        "source_histograms_on_canonical_blocks_by_input_table": {name: {str(k): int(v) for k, v in sorted(hist.items())} for name, hist in source_hist_by_table.items()},
        "low_patterns_full_records": {name: vals[:keep] for name, vals in low_by_table.items()},
        "lowest_representatives_sorted": reps[:keep],
        "elapsed_sec": time.time() - t0,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--d", type=int, action="append", required=True, help="Modulus to scan; may repeat")
    ap.add_argument("--keep", type=int, default=50)
    ap.add_argument("--out-dir", default=None)
    args = ap.parse_args()
    out_dir = Path(args.out_dir) if args.out_dir else Path(__file__).resolve().parents[1] / "data/d2_torsion_layers"
    out_dir.mkdir(parents=True, exist_ok=True)
    summaries = []
    for d in args.d:
        res = scan_d(d, args.keep)
        out = out_dir / f"torsion_layer_d{d}_scan_fast.json"
        out.write_text(json.dumps(res, indent=2, sort_keys=True) + "\n")
        summary = {
            "d": d,
            "canonical_noncentral": res["canonical_noncentral_partition_count_up_to_S3_cubed"],
            "unique_raw_partitions": res["unique_raw_partitions_before_S3_cubed"],
            "raw_noncentral_d9": res["raw_noncentral_patterns_d9"],
            "min_by_table": res["minimum_certified_sum_by_input_table"],
            "patterns_le22": res["patterns_with_sum_le22_by_input_table"],
            "hist_weak": res["certified_sum_histograms_by_input_table_raw_d9_counts"]["v3_declared_(14,8,6)"],
            "out": str(out),
            "elapsed_sec": res["elapsed_sec"],
        }
        summaries.append(summary)
        print(json.dumps(summary, indent=2, sort_keys=True))
    if len(summaries) > 1:
        out = out_dir / "torsion_layer_fast_summary.json"
        out.write_text(json.dumps(summaries, indent=2, sort_keys=True) + "\n")
        print("summary", out)


if __name__ == "__main__":
    main()
