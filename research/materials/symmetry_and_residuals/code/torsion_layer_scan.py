#!/usr/bin/env python3
r"""Scan finite-order torsion-layer partitions for T_<3,3,3>.

This is the d-parameter companion to d2_torsion_layers.py.  It enumerates
all exponent patterns P,Q,R in (Z/d)^3 and partitions the 27 support triples by
(P_a-Q_b, Q_b-R_c) modulo d.  For each noncentral partition up to S_3^3 index
renaming, it uses the same merged-block lower-bound oracle as the d=2 repair:
ordinary flattenings, Koszul/exterior flattenings, rectangular subtensors, and
only the narrow Ja'Ja'--Takche additivity ARTIFACT for actual direct-sum components
where all but at most one component has a tensor factor of dimension at most 2.

The point is to test torsion layers directly, not to re-run the additive analysis
arrangement and not to assume unrestricted direct-sum additivity.
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
        label = ((P[a] - Q[b]) % d, (Q[b] - R[c]) % d)
        blocks[label].append((a, b, c))
    return tuple(sorted((tuple(sorted(v)) for v in blocks.values() if v), key=lambda B: (len(B), B)))


def is_central(P, Q, R):
    return len(set(P)) == 1 and len(set(Q)) == 1 and len(set(R)) == 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--d", type=int, required=True)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    d = args.d
    t0 = time.time()

    raw_total = d ** 9
    raw_central = 0
    raw_noncentral = 0
    raw_shape_hist = Counter()
    raw_noncentral_shape_hist = Counter()
    canonical = {}

    vals = list(range(d))
    for P in itertools.product(vals, repeat=3):
        for Q in itertools.product(vals, repeat=3):
            for R in itertools.product(vals, repeat=3):
                part = partition_mod_d(P, Q, R, d)
                raw_shape_hist[tuple(h.partition_shape(part))] += 1
                if is_central(P, Q, R):
                    raw_central += 1
                    continue
                raw_noncentral += 1
                raw_noncentral_shape_hist[tuple(h.partition_shape(part))] += 1
                can = h.canonical_partition(part)
                if can not in canonical:
                    canonical[can] = {"representative_exponents": (P, Q, R), "raw_count": 0, "partition": part}
                canonical[can]["raw_count"] += 1

    reps = []
    hist_by_table = {name: Counter() for name in h.LB_TABLES}
    low_by_table = {name: [] for name in h.LB_TABLES}
    source_hist_by_table = {name: Counter() for name in h.LB_TABLES}
    for can, rec in canonical.items():
        P, Q, R = rec["representative_exponents"]
        pat = h.analyze_pattern(P, Q, R, rec["partition"], h.LB_TABLES)
        pat["raw_count_in_noncentral_patterns"] = rec["raw_count"]
        pat["canonical_support_partition"] = [[list(t) for t in B] for B in can]
        reps.append(pat)
        for name in h.LB_TABLES:
            s = pat["by_input_table"][name]["certified_block_lb_sum"]
            hist_by_table[name][s] += rec["raw_count"]
            if s <= 22:
                low_by_table[name].append(pat)
            for b in pat["by_input_table"][name]["blocks"]:
                source_hist_by_table[name][b["certified_lb_source"]] += 1

    reps.sort(key=lambda r: (
        min(v["certified_block_lb_sum"] for v in r["by_input_table"].values()),
        r["block_sizes"], r["P_bits"], r["Q_bits"], r["R_bits"]
    ))

    min_by_table = {}
    for name in h.LB_TABLES:
        vals2 = [r["by_input_table"][name]["certified_block_lb_sum"] for r in reps]
        min_by_table[name] = min(vals2) if vals2 else None

    result = {
        "purpose": f"Direct modulo-{d} torsion-layer scan for finite-order termwise aligned De Groote symmetries of T333.",
        "field_scope": "Characteristic zero lower-bound certificates with declared small-format inputs; finite exponent partitions only.",
        "important_correction": "This scan bounds merged multiplicative blocks directly and uses only the narrow JT86 component additivity recorded in d2_torsion_layers.py.",
        "d": d,
        "raw_exponent_patterns_total": raw_total,
        "raw_central_patterns": raw_central,
        "raw_noncentral_patterns": raw_noncentral,
        "raw_partition_shape_histogram_all": {str(k): int(v) for k, v in sorted(raw_shape_hist.items())},
        "raw_partition_shape_histogram_noncentral": {str(k): int(v) for k, v in sorted(raw_noncentral_shape_hist.items())},
        "canonical_noncentral_partition_count_up_to_S3_cubed": len(reps),
        "declared_input_tables": {name: {str(k): int(v) for k, v in sorted(tab.items())} for name, tab in h.LB_TABLES.items()},
        "certified_sum_histograms_by_input_table_raw_counts": {name: {str(k): int(v) for k, v in sorted(hist.items())} for name, hist in hist_by_table.items()},
        "minimum_certified_sum_by_input_table": min_by_table,
        "patterns_with_sum_le22_by_input_table": {name: len(vals3) for name, vals3 in low_by_table.items()},
        "source_histograms_on_canonical_blocks_by_input_table": {name: {str(k): int(v) for k, v in sorted(hist.items())} for name, hist in source_hist_by_table.items()},
        "low_patterns_full_records": {name: vals3[:20] for name, vals3 in low_by_table.items()},
        "lowest_representatives_sorted": reps[:50],
        "elapsed_sec": time.time() - t0,
    }
    if args.out is None:
        out = Path(__file__).resolve().parents[1] / f"data/d2_torsion_layers/torsion_layer_d{d}_scan.json"
    else:
        out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "d": d,
        "raw_noncentral": raw_noncentral,
        "canonical_noncentral": len(reps),
        "min_by_table": min_by_table,
        "hist_by_table": {name: {str(k): int(v) for k, v in sorted(hist.items())} for name, hist in hist_by_table.items()},
        "patterns_le22": {name: len(vals3) for name, vals3 in low_by_table.items()},
        "out": str(out),
        "elapsed_sec": time.time() - t0,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
