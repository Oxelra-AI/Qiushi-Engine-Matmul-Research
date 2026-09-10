#!/usr/bin/env python3
"""Account for rows skipped by the analysis rep2 staged CP-SAT preprocessor.

The analysis result records 8,282,848 constraining rows out of a complete
8,283,458-row Wang LUT.  This script explains the 610-row difference under
prefix {1,2}: rows are skipped if the residual capacity is negative (already a
prefix contradiction) or if the row contains no enough free candidates to bind
(`residual >= #candidate-points-in-row`).
"""
from __future__ import annotations

import json
import pickle
import sys
from collections import Counter
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))
from wang_capacity_lazy import unpack_basis, subspace_points_from_basis


def main():
    lut_path = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
    out_path = Path("data/corrected_strategy/rep2_constraining_row_account.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    prefix = {1, 2}
    candidates = set(range(1, 512)) - prefix
    with lut_path.open("rb") as f:
        payload = pickle.load(f)
    lut = {int(k): int(v) for k, v in payload["lut"].items()}

    counts = Counter()
    skip_trivial = Counter()
    skip_neg = Counter()
    constraining_by_dim_lb_res = Counter()
    examples = {"trivial": [], "negative": []}

    for key, lb in lut.items():
        basis = unpack_basis(key)
        pts = set(subspace_points_from_basis(basis))
        cap = 20 - int(lb)
        prefix_occ = len(pts & prefix)
        residual = cap - prefix_occ
        ci_len = len(pts & candidates)
        dim = len(basis)
        tag = (dim, int(lb), cap, prefix_occ, residual, ci_len)
        if residual < 0:
            counts["negative_residual"] += 1
            skip_neg[(dim, int(lb), prefix_occ, residual, ci_len)] += 1
            if len(examples["negative"]) < 20:
                examples["negative"].append({"key_hex": hex(int(key)), "basis": list(basis), "dim": dim, "lb": int(lb), "cap": cap, "prefix_occ": prefix_occ, "residual": residual, "candidate_count_in_row": ci_len})
        elif residual >= ci_len:
            counts["nonbinding_trivial"] += 1
            skip_trivial[(dim, int(lb), prefix_occ, residual, ci_len)] += 1
            if len(examples["trivial"]) < 30:
                examples["trivial"].append({"key_hex": hex(int(key)), "basis": list(basis), "dim": dim, "lb": int(lb), "cap": cap, "prefix_occ": prefix_occ, "residual": residual, "candidate_count_in_row": ci_len})
        else:
            counts["constraining"] += 1
            constraining_by_dim_lb_res[(dim, int(lb), residual)] += 1

    result = {
        "schema": "rep2_constraining_row_account_v1",
        "prefix": [1, 2],
        "lut_rows": len(lut),
        "counts": dict(counts),
        "difference_complete_minus_constraining": len(lut) - counts["constraining"],
        "skip_trivial_by_dim_lb_prefixocc_residual_cilen": [
            {"count": c, "dim": k[0], "lb": k[1], "prefix_occ": k[2], "residual": k[3], "candidate_count_in_row": k[4]}
            for k, c in skip_trivial.most_common()
        ],
        "skip_negative_by_dim_lb_prefixocc_residual_cilen": [
            {"count": c, "dim": k[0], "lb": k[1], "prefix_occ": k[2], "residual": k[3], "candidate_count_in_row": k[4]}
            for k, c in skip_neg.most_common()
        ],
        "constraining_by_dim_lb_residual_top": [
            {"count": c, "dim": k[0], "lb": k[1], "residual": k[2]}
            for k, c in constraining_by_dim_lb_res.most_common(30)
        ],
        "examples": examples,
    }
    out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(out_path), "counts": result["counts"], "difference": result["difference_complete_minus_constraining"]}, sort_keys=True))


if __name__ == "__main__":
    main()
