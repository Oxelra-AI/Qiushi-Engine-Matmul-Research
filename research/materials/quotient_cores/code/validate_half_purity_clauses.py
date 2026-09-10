#!/usr/bin/env python3
"""Validate half-purity augmentation clauses on known rank-21 E11 decompositions.

This evaluates the added clauses only, using their intended semantics, against all
519 exact rank-21 pool rows.  It is a positive control for the clause generator; it
is not a rank-19 result.
"""
from __future__ import annotations

import json
import time
from pathlib import Path

import numpy as np

GROUP = [7, 56, 448]


def slice_block(s: int):
    a = s + 1
    return a % 3, a // 3


def row_to_terms(row):
    r = len(row)//3
    return [(int(row[3*t]), int(row[3*t+1]), int(row[3*t+2])) for t in range(r)]


def check_terms(terms):
    R = len(terms)
    fails = []
    records = []
    for s in range(8):
        j_s, i_s = slice_block(s)
        c = sum((u >> s) & 1 for u, _v, _w in terms)
        v_leak = any(((u >> s) & 1) and (v & (0x1FF ^ GROUP[j_s])) for u, v, _w in terms)
        w_leak = any(((u >> s) & 1) and (w & (0x1FF ^ GROUP[i_s])) for u, _v, w in terms)
        ok = (not (v_leak and w_leak)) or c >= 5
        records.append((c, int(v_leak), int(w_leak), ok))
        if not ok:
            fails.append({"slice": s, "capacity": c, "v_leak": v_leak, "w_leak": w_leak})
    return fails, records


def main():
    t0 = time.time()
    pool_path = Path('data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy')
    pool = np.load(pool_path)
    all_fails = []
    hist = {}
    for idx, row in enumerate(pool):
        terms = row_to_terms(row)
        fails, records = check_terms(terms)
        if fails:
            all_fails.append({"row": idx, "fails": fails})
        for rec in records:
            hist[str(rec[:3])] = hist.get(str(rec[:3]), 0) + 1
    out = Path('data/block_spread/half_purity_clause_validation_rank21.json')
    out.parent.mkdir(parents=True, exist_ok=True)
    result = {
        "purpose": "positive control for half-purity clauses VLEAK & WLEAK => capacity >= 5",
        "pool": str(pool_path),
        "pool_rows": int(pool.shape[0]),
        "fail_count": len(all_fails),
        "fail_head": all_fails[:10],
        "capacity_vleak_wleak_hist": dict(sorted(hist.items())),
        "elapsed_sec": round(time.time()-t0, 3),
    }
    out.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({"status":"ok", "out":str(out), "fail_count":len(all_fails), "hist":result["capacity_vleak_wleak_hist"], "elapsed_sec":result["elapsed_sec"]}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
