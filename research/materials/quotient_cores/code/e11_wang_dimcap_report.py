#!/usr/bin/env python3
"""Report E11 Wang lower-bound/cap distributions by quotient dimension.

This is a lightweight audit file for the support-enumeration route.  It avoids
pool data and only decodes the Wang LUT rows containing the deleted E11 line.
"""
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

S04_SCRIPTS = Path("scripts")
if str(S04_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(S04_SCRIPTS))
from core_capacity_from_wang_lut import load_lut  # type: ignore

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUTDIR = Path("data/wang_validation")
OUTDIR.mkdir(parents=True, exist_ok=True)
MASK9 = (1 << 9) - 1
N = 19


def contains_e11(key: int) -> bool:
    d = key & 0xF
    return d > 0 and ((key >> (4 + 9 * (d - 1))) & MASK9) == 1


def main():
    lut, _ = load_lut(LUT_PATH)
    by_dim_lb = defaultdict(Counter)
    by_dim_cap = defaultdict(Counter)
    by_lb_dim = defaultdict(Counter)
    for k, lb in lut.items():
        if not contains_e11(k):
            continue
        dim8 = (k & 0xF) - 1
        cap = N - lb
        by_dim_lb[dim8][lb] += 1
        by_dim_cap[dim8][cap] += 1
        by_lb_dim[lb][dim8] += 1
    out = {
        "status":"ok",
        "cap_def":"cap19=19-LB",
        "by_dim8_lb": {str(d): dict(sorted((int(k), int(v)) for k,v in c.items())) for d,c in sorted(by_dim_lb.items())},
        "by_dim8_cap19": {str(d): dict(sorted((int(k), int(v)) for k,v in c.items())) for d,c in sorted(by_dim_cap.items())},
        "by_lb_dim8": {str(lb): dict(sorted((int(k), int(v)) for k,v in c.items())) for lb,c in sorted(by_lb_dim.items())},
    }
    path = OUTDIR / "e11_wang_dimcap_report.json"
    path.write_text(json.dumps(out, indent=2, sort_keys=True))
    print(json.dumps(out, indent=2, sort_keys=True))
    print(f"Saved {path}")

if __name__ == "__main__":
    main()
