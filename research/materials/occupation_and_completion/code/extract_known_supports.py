#!/usr/bin/env python3
"""Extract A-support controls from known decompositions.

Outputs:
  workspace/data/wang_native/controls/e11_poolrow*.json
  workspace/data/wang_native/controls/full_lifted_e11_poolrow0.json
  workspace/data/wang_native/controls/full_rank23_flipcpd.json (if parsed)

The support controls are for testing enumerator solution preservation.  They do
not assert minimality.  E11 pool masks are raw 8-bit quotient masks; the lifted
full control shifts them to full bits 1..8 and adds the deleted E11 slice terms.
"""
from __future__ import annotations

import json, re
from pathlib import Path
import numpy as np

OUT = Path("data/wang_native/controls")
OUT.mkdir(parents=True, exist_ok=True)
E11_POOL = Path("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy")
R23_TXT = Path("data/flip_cpd_inspect/src/khoruzhii-flip-cpd-9eeb17f/data/schemes_paper/gg-333-rank23-rec-0-0-0-z.txt")


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def parse_linear_form(expr: str, prefix: str) -> int:
    # Over F2, signs are irrelevant.  Variables are a1..a9 or b1..b9 in the text.
    mask = 0
    for m in re.finditer(rf"{prefix}(\d+)", expr):
        idx = int(m.group(1)) - 1
        mask ^= (1 << idx)
    return mask


def parse_rank23_txt(path: Path):
    text = path.read_text()
    prod_re = re.compile(r"m(\d+)\s*=\s*\((.*?)\)\((.*?)\)")
    prods = {}
    for m in prod_re.finditer(text):
        t = int(m.group(1))
        prods[t] = {
            "u": parse_linear_form(m.group(2), "a"),
            "v": parse_linear_form(m.group(3), "b"),
            "a_expr": m.group(2),
            "b_expr": m.group(3),
        }
    c_re = re.compile(r"c(\d+)\s*=\s*(.*)")
    w_masks = {t: 0 for t in prods}
    for m in c_re.finditer(text):
        cidx = int(m.group(1)) - 1
        rhs = m.group(2)
        for mt in re.finditer(r"m(\d+)", rhs):
            t = int(mt.group(1))
            if t in w_masks:
                w_masks[t] ^= (1 << cidx)
    terms = []
    for t in sorted(prods):
        terms.append([prods[t]["u"], prods[t]["v"], w_masks[t]])
    return terms


def main():
    out_summary = {"status": "ok", "controls": []}
    pool = np.load(E11_POOL)
    for row_idx in [0, 304]:
        row = pool[row_idx]
        R = row.shape[0] // 3
        e11_terms = []
        for t in range(R):
            u = int(row[3*t]) & 0xFF
            v = int(row[3*t+1])
            w = int(row[3*t+2])
            e11_terms.append([u, v, w])
        support = [u for u, _v, _w in e11_terms if u]
        data = {
            "kind": "E11 core known rank-21 support",
            "source": str(E11_POOL),
            "row": row_idx,
            "rank": R,
            "a_multiset": support,
            "distinct_a_support": sorted(set(support)),
            "distinct_count": len(set(support)),
            "duplicate_count": len(support) - len(set(support)),
        }
        path = OUT / f"e11_poolrow{row_idx}_support.json"
        write_json(path, data)
        out_summary["controls"].append(str(path))

    # Full rank-24 control from lifting E11 row 0; useful for full length 24+ if needed.
    row = pool[0]
    R = row.shape[0] // 3
    full_a = [(int(row[3*t]) & 0xFF) << 1 for t in range(R) if (int(row[3*t]) & 0xFF)]
    full_a += [1, 1, 1]  # three deleted-slice products have the same A functional E11.
    data = {
        "kind": "Full T333 rank-24 control from E11 rank-21 lift",
        "source": str(E11_POOL),
        "row": 0,
        "rank": len(full_a),
        "a_multiset": full_a,
        "distinct_a_support": sorted(set(full_a)),
        "distinct_count": len(set(full_a)),
        "duplicate_count": len(full_a) - len(set(full_a)),
    }
    path = OUT / "full_lifted_e11_poolrow0_support.json"
    write_json(path, data)
    out_summary["controls"].append(str(path))

    if R23_TXT.exists():
        terms = parse_rank23_txt(R23_TXT)
        data = {
            "kind": "Full T333 rank-23 text scheme support parsed over F2 signs ignored",
            "source": str(R23_TXT),
            "rank": len(terms),
            "terms": terms,
            "a_multiset": [u for u, _v, _w in terms if u],
            "distinct_a_support": sorted(set(u for u, _v, _w in terms if u)),
            "distinct_count": len(set(u for u, _v, _w in terms if u)),
            "duplicate_count": len([u for u, _v, _w in terms if u]) - len(set(u for u, _v, _w in terms if u)),
            "warning": "This parses a published text scheme; exact full tensor reconstruction should be checked separately before treating as decomposition evidence. It is sufficient as an A-multiset feasibility stress test only if Wang rows accept it at length 23.",
        }
        path = OUT / "full_rank23_flipcpd_text_support.json"
        write_json(path, data)
        out_summary["controls"].append(str(path))

    print(json.dumps(out_summary, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
