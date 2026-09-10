#!/usr/bin/env python3
"""Scan unconditional quotient-rank cut families for quotient support ILPs."""
from __future__ import annotations
import argparse, heapq, json, os, sys, time
from collections import Counter
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
from quotient_support_ilp import (  # type: ignore
    PIVOTS, build_contractions, gf2_rref, projection_rank_mod_space,
    point_functional_mask,
)

OUTDIR = SESSION / "workspace/data/quotient_support_ilp"
ALLMASK255 = (1 << 256) - 1


def scan(pivot_name: str, *, store_top: int, min_req: int, max_wdim: int, max_outside: int | None) -> dict[str, Any]:
    pivot = PIVOTS[pivot_name]
    t0 = time.time()
    contractions = build_contractions(pivot)
    nonzero = [q for q, rec in contractions.items() if int(rec['rank']) > 0]
    masks = {q: point_functional_mask(q) for q in nonzero}
    hist_req = Counter(); hist_w_req = Counter(); hist_out_req = Counter(); hist_side = Counter(); hist_rankpair_req = Counter()
    total_nontriv = 0; total_pass_filter = 0
    heap = []
    serial = 0
    # heap score: larger is better. use minheap of score; score tuple lexicographic.
    for ii, q1 in enumerate(nonzero):
        r1 = int(contractions[q1]['rank'])
        for q2 in nonzero[ii+1:]:
            r2 = int(contractions[q2]['rank'])
            source_union = masks[q1] | masks[q2]
            for side in ('B','C'):
                side_key = 'B_space' if side == 'B' else 'C_space'
                W = gf2_rref(list(contractions[q1][side_key]) + list(contractions[q2][side_key]), 9)
                Wdim = len(W)
                if Wdim >= 9:
                    continue
                for tgt in nonzero:
                    req = projection_rank_mod_space(contractions[tgt][side_key], W, 9)
                    if req <= 0:
                        continue
                    outside = point_functional_mask(tgt) & (~source_union) & ALLMASK255
                    outside_count = outside.bit_count()
                    total_nontriv += 1
                    hist_req[req] += 1
                    hist_w_req[(Wdim, req)] += 1
                    hist_out_req[(outside_count, req)] += 1
                    hist_side[side] += 1
                    hist_rankpair_req[(min(r1,r2), max(r1,r2), req)] += 1
                    if req < min_req or Wdim > max_wdim or (max_outside is not None and outside_count > max_outside):
                        continue
                    total_pass_filter += 1
                    if store_top <= 0:
                        continue
                    # Favor high req, small outside, small W, high source ranks. Stable negatives for minheap.
                    score = (int(req), -int(outside_count), -int(Wdim), int(r1+r2), -int(q1+q2+tgt))
                    rec = {
                        'side': side, 'sources': [int(q1), int(q2)], 'target': int(tgt),
                        'source_ranks': [r1, r2], 'W_dim': Wdim,
                        'requirement': int(req), 'outside_point_count': int(outside_count),
                    }
                    item = (score, serial, rec)
                    serial += 1
                    if len(heap) < store_top:
                        heapq.heappush(heap, item)
                    elif score > heap[0][0]:
                        heapq.heapreplace(heap, item)
    top = [rec for score, _idx, rec in sorted(heap, key=lambda x: x[0], reverse=True)]
    return {
        'schema': 'quotient_qcut_scan_v1',
        'pivot_name': pivot_name,
        'pivot': pivot,
        'total_nontrivial_pair_qcuts': int(total_nontriv),
        'filter': {'min_req': min_req, 'max_wdim': max_wdim, 'max_outside': max_outside},
        'total_pass_filter': int(total_pass_filter),
        'hist_req': {str(k): int(v) for k,v in sorted(hist_req.items())},
        'hist_wdim_req': {f'W{k[0]}_req{k[1]}': int(v) for k,v in sorted(hist_w_req.items())},
        'hist_outside_req_head': {f'out{k[0]}_req{k[1]}': int(v) for k,v in sorted(hist_out_req.items())[:200]},
        'hist_side': dict(hist_side),
        'hist_rankpair_req': {f'r{k[0]}_{k[1]}_req{k[2]}': int(v) for k,v in sorted(hist_rankpair_req.items())},
        'top_cuts': top,
        'elapsed_sec': round(time.time()-t0, 3),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--pivot-name', choices=sorted(PIVOTS), required=True)
    ap.add_argument('--store-top', type=int, default=1000)
    ap.add_argument('--min-req', type=int, default=3)
    ap.add_argument('--max-wdim', type=int, default=6)
    ap.add_argument('--max-outside', type=int, default=None)
    ap.add_argument('--out', type=Path, default=None)
    args = ap.parse_args()
    out = args.out or (OUTDIR / f'{args.pivot_name}_qcut_scan_top{args.store_top}_req{args.min_req}.json')
    out.parent.mkdir(parents=True, exist_ok=True)
    res = scan(args.pivot_name, store_top=args.store_top, min_req=args.min_req, max_wdim=args.max_wdim, max_outside=args.max_outside)
    out.write_text(json.dumps(res, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k: res[k] for k in ['pivot_name','total_nontrivial_pair_qcuts','total_pass_filter','hist_req','elapsed_sec']}, indent=2, sort_keys=True))
    print('saved', out)

if __name__ == '__main__':
    main()
