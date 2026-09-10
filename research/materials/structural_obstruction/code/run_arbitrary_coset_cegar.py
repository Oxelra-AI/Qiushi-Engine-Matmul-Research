#!/usr/bin/env python3
"""Run surviving-coset rank-one CEGAR for an explicitly supplied high-rank H."""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from surviving_coset_ansatz import load_lut, analyze_H, canonical_coset_points, solve_rankone_cegar  # type: ignore


def parse_list(s: str):
    return [int(x) for x in s.split(',') if x.strip()]


def transpose_mask(x: int) -> int:
    y = 0
    for i in range(3):
        for j in range(3):
            if (x >> (3*i+j)) & 1:
                y |= 1 << (3*j+i)
    return y


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--H', required=True, help='comma-separated H masks, or prefix transpose:comma-list')
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--binary', type=Path, default=Path('data/wang_native/full_tensor/full_wang512_cap19_len20_all_dim9_allbinding.bin'))
    ap.add_argument('--outdir', type=Path, required=True)
    ap.add_argument('--max-rounds', type=int, default=8)
    ap.add_argument('--solver-sec', type=float, default=10.0)
    ap.add_argument('--add-per-round', type=int, default=1000)
    args = ap.parse_args()
    Harg = args.H
    transposed = False
    if Harg.startswith('transpose:'):
        transposed = True
        H = [transpose_mask(x) for x in parse_list(Harg.split(':', 1)[1])]
    else:
        H = parse_list(Harg)
    lut = load_lut(args.lut)
    p = canonical_coset_points()[0]
    hrec = analyze_H(lut, H, p)
    res = solve_rankone_cegar(lut, args.binary, hrec, args.outdir, args.max_rounds, args.solver_sec, args.add_per_round)
    meta = {
        'H': H,
        'transposed_input': transposed,
        'rank_hist': hrec['rank_hist'],
        'pair_lb_hist': hrec['pair_lb_hist'],
        'triple_lb_hist': hrec['triple_lb_hist'],
        'allowed_rank_one_count': hrec['allowed_rank_one_count'],
        'final_status': res['final_status'],
        'rounds': len(res['rounds']),
        'out': str(args.outdir / 'cegar_result.json'),
    }
    (args.outdir / 'arbitrary_meta.json').write_text(json.dumps(meta, indent=2, sort_keys=True) + '\n')
    print(json.dumps(meta, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
