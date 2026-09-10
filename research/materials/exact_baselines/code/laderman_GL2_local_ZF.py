#!/usr/bin/env python3
"""analysis: local GL2-basis variation of the transported Laderman anti planes.

The anti bivectors of the eight Laderman free orbits span L_anti.  Changing the
basis (v,w) -> (av+bw, cv+dw) on a fixed plane preserves the projective bivector
(up to det), but changes the two tau-free rank-one slice generators and hence the
fixed-square compatibility variety Z(F) = {xP(x) in F+L1}.

This script exhaustively changes one of the eight planes over F3 and computes the
exact Z(F) quotient rank.  It is a local test of whether the Laderman Z-rank-3
configuration improves under a one-plane symmetric-basis move; it is not a global
search over anti-feasible planes.
"""
from __future__ import annotations
import argparse, json, importlib.util, time
from pathlib import Path
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "zF_search"
OUT.mkdir(parents=True, exist_ok=True)

spec = importlib.util.spec_from_file_location("zcore", SCRIPT_DIR / "zF_laderman_anti_span_search.py")
z = importlib.util.module_from_spec(spec)
spec.loader.exec_module(z)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--p', type=int, default=3)
    ap.add_argument('--time-budget', type=float, default=600.0)
    args = ap.parse_args()
    p = args.p
    t0 = time.time()

    L1 = z.build_L1(p)
    Lsym, Lanti81 = z.build_Lsym_Lanti_81(p)
    Xproj, Sq = z.precompute_fixed_squares(p)
    lad_pairs, lad_terms, delta, R = z.laderman_free_pairs_vectors(p)
    gl2s = z.GL2_list(p)
    identity = (1,0,0,1,1)

    base = z.analyze_configuration(p, lad_pairs, Xproj, Sq, L1, Lsym, Lanti81, f_allowed=6, want_replay=False)
    hist = {}
    records = []
    best = []
    timed_out = False
    total = 0
    for plane_idx in range(len(lad_pairs)):
        for g in gl2s:
            if g == identity:
                continue
            if time.time() - t0 > args.time_budget:
                timed_out = True
                break
            pairs = list(lad_pairs)
            pairs[plane_idx] = z.apply_GL2(lad_pairs[plane_idx], g, p)
            rec = z.analyze_configuration(p, pairs, Xproj, Sq, L1, Lsym, Lanti81, f_allowed=6, want_replay=False)
            total += 1
            key = (rec['F_cap_L1_dim'], rec['quotient_dimension_qdim'], rec['Z_fixed_squares_count_over_Fp'], rec['Z_quotient_rank'])
            hist[str(key)] = hist.get(str(key), 0) + 1
            compact = {
                'plane_idx_0based': int(plane_idx),
                'plane_pair_1based': [z.FREE_PAIRS[plane_idx][0]+1, z.FREE_PAIRS[plane_idx][1]+1],
                'GL2': [int(x) for x in g[:4]],
                'det': int(g[4]),
                'record': {k: rec[k] for k in rec if k not in ('replay','selected_Z_indices_for_basis')},
                'selected_Z_indices_for_basis': rec['selected_Z_indices_for_basis'],
            }
            score = (rec['rank22_condition_met_by_Z'], rec['Z_quotient_rank'], rec['Z_fixed_squares_count_over_Fp'], rec['F_cap_L1_dim'])
            compact['score'] = [int(score[0]), int(score[1]), int(score[2]), int(score[3])]
            best.append(compact)
            best = sorted(best, key=lambda x: tuple(x['score']), reverse=True)[:20]
        if timed_out:
            break

    out = {
        'field': f'F_{p}',
        'scaled_transport_delta': int(delta),
        'scaled_transport_R_columns': R.astype(int).tolist(),
        'GL2_size': len(gl2s),
        'base_laderman_record': base,
        'single_plane_moves_tested': int(total),
        'timed_out': bool(timed_out),
        'histogram_(Fcap,qdim,Zcount,Zqrank)': hist,
        'best_single_plane_moves': best,
        'interpretation': 'Single-plane GL2 changes preserve the anti planes but alter F. This tests local improvement of Z(F) around Laderman; it does not vary the anti bivector planes themselves.'
    }
    path = OUT / f'laderman_GL2_single_plane_ZF_F{p}.json'
    path.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps(out, indent=2))
    print(f'SAVED {path}')

if __name__ == '__main__':
    main()
