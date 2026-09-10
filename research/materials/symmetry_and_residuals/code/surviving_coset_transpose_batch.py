#!/usr/bin/env python3
"""Run surviving-coset rank-one CEGAR for transposes of the 16 normalized H cases."""
from __future__ import annotations
import argparse, json, sys, time
from pathlib import Path
from itertools import combinations
from collections import Counter
SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from surviving_coset_ansatz import load_lut, analyze_H, canonical_coset_points, h_to_firstrows, solve_rankone_cegar  # type: ignore


def transpose_mask(x:int)->int:
    y=0
    for i in range(3):
        for j in range(3):
            if (int(x)>>(3*i+j))&1:
                y |= 1<<(3*j+i)
    return y


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--outroot', type=Path, required=True)
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--binary', type=Path, default=Path('data/wang_native/full_tensor/full_wang512_cap19_len20_all_dim9_allbinding.bin'))
    ap.add_argument('--max-rounds', type=int, default=8)
    ap.add_argument('--solver-sec', type=float, default=10.0)
    ap.add_argument('--add-per-round', type=int, default=1000)
    args=ap.parse_args()
    t0=time.time(); args.outroot.mkdir(parents=True, exist_ok=True)
    lut=load_lut(args.lut)
    p, coset, rank2, rank3 = canonical_coset_points()
    Hs=[sorted(list(c2)+list(c3)) for c2 in combinations(rank2,1) for c3 in combinations(rank3,3)]
    Hs=sorted(Hs, key=lambda H: h_to_firstrows(H,p))
    records=[]
    for i,H in enumerate(Hs):
        HT=sorted(transpose_mask(x) for x in H)
        hrec=analyze_H(lut, HT, p)
        outdir=args.outroot/f'transpose_H{i:02d}'
        res=solve_rankone_cegar(lut,args.binary,hrec,outdir,args.max_rounds,args.solver_sec,args.add_per_round)
        rec={'case':i,'H_base':H,'H_transpose':HT,'H_firstrows':hrec['firstrows'],'rank_hist':hrec['rank_hist'],'pair_lb_hist':hrec['pair_lb_hist'],'triple_lb_hist':hrec['triple_lb_hist'],'allowed_rank_one_count':hrec['allowed_rank_one_count'],'final_status':res['final_status'],'rounds':len(res['rounds']),'support_rounds':sum(1 for r in res['rounds'] if 'support' in r),'out':str(outdir/'cegar_result.json')}
        records.append(rec)
        print(json.dumps(rec, sort_keys=True), flush=True)
    summary={'schema':'surviving_coset_transpose_batch_v1','count':len(records),'status_hist':dict(Counter(r['final_status'] for r in records)),'records':records,'elapsed_sec':time.time()-t0}
    out=args.outroot/'transpose_batch_summary.json'
    out.write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'out':str(out),'count':len(records),'status_hist':summary['status_hist'],'elapsed_sec':summary['elapsed_sec']}, indent=2, sort_keys=True))

if __name__=='__main__':
    main()
