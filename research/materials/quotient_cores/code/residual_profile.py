#!/usr/bin/env python3
r"""Profile residual Wang constraints for fixed matching strata after vertex exclusions."""
import argparse, json, pathlib, pickle, sys, time
from collections import Counter

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))
from graph_coloring_certificate import rank1_points, load_lut, iter_strata, process_stratum, make_pivot_dict, in_span_piv
from wang_capacity_lazy import unpack_basis, subspace_points_from_basis


def profile_one(lut, st, idx, max_res):
    r1 = rank1_points(); hr_list = sorted(m for m in range(1,512) if m not in r1); hr_set=set(hr_list)
    matching=[int(x) for x in st['canonical']]
    info=process_stratum(lut, matching, hr_set, hr_list)
    survivors=info['survivors']; sidx={h:i for i,h in enumerate(survivors)}
    compressed={}  # mask -> min residual
    raw=Counter(); useful=Counter(); bit_hist=Counter()
    for key,lb in lut.items():
        cap=20-int(lb); basis=unpack_basis(int(key)); piv=make_pivot_dict(basis)
        cnt=sum(1 for m in matching if in_span_piv(piv,m))
        res=cap-cnt
        if res < 0 or res > max_res:
            continue
        raw[res]+=1
        mask=0
        for p in subspace_points_from_basis(basis):
            p=int(p)
            if p in sidx:
                mask |= 1 << sidx[p]
        bc=mask.bit_count()
        if bc <= res:
            continue
        useful[res]+=1; bit_hist[(res,bc)]+=1
        old=compressed.get(mask)
        if old is None or res < old:
            compressed[mask]=res
    comp_count=Counter(compressed.values())
    return {
        'idx':idx,'k':int(st['k']),'matching':matching,'target':20-len(matching),
        'survivor_count':len(survivors),'vertex_excluded':len(info['vertex_key']),
        'raw_by_residual':dict(raw),'useful_raw_by_residual':dict(useful),
        'compressed_by_residual':dict(comp_count),'compressed_total':len(compressed),
        'bit_hist_head':[{'residual':r,'mask_size':b,'count':c} for (r,b),c in bit_hist.most_common(20)]
    }


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--indices',required=True); ap.add_argument('--max-res',type=int,default=2); ap.add_argument('--strata',default='workspace/data/matching_strata/anchored_matching_strata.json'); ap.add_argument('--lut',default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl'); ap.add_argument('--out',required=True)
    args=ap.parse_args(); wanted={int(x) for x in args.indices.replace(';',',').split(',') if x.strip()}
    lut=load_lut(pathlib.Path(args.lut)); strata=[(i,s) for i,s in iter_strata(pathlib.Path(args.strata),0) if i in wanted]
    recs=[]; t0=time.time()
    for idx,st in strata:
        ts=time.time(); rec=profile_one(lut,st,idx,args.max_res); rec['elapsed_sec']=time.time()-ts; print(json.dumps(rec,sort_keys=True)); recs.append(rec)
    payload={'max_res':args.max_res,'records':recs,'elapsed_sec':time.time()-t0}
    pathlib.Path(args.out).parent.mkdir(parents=True,exist_ok=True); pathlib.Path(args.out).write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')

if __name__=='__main__': main()
