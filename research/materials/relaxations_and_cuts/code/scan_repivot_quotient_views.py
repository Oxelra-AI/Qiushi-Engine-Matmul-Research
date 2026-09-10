#!/usr/bin/env python3
"""Scan selected full-A supports through every selected rank-2 pivot view.

For a full length-20 A-support X and each rank-2 a in X, normalize a to 17,
project X\{a} to F2^9/<17>, and replay the native rank-2 quotient Wang rows.
This looks for the scientifically valuable situation where ordinary quotient
occupation passes in another pivot view but full lift compatibility or existing
conditional cuts fail.  If all views already violate quotient occupation, the
candidate is not a source of a new lift obstruction.
"""
from __future__ import annotations
import argparse, json, struct, sys, hashlib, time
from collections import Counter, defaultdict
from pathlib import Path
ROOT=Path('research/research_record')
SCRIPTS=ROOT/'workspace/scripts'
if str(SCRIPTS) not in sys.path: sys.path.insert(0,str(SCRIPTS))
import conditional_repivot_cuts as c  # type: ignore

RANK2_ALL=Path('data/wang_native/quotient_binaries/rank2_all_n19.bin')
DEFAULT_FILES=[
ROOT/'workspace/data/quotient_lift/pivot_fixed/rank2_branch0_n20_d2cap2.json',
ROOT/'workspace/data/quotient_lift/pivot_fixed/rank2_branch2_n20_d2cap2.json',
ROOT/'workspace/data/quotient_lift/pivot_fixed/rank3_branch0_n20_d2cap2.json',
ROOT/'workspace/data/quotient_lift/conditional_cuts/rank2_branch0_global_bool_cond_d2.json',
ROOT/'workspace/data/quotient_lift/conditional_cuts/rank2_branch2_global_bool_cond_d2.json',
ROOT/'workspace/data/quotient_lift/conditional_cuts/rank3_branch0_global_bool_cond_d2.json',
ROOT/'workspace/data/quotient_lift/conditional_cuts/rank2_branch0_global_bool_cond_d3cap5_r1.json',
]
OUT=ROOT/'workspace/data/quotient_lift/conditional_cuts/repivot_quotient_view_scan.json'


def sha(path:Path):
    h=hashlib.sha256();
    with path.open('rb') as f:
        for ch in iter(lambda:f.read(1<<20),b''): h.update(ch)
    return h.hexdigest()


def load_rows(path:Path):
    data=path.read_bytes(); assert data[:8]==b'E11WANG1'
    n=struct.unpack('<I',data[8:12])[0]; rows=[]; cap_hist=Counter()
    for i in range(n):
        rec=data[12+36*i:12+36*(i+1)]
        cap=rec[0]; dim=rec[1]; words=struct.unpack('<4Q',rec[4:36]); mask=0
        for j,w in enumerate(words): mask |= int(w)<<(64*j)
        rows.append((cap,dim,mask,i)); cap_hist[cap]+=1
    return rows,{'count':n,'sha256':sha(path),'cap_hist':dict(sorted(cap_hist.items()))}


def quotient_support_for_pivot(full_support, a, normalizers):
    Pmask,Qmask,QinvTmask,P,QinvT=normalizers[a]
    pts=[]; full_images=[]
    for b in full_support:
        if b==a: continue
        gb=c.full_action(P,QinvT,b); full_images.append(gb)
        qp=c.quotient_point_from_full(gb,17)
        if qp is None:
            return None, {'error':'other_point_maps_to_pivot_or_zero','b':b,'gb':gb}
        pts.append(qp[0])
    ctr=Counter(pts)
    return pts, {'normalizer':{'Pmask':Pmask,'Qmask':Qmask,'QinvTmask':QinvTmask},'duplicate_fibers':{str(k):int(v) for k,v in ctr.items() if v>1},'full_images':full_images}


def check_qrows(qpts, rows, max_head=20):
    mask=0
    for p in qpts: mask |= 1<<p
    viol=[]; cap_hist=Counter(); dim_hist=Counter(); max_excess=0
    for cap,dim,rowmask,idx in rows:
        occ=(mask & rowmask).bit_count()
        if occ>cap:
            ex=occ-cap; max_excess=max(max_excess,ex); cap_hist[cap]+=1; dim_hist[dim]+=1
            if len(viol)<max_head: viol.append({'idx':idx,'cap':cap,'dim':dim,'occ':occ,'excess':ex})
    return {'violation_count':sum(cap_hist.values()),'max_excess':max_excess,'cap_hist':dict(sorted((str(k),int(v)) for k,v in cap_hist.items())),'dim_hist':dict(sorted((str(k),int(v)) for k,v in dim_hist.items())),'violation_head':viol}


def extract_supports(path:Path):
    d=json.loads(path.read_text()); out=[]
    for i,r in enumerate(d.get('rounds',[])):
        if 'full_A_multiset' in r:
            out.append({'round':i,'support':list(map(int,r['full_A_multiset'])),'origin_kind':'full_A_multiset','full_violation_count':r.get('full_check_stats',{}).get('violation_count')})
        elif 'support' in r:
            out.append({'round':i,'support':list(map(int,r['support'])),'origin_kind':'support','full_violation_count':r.get('full_check_stats',{}).get('violation_count')})
    return out


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--files',nargs='*',default=[str(p) for p in DEFAULT_FILES]); args=ap.parse_args()
    t0=time.time(); rows,rowmeta=load_rows(RANK2_ALL); normalizers=c.find_rank2_normalizers(); cuts,_=c.load_all_cuts(); cond,_=c.build_conditional_cut_masks(cuts)
    allrecs=[]; global_best=[]; pass_views=[]
    for path_s in args.files:
        path=Path(path_s)
        if not path.exists(): continue
        for srec in extract_supports(path):
            supp=srec['support']; rank2=[a for a in supp if c.rank_of_mask(a)==2]
            rec={'path':str(path),'round':srec['round'],'origin_kind':srec['origin_kind'],'full_violation_count':srec.get('full_violation_count'),'support':supp,'rank_hist':dict(sorted((str(k),int(v)) for k,v in Counter(c.rank_of_mask(a) for a in supp).items())),'rank2_count':len(rank2),'views':[]}
            cev=c.eval_candidate(supp,cond)
            rec['conditional_eval_summary']={'violations':cev['violations'],'max_lhs':cev['max_lhs'],'max_occ_B':cev['max_occ_B_when_active']}
            for a in rank2:
                qpts,info=quotient_support_for_pivot(supp,a,normalizers)
                if qpts is None:
                    v={'pivot_a':a,'error':info}; rec['views'].append(v); continue
                dup=info['duplicate_fibers']
                if dup:
                    chk={'violation_count':None,'duplicate_fibers':dup}
                else:
                    chk=check_qrows(qpts,rows)
                    if chk['violation_count']==0:
                        pass_views.append({'path':str(path),'round':srec['round'],'pivot_a':a,'quotient_support':sorted(qpts),'full_support':supp})
                v={'pivot_a':a,'q_support_sorted':sorted(qpts),'duplicate_fibers':dup,'quotient_check':chk,'normalizer':info['normalizer']}
                rec['views'].append(v)
                if chk.get('violation_count') is not None:
                    global_best.append({'path':str(path),'round':srec['round'],'pivot_a':a,'q_violations':chk['violation_count'],'max_excess':chk['max_excess'],'full_violation_count':srec.get('full_violation_count'),'conditional_max_lhs':cev['max_lhs'],'q_support':sorted(qpts)})
            # keep only compact best views in per-record? No, preserve all but truncate violation heads.
            allrecs.append(rec)
    global_best.sort(key=lambda r:(r['q_violations'], -r['max_excess'], r['path'], r['round'], r['pivot_a']))
    summary={'total_candidates':len(allrecs),'total_views':sum(len(r['views']) for r in allrecs),'quotient_admissible_views':len(pass_views),'best_views_head':global_best[:30]}
    out={'schema':'s0908_repivot_quotient_view_scan_v1','meaning':'Each saved full-A support is viewed from every selected rank-2 factor. A quotient-admissible view would be a candidate source for a new lift obstruction; quotient violations mean ordinary rank-2 quotient occupation already rejects that pivot view.','rank2_rows':str(RANK2_ALL),'rank2_rows_meta':rowmeta,'summary':summary,'quotient_admissible_views':pass_views,'records':allrecs,'elapsed_sec':time.time()-t0}
    OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'out':str(OUT),**summary,'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))

if __name__=='__main__': main()
