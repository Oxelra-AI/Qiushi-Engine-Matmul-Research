#!/usr/bin/env python3
"""analysis: conditional re-pivoted lift-obstruction cuts.

The certified pivot-17 quotient cuts say: if a selected rank-2 full
A-direction is normalized to q=17, then among the remaining directions at most
11 quotient fibers from any certified 12-point obstruction cut C can occur.
For an arbitrary selected rank-2 full direction a and a normalizing tensor
automorphism g with g(a)=17, this becomes the conditional full-direction cut

    sum_{b in B(a,C)} z_b + 9 z_a <= 20,

where B(a,C)={b!=0,a : pi_17(g(b)) in C}.  If z_a=1 this is
|X cap B(a,C)|<=11; if z_a=0 it is tautological for a 20-term support.
This script generates these cuts from the two replay-certified transported
pivot-17 cut orbits and evaluates them on saved full-A candidates.
"""
from __future__ import annotations
import argparse, hashlib, json, struct, time
from collections import Counter, defaultdict
from pathlib import Path

ROOT=Path('research/research_record')
CUT_FILES=[
    ROOT/'workspace/data/quotient_lift/transport/rank2_lift_cut_transport_rows.bin',
    ROOT/'workspace/data/quotient_lift/transport/rank2_survivor2_lift_cut_transport_rows.bin',
]
DEFAULT_CANDIDATES=[
    ROOT/'workspace/data/quotient_lift/pivot_fixed/rank2_branch0_n20_d2cap2.json',
    ROOT/'workspace/data/quotient_lift/pivot_fixed/rank2_branch2_n20_d2cap2.json',
    ROOT/'workspace/data/quotient_lift/pivot_fixed/rank3_branch0_n20_d2cap2.json',
]
OUTDIR=ROOT/'workspace/data/quotient_lift/conditional_cuts'
OUTDIR.mkdir(parents=True,exist_ok=True)
PIVOT17=17


def sha_file(path:Path)->str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''):
            h.update(c)
    return h.hexdigest()


def parse_cut_binary(path:Path):
    data=path.read_bytes()
    if data[:8] != b'E11WANG1':
        raise ValueError(f'{path}: bad magic {data[:8]!r}')
    n=struct.unpack('<I',data[8:12])[0]
    if len(data) != 12 + 36*n:
        raise ValueError(f'{path}: size mismatch')
    cuts=[]
    for i in range(n):
        rec=data[12+36*i:12+36*(i+1)]
        cap=rec[0]; dim=rec[1]
        words=struct.unpack('<4Q',rec[4:36])
        mask=0
        for j,w in enumerate(words): mask |= int(w) << (64*j)
        pts=tuple(k for k in range(1,256) if (mask>>k)&1)
        if cap != 11 or len(pts) != 12:
            raise ValueError(f'{path}: unexpected cut record {i}: cap={cap} pop={len(pts)} dim={dim}')
        cuts.append({'source_file':str(path),'source_index':i,'cap':cap,'dim':dim,'points':pts,'mask':mask})
    return cuts


def bits_to_mat(mask:int):
    return [[(mask>>(3*i+j))&1 for j in range(3)] for i in range(3)]

def mat_to_bits(M):
    x=0
    for i in range(3):
        for j in range(3):
            if M[i][j]&1: x |= 1<<(3*i+j)
    return x

def transpose(A): return [[A[j][i] for j in range(3)] for i in range(3)]

def matmul(A,B):
    return [[sum(A[i][k]&B[k][j] for k in range(3))&1 for j in range(3)] for i in range(3)]

def gf2_rank_mat(A):
    M=[row[:] for row in A]; r=0
    for c in range(3):
        piv=None
        for i in range(r,3):
            if M[i][c]: piv=i; break
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]
        for i in range(3):
            if i!=r and M[i][c]:
                M[i]=[M[i][j]^M[r][j] for j in range(3)]
        r+=1
    return r

def gf2_inv(A):
    M=[row[:] + [1 if i==j else 0 for j in range(3)] for i,row in enumerate(A)]
    r=0
    for c in range(3):
        piv=None
        for i in range(r,3):
            if M[i][c]: piv=i; break
        if piv is None: raise ValueError('singular')
        M[r],M[piv]=M[piv],M[r]
        for i in range(3):
            if i!=r and M[i][c]: M[i]=[M[i][j]^M[r][j] for j in range(6)]
        r+=1
    return [row[3:] for row in M]

def gl3():
    out=[]
    for mask in range(1<<9):
        M=bits_to_mat(mask)
        if gf2_rank_mat(M)==3: out.append((mask,M))
    return out

GL3=gl3()


def full_action(P,QinvT,a:int)->int:
    # same convention as pivot_fixed_occ_cegar_int.py
    return mat_to_bits(matmul(matmul(transpose(P),bits_to_mat(a)),QinvT))


def section_lift(qpoint:int,pivot:int=PIVOT17)->int:
    h=pivot.bit_length()-1
    return (qpoint & ((1<<h)-1)) | ((qpoint>>h)<<(h+1))


def quotient_point_from_full(a:int,pivot:int=PIVOT17):
    if a==0 or a==pivot: return None
    h=pivot.bit_length()-1
    v=int(a)
    if (v>>h)&1: v ^= pivot
    if (v>>h)&1: raise AssertionError('pivot reduction failed')
    p=(v & ((1<<h)-1)) | ((v>>(h+1))<<h)
    eps=1 if (a ^ section_lift(p,pivot))==pivot else 0
    if (section_lift(p,pivot) ^ (pivot if eps else 0)) != a:
        raise AssertionError('bad lift decomposition')
    return p,eps


def rank_of_mask(a:int)->int:
    return gf2_rank_mat(bits_to_mat(a))


def find_rank2_normalizers():
    """Return a -> first (Pmask,Qmask,QinvTmask,P,QinvT) with g(a)=17."""
    rank2=[a for a in range(1,512) if rank_of_mask(a)==2]
    out={}
    for Pmask,P in GL3:
        for Qmask,Q in GL3:
            QinvT=transpose(gf2_inv(Q)); QinvTmask=mat_to_bits(QinvT)
            # This pair sends some rank-2 matrices to 17; invert map by scanning all rank2.
            for a in rank2:
                if a in out: continue
                if full_action(P,QinvT,a)==PIVOT17:
                    out[a]=(Pmask,Qmask,QinvTmask,P,QinvT)
            if len(out)==len(rank2):
                return out
    if len(out)!=len(rank2):
        raise RuntimeError(f'normalizers incomplete {len(out)}/{len(rank2)}')
    return out


def build_conditional_cut_masks(cuts):
    t0=time.time()
    normalizers=find_rank2_normalizers()
    rank2_dirs=sorted(normalizers)
    cond=[]; seen=set(); size_hist=Counter()
    for a in rank2_dirs:
        Pmask,Qmask,QinvTmask,P,QinvT=normalizers[a]
        # map every full direction b!=a to quotient point after normalization.
        image_qp={}
        for b in range(1,512):
            if b==a: continue
            gb=full_action(P,QinvT,b)
            qp=quotient_point_from_full(gb,PIVOT17)
            if qp is None:
                # should only happen for b=a since g is invertible and g(a)=17
                continue
            image_qp[b]=qp[0]
        for ci,c in enumerate(cuts):
            C=set(c['points'])
            mask=0
            for b,p in image_qp.items():
                if p in C:
                    mask |= 1<<b
            B=tuple(i for i in range(1,512) if (mask>>i)&1)
            if len(B)!=24:
                raise AssertionError(f'unexpected B size for a={a}, cut={ci}: {len(B)}')
            key=(a,mask)
            if key in seen: continue
            seen.add(key); size_hist[len(B)]+=1
            cond.append({'pivot_a':a,'cut_index':ci,'source_file':c['source_file'],'source_index':c['source_index'],
                         'B_mask_hex':hex(mask),'B_points':B,'normalizer':{'Pmask':Pmask,'Qmask':Qmask,'QinvTmask':QinvTmask}})
    return cond, {'rank2_direction_count':len(rank2_dirs),'conditional_cut_count':len(cond),
                  'B_size_hist':dict(sorted(size_hist.items())),'elapsed_sec':time.time()-t0}


def load_all_cuts():
    allcuts=[]; manifests=[]
    for f in CUT_FILES:
        cuts=parse_cut_binary(f)
        manifests.append({'path':str(f),'sha256':sha_file(f),'count':len(cuts)})
        allcuts.extend(cuts)
    # Dedup by quotient point mask.
    seen={}; uniq=[]
    for c in allcuts:
        if c['mask'] not in seen:
            seen[c['mask']]=len(uniq); uniq.append(c)
    return uniq, manifests


def eval_candidate(fullA, cond):
    ctr=Counter(map(int,fullA))
    setmask=0
    for b,c in ctr.items():
        if b>0: setmask |= 1<<b
    rank_hist=Counter(rank_of_mask(a) for a in ctr for _ in range(ctr[a]))
    mult_gt1={str(k):int(v) for k,v in ctr.items() if v>1}
    selected_rank2=sorted(a for a in ctr if rank_of_mask(a)==2)
    viol=[]; best=[]; max_occ=-1; max_lhs=-1
    for cc in cond:
        a=cc['pivot_a']; za=ctr.get(a,0)
        if za==0: continue
        Bmask=int(cc['B_mask_hex'],16)
        occ=sum(ctr.get(b,0) for b in cc['B_points'])
        lhs=occ + 9*za
        if occ>max_occ or lhs>max_lhs:
            max_occ=max(max_occ,occ); max_lhs=max(max_lhs,lhs)
        rec={'pivot_a':a,'za':za,'occ_B':occ,'lhs':lhs,'rhs':20,'cut_index':cc['cut_index'],
             'source_index':cc['source_index'],'normalizer':cc['normalizer'],
             'B_selected':sorted([b for b in cc['B_points'] if ctr.get(b,0)])}
        if lhs>20:
            viol.append(rec)
        best.append(rec)
    best.sort(key=lambda r:(-r['lhs'],-r['occ_B'],r['pivot_a'],r['cut_index']))
    by_pivot=defaultdict(lambda:{'violations':0,'max_lhs':-10,'max_occ':-1})
    for r in best:
        d=by_pivot[str(r['pivot_a'])]
        d['max_lhs']=max(d['max_lhs'],r['lhs']); d['max_occ']=max(d['max_occ'],r['occ_B'])
    for r in viol:
        by_pivot[str(r['pivot_a'])]['violations']+=1
    return {'rank_hist':dict(sorted((str(k),int(v)) for k,v in rank_hist.items())),'multiplicity_gt1':mult_gt1,
            'selected_rank2_count':len(selected_rank2),'selected_rank2':selected_rank2,
            'active_conditional_tests':len(best),'violations':len(viol),'violating_pivot_count':len({r['pivot_a'] for r in viol}),
            'max_lhs':max_lhs,'max_occ_B_when_active':max_occ,
            'by_pivot':dict(sorted(by_pivot.items(), key=lambda kv:int(kv[0]))),
            'violation_head':viol[:20],'best_head':best[:20]}


def evaluate_saved_candidates(cond, paths):
    out=[]
    for path in paths:
        data=json.loads(Path(path).read_text())
        rec={'path':str(path),'pivot_name':data.get('pivot_name'),'fixed_pivot':data.get('pivot'),
             'final_status':data.get('final_status'),'round_count':len(data.get('rounds',[])),'rounds':[]}
        for i,r in enumerate(data.get('rounds',[])):
            if 'full_A_multiset' not in r: continue
            ev=eval_candidate(r['full_A_multiset'],cond)
            ev.update({'round':i,'solver_status':r.get('status'),'active_rows':r.get('active_rows'),
                       'full_violation_count':r.get('full_check_stats',{}).get('violation_count'),
                       'quotient_support':r.get('quotient_support')})
            rec['rounds'].append(ev)
        out.append(rec)
    return out


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--out',default=str(OUTDIR/'conditional_repivot_cut_candidate_eval.json'))
    ap.add_argument('--candidates',nargs='*',default=[str(p) for p in DEFAULT_CANDIDATES])
    args=ap.parse_args(); t0=time.time()
    cuts,manifests=load_all_cuts()
    cond,stats=build_conditional_cut_masks(cuts)
    evals=evaluate_saved_candidates(cond,args.candidates)
    # Compact histograms for quick reading.
    summary=[]
    for e in evals:
        sr={'path':e['path'],'pivot_name':e['pivot_name'],'fixed_pivot':e['fixed_pivot'],'rounds':[]}
        for r in e['rounds']:
            sr['rounds'].append({'round':r['round'],'rank_hist':r['rank_hist'],'selected_rank2_count':r['selected_rank2_count'],
                                 'violations':r['violations'],'violating_pivot_count':r['violating_pivot_count'],
                                 'max_lhs':r['max_lhs'],'max_occ_B_when_active':r['max_occ_B_when_active'],
                                 'full_violation_count':r['full_violation_count']})
        summary.append(sr)
    payload={'schema':'s0908_conditional_repivot_cuts_v1','meaning':'Conditional full-direction consequences of the two certified pivot-17 lift obstruction orbits, applied around every selected rank-2 full A-factor. A violation excludes the candidate A-support as a rank-20 full decomposition necessary condition; absence of violation is not feasibility.',
             'cut_inputs':manifests,'unique_quotient_cuts':len(cuts),'generation_stats':stats,
             'candidate_evaluations':evals,'summary':summary,'elapsed_sec':time.time()-t0}
    outp=Path(args.out); outp.parent.mkdir(parents=True,exist_ok=True); outp.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'out':str(outp),'unique_quotient_cuts':len(cuts),'conditional_cut_count':stats['conditional_cut_count'],'summary':summary,'elapsed_sec':payload['elapsed_sec']},indent=2,sort_keys=True))

if __name__=='__main__': main()
