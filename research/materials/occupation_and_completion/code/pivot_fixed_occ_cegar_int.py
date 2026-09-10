#!/usr/bin/env python3
"""analysis: integer pivot-fixed full A-side Wang occupation CEGAR.

Mathematical object.  Fix a full A-side pivot q in F_2^9, selected once in a
length-n full A multiset.  Every other full A direction lies in exactly one of
2 lifts of a quotient point p in F_2^9/<q>.  Variables y0_p,y1_p are
nonnegative integer multiplicities of those lifts.  For a full Wang subspace W,

  1_{q in W} + sum_{p:s(p) in W} y0_p + sum_{p:s(p)+q in W} y1_p <= n - L(W).

For n=20 the one- and two-dimensional Wang rows force the variables to become
ordinary lift bits for any feasible support, but this integer model also supports
n=23 positive controls with repeated A directions.  It scans the complete Wang
LUT directly and therefore does not use the invalid analysis exported rows.
"""
from __future__ import annotations
import argparse, hashlib, json, pickle, sys, time
from collections import Counter, defaultdict
from pathlib import Path
from ortools.sat.python import cp_model

ROOT=Path('research/research_record')
S04=Path('scripts')
if str(S04) not in sys.path: sys.path.insert(0,str(S04))
from wang_capacity_lazy import unpack_basis  # type: ignore

LUT_PATH=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')
OUTDIR=ROOT/'workspace/data/quotient_lift/pivot_fixed'
OUTDIR.mkdir(parents=True,exist_ok=True)
PIVOTS={'rank2':17,'rank3':273}


def sha_file(path:Path)->str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda:f.read(1<<20),b''):
            h.update(c)
    return h.hexdigest()

def load_lut(path:Path):
    with path.open('rb') as f: payload=pickle.load(f)
    return payload['lut'], payload.get('meta',{})

def section_lift(qpoint:int,pivot:int)->int:
    h=pivot.bit_length()-1
    return (qpoint & ((1<<h)-1)) | ((qpoint>>h)<<(h+1))

def quotient_point_from_full(a:int,pivot:int):
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

def subspace_points(basis):
    pts=[0]
    for b in basis:
        pts += [x^int(b) for x in pts]
    return pts

def reduce_by_pivots(x:int,pairs):
    y=int(x)
    for hb,b in pairs:
        if (y>>hb)&1:
            y ^= b
            if y==0: return 0
    return y

def in_span(x:int,pairs)->bool:
    return reduce_by_pivots(x,pairs)==0

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
            if i!=r and M[i][c]: M[i]=[M[i][j]^M[r][j] for j in range(3)]
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

def full_action(P,QinvT,a:int)->int:
    return mat_to_bits(matmul(matmul(transpose(P),bits_to_mat(a)),QinvT))

def load_qmm_a_masks(path:Path):
    terms=[]; cur={}
    for line in path.read_text().splitlines():
        line=line.strip()
        if line.startswith('term'):
            if cur: terms.append(cur); cur={}
        elif line.startswith('u '):
            cur['u']=[abs(int(x))&1 for x in line.split()[1:]]
    if cur: terms.append(cur)
    masks=[]
    for t in terms:
        m=0
        for i,b in enumerate(t['u']):
            if b: m |= 1<<i
        masks.append(m)
    return masks

def normalize_to_pivot(masks:list[int], pivot:int):
    if pivot in masks:
        return masks, {'already_pivot':True,'chosen_term':masks.index(pivot),'source_mask':pivot}
    prank=gf2_rank_mat(bits_to_mat(pivot)); G=gl3()
    for idx,a in enumerate(masks):
        if gf2_rank_mat(bits_to_mat(a)) != prank: continue
        for Pmask,P in G:
            for Qmask,Q in G:
                QinvT=transpose(gf2_inv(Q))
                if full_action(P,QinvT,a)==pivot:
                    return [full_action(P,QinvT,x) for x in masks], {'already_pivot':False,'chosen_term':idx,'source_mask':a,'Pmask':Pmask,'Qmask':Qmask,'QinvTmask':mat_to_bits(QinvT)}
    raise ValueError('no same-rank factor normalizes to pivot')

def row_spec_from_basis(idx:int,basis,lb:int,n:int,pivot:int):
    cap=n-int(lb)
    pairs=tuple((int(b).bit_length()-1,int(b)) for b in basis if b)
    contains_q=in_span(pivot,pairs)
    rhs=cap-(1 if contains_q else 0)
    eps0=[]; eps1=[]
    if rhs >= 0:
        for a in subspace_points(basis):
            if a==0 or a==pivot: continue
            qp=quotient_point_from_full(int(a),pivot)
            if qp is None: continue
            p,e=qp
            (eps1 if e else eps0).append(p)
    eps0=sorted(set(eps0)); eps1=sorted(set(eps1))
    active=len(set(eps0)|set(eps1))
    return {'idx':int(idx),'dim':len(basis),'lb':int(lb),'cap':int(cap),'rhs':int(rhs),'eps0':eps0,'eps1':eps1,'active':active,'contains_pivot':bool(contains_q),'basis':list(map(int,basis))}

def build_initial_rows(lut,pivot:int,n:int,initial_dim:int,initial_cap:int):
    rows=[]; seen=set(); cap_hist=Counter(); dim_hist=Counter(); skipped=Counter(); t0=time.time()
    for idx,(key,lb0) in enumerate(lut.items()):
        basis=unpack_basis(int(key)); d=len(basis); cap=n-int(lb0)
        if d>initial_dim: continue
        if cap<0 or cap>=n or cap>initial_cap: continue
        r=row_spec_from_basis(idx,basis,int(lb0),n,pivot)
        if r['rhs']>=0 and r['active']==0:
            skipped['no_active']+=1; continue
        k=(tuple(r['eps0']),tuple(r['eps1']),r['rhs'])
        if k in seen:
            skipped['duplicate']+=1; continue
        seen.add(k); rows.append(r); cap_hist[r['cap']]+=1; dim_hist[r['dim']]+=1
    return rows, {'rows':len(rows),'cap_hist':dict(sorted(cap_hist.items())),'dim_hist':dict(sorted(dim_hist.items())),'skipped':dict(skipped),'elapsed_sec':time.time()-t0}

def solve_model(rows,n:int,force_counts:dict[tuple[int,int],int],force_support:set[int],forbid:set[int],time_limit:float,seed:int):
    model=cp_model.CpModel(); ub=n-1
    y0={p:model.NewIntVar(0,ub,f'y0_{p}') for p in range(1,256)}
    y1={p:model.NewIntVar(0,ub,f'y1_{p}') for p in range(1,256)}
    model.Add(sum(y0[p]+y1[p] for p in range(1,256)) == n-1)
    for p in force_support: model.Add(y0[p]+y1[p] == 1)
    for (p,e),cnt in force_counts.items(): model.Add((y1 if e else y0)[p] == int(cnt))
    for p in forbid: model.Add(y0[p]==0); model.Add(y1[p]==0)
    for r in rows:
        if r['rhs']<0:
            model.Add(0 <= -1)
        else:
            model.Add(sum(y0[p] for p in r['eps0']) + sum(y1[p] for p in r['eps1']) <= r['rhs'])
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(time_limit); solver.parameters.num_search_workers=8; solver.parameters.random_seed=int(seed)
    t0=time.time(); st=solver.Solve(model); elapsed=time.time()-t0
    rec={'status':solver.StatusName(st),'solve_elapsed_sec':elapsed,'wall_time':solver.WallTime(),'conflicts':solver.NumConflicts(),'branches':solver.NumBranches(),'active_rows':len(rows)}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        c0={}; c1={}; qsupport=[]; bits=[]
        for p in range(1,256):
            v0=int(solver.Value(y0[p])); v1=int(solver.Value(y1[p]))
            if v0: c0[str(p)]=v0
            if v1: c1[str(p)]=v1
            if v0+v1:
                qsupport.append(p)
                # bit list only meaningful when total multiplicity is one.
                bits.append(1 if v1 and not v0 else 0)
        rec['y0_counts']=c0; rec['y1_counts']=c1; rec['quotient_support']=qsupport; rec['lift_bits_in_support_order']=bits; rec['total_selected_after_pivot']=sum(c0.values())+sum(c1.values())
    return rec

def candidate_multiset(pivot:int,c0:dict[str,int],c1:dict[str,int]):
    chosen=[pivot]
    for p_s,c in c0.items():
        chosen += [section_lift(int(p_s),pivot)]*int(c)
    for p_s,c in c1.items():
        chosen += [(section_lift(int(p_s),pivot)^pivot)]*int(c)
    return chosen

def check_candidate(lut,pivot:int,n:int,c0:dict[str,int],c1:dict[str,int],max_report:int=5000):
    chosen=candidate_multiset(pivot,c0,c1)
    viol=[]; t0=time.time(); cap_hist=Counter(); dim_hist=Counter(); excess_hist=Counter(); checked=0
    for idx,(key,lb0) in enumerate(lut.items()):
        cap=n-int(lb0)
        if cap>=n: continue
        basis=unpack_basis(int(key)); pairs=tuple((int(b).bit_length()-1,int(b)) for b in basis if b)
        occ=sum(1 for a in chosen if in_span(a,pairs))
        checked+=1
        if occ>cap:
            v={'idx':idx,'dim':len(basis),'lb':int(lb0),'cap':int(cap),'occ':int(occ),'excess':int(occ-cap),'basis':list(map(int,basis))}
            viol.append(v); cap_hist[cap]+=1; dim_hist[len(basis)]+=1; excess_hist[occ-cap]+=1
    viol.sort(key=lambda v:(-v['excess'],v['cap'],v['dim'],v['idx']))
    stats={'chosen_full_A_length':len(chosen),'checked_rows':checked,'violation_count':len(viol),'violation_cap_hist':dict(sorted((str(k),int(v)) for k,v in cap_hist.items())),'violation_dim_hist':dict(sorted((str(k),int(v)) for k,v in dim_hist.items())),'violation_excess_hist':dict(sorted((str(k),int(v)) for k,v in excess_hist.items())),'elapsed_sec':time.time()-t0}
    return viol[:max_report],stats,chosen

def parse_force_counts(s:str):
    ctr=Counter()
    for tok in s.split(','):
        if not tok.strip(): continue
        p,e=tok.split(':') if ':' in tok else (tok,'0')
        ctr[(int(p),int(e))]+=1
    return dict(ctr)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--pivot-name',choices=['rank2','rank3'],required=True)
    ap.add_argument('--n',type=int,default=20)
    ap.add_argument('--initial-dim',type=int,default=3)
    ap.add_argument('--initial-cap',type=int,default=5)
    ap.add_argument('--rounds',type=int,default=6)
    ap.add_argument('--time-per-round',type=float,default=120.0)
    ap.add_argument('--total-time',type=float,default=900.0)
    ap.add_argument('--seed',type=int,default=24200)
    ap.add_argument('--force-quotient',default='',help='comma list p:eps, multiplicities by repetition')
    ap.add_argument('--force-support',default='',help='comma list quotient points selected exactly once')
    ap.add_argument('--forbid-quotient',default='')
    ap.add_argument('--qmm-control',type=Path,default=None)
    ap.add_argument('--label',default='')
    args=ap.parse_args(); t0=time.time(); pivot=PIVOTS[args.pivot_name]
    print(f'Loading LUT {LUT_PATH}',flush=True); lut,meta=load_lut(LUT_PATH); print(f'LUT rows={len(lut)} coverage={meta.get("coverage_ok")}',flush=True)
    force_counts=parse_force_counts(args.force_quotient); force_support={int(x) for x in args.force_support.split(',') if x.strip()}; norm_info=None
    if args.qmm_control:
        masks0=load_qmm_a_masks(args.qmm_control); masks,norm_info=normalize_to_pivot(masks0,pivot)
        ctr=Counter(); pivot_count=0
        for a in masks:
            if a==pivot: pivot_count+=1; continue
            qp=quotient_point_from_full(a,pivot)
            if qp is None: continue
            ctr[qp]+=1
        force_counts=dict(ctr); force_support=set()
        print(f'qmm normalization={norm_info} pivot_count={pivot_count} forced_after_pivot={sum(ctr.values())}',flush=True)
        if pivot_count!=1 or sum(ctr.values())!=args.n-1:
            print('WARNING: qmm control does not give exactly one pivot plus n-1 quotient terms',flush=True)
    forbid={int(x) for x in args.forbid_quotient.split(',') if x.strip()}
    rows,init_stats=build_initial_rows(lut,pivot,args.n,args.initial_dim,args.initial_cap)
    row_keys={(tuple(r['eps0']),tuple(r['eps1']),r['rhs']) for r in rows}
    rounds=[]
    print(f'initial_rows={len(rows)} init_stats={init_stats} force_counts={len(force_counts)} force_support={sorted(force_support)} forbid_count={len(forbid)}',flush=True)
    for rnd in range(args.rounds):
        if time.time()-t0 >= args.total_time: break
        tl=min(args.time_per_round,args.total_time-(time.time()-t0))
        print(f'round {rnd}: active_rows={len(rows)} tl={tl:.1f}',flush=True)
        rec=solve_model(rows,args.n,force_counts,force_support,forbid,tl,args.seed+rnd)
        if 'y0_counts' not in rec:
            rounds.append(rec); print(f"  {rec['status']} no assignment",flush=True); break
        viol,stats,fullA=check_candidate(lut,pivot,args.n,rec['y0_counts'],rec['y1_counts'])
        rec['full_A_multiset']=fullA; rec['full_check_stats']=stats; rec['violation_head']=viol[:50]
        print(f"  {rec['status']} full_viol={stats['violation_count']} cap_hist={stats['violation_cap_hist']}",flush=True)
        if not viol:
            rec['fully_full_wang_admissible']=True; rounds.append(rec); break
        new=0
        for v in viol:
            r=row_spec_from_basis(v['idx'],v['basis'],v['lb'],args.n,pivot)
            if r['rhs']>=0 and r['active']==0: continue
            k=(tuple(r['eps0']),tuple(r['eps1']),r['rhs'])
            if k not in row_keys:
                row_keys.add(k); rows.append(r); new+=1
        rec['new_rows_added']=new
        rounds.append(rec)
        if new==0: break
    out={'schema':'s0908_pivot_fixed_integer_occ_cegar_v1','pivot_name':args.pivot_name,'pivot':pivot,'n':args.n,'source_lut':str(LUT_PATH),'source_lut_sha256':sha_file(LUT_PATH),'lut_coverage_ok':meta.get('coverage_ok'),'initial_dim':args.initial_dim,'initial_cap':args.initial_cap,'initial_stats':init_stats,'force_counts':{f'{p}:{e}':int(c) for (p,e),c in sorted(force_counts.items())},'force_support':sorted(force_support),'forbid_quotient':sorted(forbid),'qmm_control':str(args.qmm_control) if args.qmm_control else None,'qmm_normalization':norm_info,'rounds':rounds,'final_row_count':len(rows),'final_status':rounds[-1]['status'] if rounds else 'no_rounds','found_full_wang_admissible':any(r.get('fully_full_wang_admissible') for r in rounds),'elapsed_sec':time.time()-t0,'meaning':'A-side Wang occupation for a fixed full pivot; infeasibility is a necessary-condition exclusion, feasibility is only an A-side occupation/lift witness and not a B/C decomposition.'}
    lab=args.label or f'{args.pivot_name}_n{args.n}_d{args.initial_dim}_cap{args.initial_cap}'
    path=OUTDIR/f'{lab}.json'; path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('saved',path,flush=True)
    print(json.dumps({'final_status':out['final_status'],'rounds':len(rounds),'found_full_wang_admissible':out['found_full_wang_admissible'],'final_row_count':out['final_row_count'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True),flush=True)

if __name__=='__main__': main()
