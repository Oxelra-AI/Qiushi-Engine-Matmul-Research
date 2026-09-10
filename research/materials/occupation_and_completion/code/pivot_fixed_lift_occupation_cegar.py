#!/usr/bin/env python3
"""analysis: pivot-fixed full A-side occupation/lift CEGAR.

For a fixed full A pivot q (rank2 mask 17 or rank3 mask 273), a length-n full
A-support containing q is represented by variables y0_p,y1_p for quotient
points p=1..255.  y0/y1 select the two lifts s(p) and s(p)+q; q itself is a
separate fixed selected term.  Thus sum_p(y0_p+y1_p)=n-1 and y0_p+y1_p<=1.

Every full Wang row W gives:
  [q in W] + sum_{p: s(p) in W} y0_p + sum_{p: s(p)+q in W} y1_p <= n - L(W).
Rows containing q are quotient rows with the pivot contribution subtracted;
rows not containing q are lift-bit constraints.  This script adds rows lazily
from the full 9D Wang LUT.  It is intended as an independent single-instance
model and positive-control check, not as a final proof certificate.
"""
from __future__ import annotations
import argparse, hashlib, json, pickle, sys, time
from collections import Counter
from pathlib import Path
from ortools.sat.python import cp_model

ROOT=Path('research/research_record')
S04=Path('scripts')
if str(S04) not in sys.path: sys.path.insert(0,str(S04))
from wang_capacity_lazy import unpack_basis, rref_basis  # type: ignore

LUT_PATH=Path('data/wang_f2_lb20/wang_subspace_lut.pkl')
OUTDIR=ROOT/'workspace/data/quotient_lift/pivot_fixed'
OUTDIR.mkdir(parents=True, exist_ok=True)
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

def section_lift(qpoint:int, pivot:int)->int:
    h=pivot.bit_length()-1
    return (qpoint & ((1<<h)-1)) | ((qpoint>>h)<<(h+1))

def reduce_by_pairs(x:int, pairs):
    y=int(x)
    for hb,b in pairs:
        if (y>>hb)&1:
            y ^= b
            if y==0: return 0
    return y

def in_span(x:int,pairs)->bool:
    return reduce_by_pairs(x,pairs)==0

def parse_support(s:str):
    if not s: return None
    return [int(x) for x in s.split(',') if x.strip()]

def bits_to_mat(mask:int):
    return [[(mask>>(3*i+j))&1 for j in range(3)] for i in range(3)]

def mat_to_bits(M):
    x=0
    for i in range(3):
        for j in range(3):
            if M[i][j]&1: x |= 1<<(3*i+j)
    return x

def matmul(A,B):
    return [[sum(A[i][k]&B[k][j] for k in range(3))&1 for j in range(3)] for i in range(3)]

def transpose(A): return [[A[j][i] for j in range(3)] for i in range(3)]

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
            if i!=r and M[i][c]:
                M[i]=[M[i][j]^M[r][j] for j in range(6)]
        r+=1
    return [row[3:] for row in M]

def gl3_mats():
    out=[]
    for mask in range(1<<9):
        M=bits_to_mat(mask)
        if gf2_rank_mat(M)==3: out.append((mask,M))
    return out

def full_action_masks(P,QinvT,a:int)->int:
    return mat_to_bits(matmul(matmul(transpose(P), bits_to_mat(a)), QinvT))

def normalize_masks_to_pivot(masks:list[int], pivot:int):
    prank=gf2_rank_mat(bits_to_mat(pivot))
    G=gl3_mats()
    for idx,a in enumerate(masks):
        if gf2_rank_mat(bits_to_mat(a)) != prank: continue
        for Pmask,P in G:
            for Qmask,Q in G:
                QinvT=transpose(gf2_inv(Q))
                if full_action_masks(P,QinvT,a)==pivot:
                    tm=[full_action_masks(P,QinvT,x) for x in masks]
                    return tm, {'chosen_term':idx,'source_mask':a,'Pmask':Pmask,'Qmask':Qmask,'QinvTmask':mat_to_bits(QinvT)}
    raise ValueError(f'no same-rank qmm A factor can be moved to pivot {pivot}')

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
            if b&1: m |= 1<<i
        masks.append(m)
    return masks

def quotient_point_from_full(a:int, pivot:int):
    if a==0: return None
    h=pivot.bit_length()-1
    # quotient coordinate is high-pivot section: remove bit h after reducing by pivot if needed.
    v=int(a)
    if (v>>h)&1:
        v ^= pivot
    if (v>>h)&1:
        raise AssertionError('pivot reduction failed')
    q=(v & ((1<<h)-1)) | ((v>>(h+1))<<h)
    if q==0:
        return None
    # lift bit epsilon satisfies a = section(q)+epsilon*pivot
    eps=1 if (a ^ section_lift(q,pivot))==pivot else 0
    if section_lift(q,pivot) ^ (eps*pivot) != a:
        raise AssertionError('bad quotient/lift decomposition')
    return q, eps

def init_rows(lut:dict, pivot:int, n:int, initial_dim:int, initial_cap:int, progress:int=0):
    """Build initial row specs from small dimension/cap rows."""
    specs=[]; seen=set(); stats=Counter(); cap_hist=Counter(); dim_hist=Counter(); t0=time.time()
    for idx,(key,lb0) in enumerate(lut.items()):
        basis=unpack_basis(int(key)); d=len(basis); lb=int(lb0); cap=n-lb
        if d>initial_dim or cap>initial_cap or cap>=n or cap<0:
            continue
        pairs=tuple((int(b).bit_length()-1,int(b)) for b in basis if b)
        rhs=cap - (1 if in_span(pivot,pairs) else 0)
        if rhs < 0:
            specs.append({'idx':idx,'basis':list(map(int,basis)),'dim':d,'lb':lb,'cap':cap,'rhs':rhs,'eps0':[],'eps1':[],'active':0,'contains_pivot':True})
            continue
        eps0=[]; eps1=[]
        for p in range(1,256):
            a0=section_lift(p,pivot); a1=a0^pivot
            b0=in_span(a0,pairs); b1=in_span(a1,pairs)
            if b0 and b1 and not in_span(pivot,pairs):
                raise AssertionError('nonpivot row contains both lifts')
            if b0: eps0.append(p)
            if b1: eps1.append(p)
        key2=(tuple(eps0),tuple(eps1),rhs)
        # preserve one source for identical constraints.
        if key2 in seen: continue
        seen.add(key2)
        active=len(set(eps0)|set(eps1))
        # keep even if active<=rhs? those are tautological for y variables; skip to reduce model.
        if active<=rhs: continue
        specs.append({'idx':idx,'basis':list(map(int,basis)),'dim':d,'lb':lb,'cap':cap,'rhs':rhs,'eps0':eps0,'eps1':eps1,'active':active,'contains_pivot':in_span(pivot,pairs)})
        stats['rows']+=1; cap_hist[cap]+=1; dim_hist[d]+=1
    return specs, {'dedup_initial_rows':len(specs),'cap_hist':dict(cap_hist),'dim_hist':dict(dim_hist),'stats':dict(stats)}

def solve(rows, n:int, force_assign:list[tuple[int,int]], force_support:set[int], forbid_pts:set[int], time_limit:float, seed:int):
    model=cp_model.CpModel()
    y0={p:model.NewBoolVar(f'y0_{p}') for p in range(1,256)}
    y1={p:model.NewBoolVar(f'y1_{p}') for p in range(1,256)}
    for p in range(1,256): model.Add(y0[p]+y1[p] <= 1)
    model.Add(sum(y0[p]+y1[p] for p in range(1,256)) == n-1)
    for p in force_support:
        model.Add(y0[p] + y1[p] == 1)
    for p,e in force_assign:
        model.Add((y1 if e else y0)[p] == 1)
        model.Add((y0 if e else y1)[p] == 0)
    for p in forbid_pts:
        model.Add(y0[p] == 0); model.Add(y1[p] == 0)
    for r in rows:
        if r['rhs'] < 0:
            model.Add(0 <= -1)
        else:
            model.Add(sum(y0[p] for p in r['eps0']) + sum(y1[p] for p in r['eps1']) <= int(r['rhs']))
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(time_limit); solver.parameters.num_search_workers=8; solver.parameters.random_seed=int(seed)
    t0=time.time(); st=solver.Solve(model); elapsed=time.time()-t0
    rec={'status':solver.StatusName(st),'solve_elapsed_sec':elapsed,'wall_time':solver.WallTime(),'conflicts':solver.NumConflicts(),'branches':solver.NumBranches(),'active_rows':len(rows)}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        supp=[]; bits=[]
        for p in range(1,256):
            v0=solver.Value(y0[p]); v1=solver.Value(y1[p])
            if v0 or v1:
                supp.append(p); bits.append(1 if v1 else 0)
        rec['quotient_support']=supp; rec['lift_bits_in_support_order']=bits
        rec['full_A_support']=[section_lift(p,0) for p in []] # placeholder overwritten below by caller if desired
    return rec

def check_candidate(lut:dict, pivot:int, n:int, qsupport:list[int], bits:list[int], max_report:int=1000):
    chosen=[pivot]
    for p,e in zip(qsupport,bits):
        chosen.append(section_lift(p,pivot) ^ (pivot if e else 0))
    cmask=set(chosen)
    violations=[]; checked=0; t0=time.time()
    for idx,(key,lb0) in enumerate(lut.items()):
        lb=int(lb0); cap=n-lb
        if cap>=n: continue
        basis=unpack_basis(int(key)); pairs=tuple((int(b).bit_length()-1,int(b)) for b in basis if b)
        occ=sum(1 for a in chosen if in_span(a,pairs))
        if occ>cap:
            violations.append({'idx':idx,'dim':len(basis),'lb':lb,'cap':cap,'occ':occ,'excess':occ-cap,'basis':list(map(int,basis))})
        checked+=1
    violations.sort(key=lambda v:(-v['excess'], v['cap'], v['dim'], v['idx']))
    stats={'checked_rows':checked,'violation_count':len(violations),'violation_cap_hist':{str(k):int(v) for k,v in sorted(Counter(vv['cap'] for vv in violations).items())},'violation_dim_hist':{str(k):int(v) for k,v in sorted(Counter(vv['dim'] for vv in violations).items())},'elapsed_sec':time.time()-t0}
    return violations[:max_report], stats, chosen

def row_from_violation(pivot:int, n:int, v:dict):
    basis=v['basis']; pairs=tuple((int(b).bit_length()-1,int(b)) for b in basis if b)
    rhs=int(v['cap']) - (1 if in_span(pivot,pairs) else 0)
    eps0=[]; eps1=[]
    for p in range(1,256):
        a0=section_lift(p,pivot); a1=a0^pivot
        if in_span(a0,pairs): eps0.append(p)
        if in_span(a1,pairs): eps1.append(p)
    active=len(set(eps0)|set(eps1))
    return {'idx':int(v['idx']),'basis':basis,'dim':int(v['dim']),'lb':int(v['lb']),'cap':int(v['cap']),'rhs':rhs,'eps0':eps0,'eps1':eps1,'active':active,'contains_pivot':in_span(pivot,pairs)}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--pivot-name', choices=['rank2','rank3'], required=True)
    ap.add_argument('--n', type=int, default=20)
    ap.add_argument('--initial-dim', type=int, default=3)
    ap.add_argument('--initial-cap', type=int, default=5)
    ap.add_argument('--rounds', type=int, default=8)
    ap.add_argument('--time-per-round', type=float, default=120.0)
    ap.add_argument('--total-time', type=float, default=900.0)
    ap.add_argument('--seed', type=int, default=24020)
    ap.add_argument('--force-quotient', default='', help='comma list p:eps; forces a specific lift assignment')
    ap.add_argument('--force-support', default='', help='comma list quotient points; forces support but leaves lift bit free')
    ap.add_argument('--forbid-quotient', default='', help='comma list quotient points to forbid')
    ap.add_argument('--qmm-control', type=Path, default=None, help='If given, derive force assignment from all A terms except pivot; mainly n=23 positive control')
    ap.add_argument('--label', default='')
    args=ap.parse_args(); t0=time.time(); pivot=PIVOTS[args.pivot_name]
    print(f'Loading LUT {LUT_PATH}', flush=True); lut,meta=load_lut(LUT_PATH); print(f'LUT rows={len(lut)} coverage={meta.get("coverage_ok")}', flush=True)
    force=[]
    force_support={int(x) for x in args.force_support.split(',') if x.strip()}
    if args.force_quotient:
        for tok in args.force_quotient.split(','):
            if not tok.strip(): continue
            if ':' in tok:
                p,e=tok.split(':'); force.append((int(p),int(e)))
            else:
                force.append((int(tok),0))
    if args.qmm_control:
        masks0=load_qmm_a_masks(args.qmm_control)
        if pivot in masks0:
            masks=masks0; norm_info={'chosen_term':masks.index(pivot),'source_mask':pivot,'already_pivot':True}
        else:
            masks,norm_info=normalize_masks_to_pivot(masks0,pivot)
        print(f'qmm normalization: {norm_info}', flush=True)
        # Use every non-pivot full A factor in the transformed verified scheme as a forced lift.
        force=[]; zeros=0; bad=[]
        for a in masks:
            if a==pivot: continue
            qp=quotient_point_from_full(a,pivot)
            if qp is None:
                zeros += 1
            else:
                force.append(qp)
        force_support=set()
        if len(force) != args.n-1:
            print(f'warning: qmm produced {len(force)} quotient assignments for n-1={args.n-1}; zeros={zeros}; bad={bad}', flush=True)
    forbid={int(x) for x in args.forbid_quotient.split(',') if x.strip()}
    rows, init_stats=init_rows(lut,pivot,args.n,args.initial_dim,args.initial_cap)
    row_keys={(tuple(r['eps0']),tuple(r['eps1']),r['rhs']) for r in rows}
    rounds=[]
    print(f'initial rows={len(rows)} force_assign={len(force)} force_support={len(force_support)} forbid={len(forbid)} n={args.n}', flush=True)
    for rnd in range(args.rounds):
        if time.time()-t0 >= args.total_time: break
        tl=min(args.time_per_round, args.total_time-(time.time()-t0))
        print(f'round {rnd}: rows={len(rows)} tl={tl:.1f}', flush=True)
        rec=solve(rows,args.n,force,force_support,forbid,tl,args.seed+rnd)
        if 'quotient_support' not in rec:
            rounds.append(rec); print(f"  {rec['status']} no assignment", flush=True); break
        viol,stats,fullA=check_candidate(lut,pivot,args.n,rec['quotient_support'],rec['lift_bits_in_support_order'],max_report=5000)
        rec['full_A_support']=fullA
        rec['full_check_stats']=stats
        rec['violation_head']=viol[:50]
        print(f"  {rec['status']} violations={stats['violation_count']} cap_hist={stats['violation_cap_hist']}", flush=True)
        if not viol:
            rec['fully_full_wang_admissible']=True; rounds.append(rec); break
        new=0
        for v in viol:
            rr=row_from_violation(pivot,args.n,v)
            key=(tuple(rr['eps0']),tuple(rr['eps1']),rr['rhs'])
            if key not in row_keys:
                row_keys.add(key); rows.append(rr); new+=1
        rec['new_rows_added']=new
        rounds.append(rec)
        if new==0: break
    out={'schema':'s0908_pivot_fixed_lift_occupation_cegar_v1','pivot_name':args.pivot_name,'pivot':pivot,'n':args.n,'meaning':'full A-side Wang occupation only for fixed pivot; infeasible is necessary-condition exclusion, feasible is not B/C decomposition','source_lut':str(LUT_PATH),'source_lut_sha256':sha_file(LUT_PATH),'lut_coverage_ok':meta.get('coverage_ok'),'initial_dim':args.initial_dim,'initial_cap':args.initial_cap,'initial_stats':init_stats,'force_assignment_count':len(force),'force_assignment':force,'force_support':sorted(force_support),'forbid_quotient':sorted(forbid),'qmm_control':str(args.qmm_control) if args.qmm_control else None,'rounds':rounds,'final_row_count':len(rows),'final_status':rounds[-1]['status'] if rounds else 'no_rounds','found_full_wang_admissible':any(r.get('fully_full_wang_admissible') for r in rounds),'elapsed_sec':time.time()-t0}
    lab=args.label or f'{args.pivot_name}_n{args.n}_d{args.initial_dim}_cap{args.initial_cap}'
    path=OUTDIR/f'{lab}.json'
    path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('saved',path,flush=True)
    print(json.dumps({'final_status':out['final_status'],'rounds':len(rounds),'found_full_wang_admissible':out['found_full_wang_admissible'],'final_row_count':out['final_row_count'],'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True), flush=True)

if __name__=='__main__': main()
