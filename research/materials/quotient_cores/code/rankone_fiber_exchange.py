#!/usr/bin/env python3
"""analysis exact one-extension search in the rank-one span representation.

For a retained space V containing W=col(D), enumerate all nonzero rank-one
9x9 matrices s=a⊗b and group them by their reduction remainder modulo V.  If
rem(s)=0, s is in F0.  For a nonzero fiber F_z choose s0 in F_z.  Then all
rank-one matrices in U=V+<s0> are exactly F0 union F_z, and their span has
rank

    1 + dim span( F0_tags union {tag(s)+tag(s0) : s in F_z} )

in coordinates of V plus the new outside coordinate.  Thus the extension is
rank-one generated exactly when the inner dimension equals dim(V).  When
V has dimension 21 this gives a direct rank-22 construction test; when V has
constant dimension 22 it gives a rank-23 positive control.

The search is exhaustive for each chosen retained V over all 511^2 nonzero
rank-one columns.  It is local to the chosen V's; absence of a hit is not a
global nonexistence result.
"""
from __future__ import annotations

import argparse
import json
import random
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import residual_repair_geometry as rg  # type: ignore
from rankone_lattice import (  # type: ignore
    echelon_add,
    echelon_reduce,
    independent_subset,
    rank_of_int_list,
    rank_ones_in_span,
    solve_and_verify,
)
from dependency_modW import (  # type: ignore
    bitparity,
    functional_space,
    make_Wcoord_basis,
    quotient_decomposition,
)

OUTDIR = Path('data/rankone_fiber_exchange')


def build_rank23_basis(terms: Sequence[Tuple[int,int,int]]) -> Dict[int,Tuple[int,int]]:
    basis: Dict[int,Tuple[int,int]] = {}
    for i,(a,b,_c) in enumerate(terms):
        if not echelon_add(basis, rg.vec_mask9_to_outer81(a,b), 1<<i):
            raise RuntimeError(f'rank23 source columns dependent at {i}')
    return basis


def W_coords_in_basis(basis: Dict[int,Tuple[int,int]], W_cols: Sequence[int]) -> List[int]:
    out=[]
    for w in W_cols:
        rem,tag=echelon_reduce(basis,int(w))
        if rem:
            raise RuntimeError('W column not in source span')
        out.append(int(tag))
    if rank_of_int_list(out)!=9:
        raise RuntimeError('W coordinate rank != 9')
    return out


def q_independent_items(rankones: Sequence[Tuple[int,int,int]], Wcoords: Sequence[int], dim:int, prefer_original:bool=True):
    Wb=make_Wcoord_basis(Wcoords)
    qtags,_=quotient_decomposition([int(t) for _a,_b,t in rankones], Wb)
    items=[]
    for (a,b,t),q in zip(rankones,qtags):
        # stable order: originals first when requested, then small tags
        is_extra = (int(t) & (int(t)-1)) != 0
        key=(is_extra if prefer_original else False, int(t), int(a), int(b))
        items.append((key,int(q),(int(a),int(b),int(t))))
    items.sort(key=lambda x:x[0])
    picked=[]; piv={}
    for _key,q,payload in items:
        x=q
        while x:
            p=x.bit_length()-1
            if p in piv:
                x ^= piv[p]
            else:
                piv[p]=x; picked.append(payload); break
        if len(picked)==dim:
            return picked
    raise RuntimeError(f'could not choose {dim} quotient-independent rank-one items')


def best_hyperplane_seed_records(name:str, terms:Sequence[Tuple[int,int,int]], W_cols:Sequence[int], max_hyperplanes:int=4):
    basis=build_rank23_basis(terms)
    Wcoords=W_coords_in_basis(basis,W_cols)
    S=rank_ones_in_span(basis)
    phibasis=functional_space(Wcoords,len(terms))
    best_rank=-1; best=[]; hist=Counter()
    for phi_code in range(1,1<<len(phibasis)):
        phi=0
        for i,b in enumerate(phibasis):
            if (phi_code>>i)&1:
                phi ^= int(b)
        kept=[ro for ro in S if not bitparity(phi & int(ro[2]))]
        r=rank_of_int_list([int(t) for _a,_b,t in kept])
        hist[r]+=1
        if r>best_rank:
            best_rank=r; best=[(phi,kept)]
        elif r==best_rank and len(best)<max_hyperplanes:
            best.append((phi,kept))
    out=[]
    for idx,(phi,kept) in enumerate(best[:max_hyperplanes]):
        seed13=q_independent_items(kept,Wcoords,13)
        out.append({'kind':'best_hyperplane_seed13','source':name,'record_index':idx,'phi':int(phi),'best_hyperplane_rank':int(best_rank),'rank_one_count_in_hyperplane':len(kept),'seed13_ab':[(a,b) for a,b,_t in seed13],'seed13_tags':[int(t) for _a,_b,t in seed13],'hyperplane_rank_hist':{str(k):int(v) for k,v in sorted(hist.items())}})
    return out


def rank23_positive_records(name:str, terms:Sequence[Tuple[int,int,int]], W_cols:Sequence[int], max_records:int=3):
    basis=build_rank23_basis(terms)
    Wcoords=W_coords_in_basis(basis,W_cols)
    orig=[(int(a),int(b),1<<i) for i,(a,b,_c) in enumerate(terms)]
    q14=q_independent_items(orig,Wcoords,14)
    out=[]
    # Omit a few different q-basis positions, leaving V=W+13 columns, and the
    # omitted one should be in an accepting nonzero fiber for the full rank-23 span.
    for omit in range(min(max_records,len(q14))):
        retained=[(a,b) for j,(a,b,_t) in enumerate(q14) if j!=omit]
        omitted=q14[omit]
        out.append({'kind':'rank23_positive_qbasis14_omit1','source':name,'record_index':omit,'retained13_ab':retained,'omitted_ab':(omitted[0],omitted[1]),'omitted_tag':int(omitted[2]),'qbasis14_tags':[int(t) for _a,_b,t in q14]})
    return out


def build_V_basis(W_cols: Sequence[int], seeds: Sequence[Tuple[int,int]]):
    basis: Dict[int,Tuple[int,int]] = {}
    for j,w in enumerate(W_cols):
        if not echelon_add(basis,int(w),1<<j):
            raise RuntimeError('dependent W')
    for i,(a,b) in enumerate(seeds):
        if not echelon_add(basis, rg.vec_mask9_to_outer81(int(a),int(b)), 1<<(9+i)):
            return None
    return basis


def all_rankone_pairs():
    for a in range(1,512):
        for b in range(1,512):
            yield a,b,rg.vec_mask9_to_outer81(a,b)


def select_independent_columns(items: Sequence[Tuple[int,int,int]], target:int):
    # items are (a,b,ambient81).  Choose independent ambient columns.
    return independent_subset([(int(v),(int(a),int(b))) for a,b,v in items], target)


def fiber_scan(W_cols:Sequence[int], seeds:Sequence[Tuple[int,int]], target_dim:int, label:str, expected_ab:Tuple[int,int]|None=None, stop_on_witness:bool=True):
    t0=time.time()
    basis=build_V_basis(W_cols,seeds)
    if basis is None:
        return {'label':label,'status':'INVALID_V_DIM','seed_count':len(seeds),'target_dim':target_dim}
    dimV=len(basis)
    if target_dim!=dimV+1:
        raise ValueError(f'target_dim {target_dim} must equal dim(V)+1={dimV+1}')
    fibers: Dict[int,List[Tuple[int,int,int]]] = defaultdict(list)  # rem -> [(tag,a,b)]
    F0: List[Tuple[int,int,int]] = []
    expected_rem=None; expected_tag=None
    for a,b,v in all_rankone_pairs():
        rem,tag=echelon_reduce(basis,v)
        if rem==0:
            F0.append((int(tag),a,b))
        else:
            fibers[int(rem)].append((int(tag),a,b))
        if expected_ab is not None and (a,b)==tuple(expected_ab):
            expected_rem=int(rem); expected_tag=int(tag)
    F0_tags=[t for t,_a,_b in F0]
    R0_rank=rank_of_int_list(F0_tags)
    status_hist=Counter(); fiber_size_hist=Counter(); combined_rank_hist=Counter(); accepting=[]
    best={'combined_rank':-1,'fiber_size':0,'rem':None,'example_ab':None,'contains_expected':False}
    expected_record=None
    for rem,lst in fibers.items():
        fiber_size_hist[len(lst)]+=1
        ref_tag,ref_a,ref_b=lst[0]
        diffs=[int(t)^int(ref_tag) for t,_a,_b in lst]
        combined_rank=rank_of_int_list(F0_tags + diffs)
        combined_rank_hist[combined_rank]+=1
        ok=(combined_rank==dimV)
        status_hist['ACCEPT'] += int(ok)
        status_hist['REJECT'] += int(not ok)
        contains_expected = expected_rem==rem if expected_rem is not None else False
        if (combined_rank, len(lst))>(best['combined_rank'],best['fiber_size']):
            best={'combined_rank':int(combined_rank),'fiber_size':len(lst),'rem':int(rem),'example_ab':(int(ref_a),int(ref_b)),'contains_expected':bool(contains_expected)}
        if contains_expected:
            expected_record={'expected_ab':tuple(expected_ab) if expected_ab is not None else None,'expected_rem':int(expected_rem),'expected_tag':int(expected_tag),'fiber_size':len(lst),'combined_rank':int(combined_rank),'accepts':bool(ok),'ref_ab':(int(ref_a),int(ref_b))}
        if ok:
            # The actual rank-one content of U is F0 plus this fiber.  Select a
            # spanning set of target_dim rank-one ambient columns and verify.
            actual=[(a,b,rg.vec_mask9_to_outer81(a,b)) for _t,a,b in F0]
            actual += [(a,b,rg.vec_mask9_to_outer81(a,b)) for _t,a,b in lst]
            picks=select_independent_columns(actual,target_dim)
            A=[a for a,_b in picks]; B=[b for _a,b in picks]
            verify=solve_and_verify(A,B)
            rec={'rem':int(rem),'fiber_size':len(lst),'combined_rank':int(combined_rank),'ref_ab':(int(ref_a),int(ref_b)),'selected_A':A,'selected_B':B,'verify':verify}
            accepting.append(rec)
            if stop_on_witness and verify.get('status')=='VERIFIED' and target_dim<=22:
                break
    out={'schema':'s0908_rankone_fiber_scan_v1','label':label,'seed_count':len(seeds),'dimV':dimV,'target_dim':target_dim,'F0_size':len(F0),'F0_rank':int(R0_rank),'nonzero_fiber_count':len(fibers),'status_hist':{str(k):int(v) for k,v in sorted(status_hist.items())},'fiber_size_hist':{str(k):int(v) for k,v in sorted(fiber_size_hist.items())},'combined_rank_hist':{str(k):int(v) for k,v in sorted(combined_rank_hist.items())},'best':best,'expected_record':expected_record,'accepting_count':len(accepting),'accepting_head':accepting[:5],'elapsed_sec':time.time()-t0}
    return out


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--sources', default='cn122_qmm,flip_rank23_text,pivot17_transformed_rank23')
    ap.add_argument('--max-hyperplanes', type=int, default=2)
    ap.add_argument('--rank22-source-limit', type=int, default=3)
    ap.add_argument('--rank22-scan-positions', default='all', help='all or comma positions among 0..12')
    ap.add_argument('--positive-controls', action='store_true')
    ap.add_argument('--no-rank22', action='store_true')
    ap.add_argument('--outdir', type=Path, default=OUTDIR)
    args=ap.parse_args()
    args.outdir.mkdir(parents=True,exist_ok=True)
    sources=rg.load_sources(); W_cols=rg.D_columns_as_ints()
    t0=time.time(); records=[]; seed_records=[]; pos_records=[]; witnesses=[]
    for name in [x.strip() for x in args.sources.split(',') if x.strip()]:
        if args.positive_controls:
            pos_records.extend(rank23_positive_records(name,sources[name],W_cols,max_records=2))
        if not args.no_rank22:
            seed_records.extend(best_hyperplane_seed_records(name,sources[name],W_cols,args.max_hyperplanes))
    # Positive controls first, exercising nonzero-fiber acceptance to dim 23.
    for rec in pos_records:
        label=f"positive_{rec['source']}_{rec['record_index']}"
        out=fiber_scan(W_cols, rec['retained13_ab'], 23, label, expected_ab=tuple(rec['omitted_ab']), stop_on_witness=False)
        out['source_record']=rec
        records.append(out)
        print('positive',label,'dimV',out.get('dimV'),'F0_rank',out.get('F0_rank'),'fibers',out.get('nonzero_fiber_count'),'accepting',out.get('accepting_count'),'expected',out.get('expected_record'),flush=True)
    # Exact rank-22 one-seed extension scans.  For a best hyperplane seed13,
    # remove each selected position to make V dimension 21 and test all fibers.
    if args.rank22_scan_positions.strip().lower()=='all':
        positions=list(range(13))
    else:
        positions=[int(x) for x in args.rank22_scan_positions.split(',') if x.strip()]
    scan_count=0
    for si,rec in enumerate(seed_records):
        if scan_count>=args.rank22_source_limit:
            break
        seed13=[tuple(x) for x in rec['seed13_ab']]
        for pos in positions:
            if pos<0 or pos>=len(seed13):
                continue
            retained=[ab for j,ab in enumerate(seed13) if j!=pos]
            label=f"rank22_{rec['source']}_seed{rec['record_index']}_omit{pos}"
            out=fiber_scan(W_cols, retained, 22, label, expected_ab=seed13[pos], stop_on_witness=True)
            out['source_record']={k:v for k,v in rec.items() if k not in ('hyperplane_rank_hist',)}
            out['omitted_seed_ab']=seed13[pos]
            records.append(out); scan_count+=1
            if out.get('accepting_count'):
                for a in out.get('accepting_head',[]):
                    if a.get('verify',{}).get('status')=='VERIFIED':
                        witnesses.append(a['verify'])
            print('rank22',label,'F0_rank',out.get('F0_rank'),'fibers',out.get('nonzero_fiber_count'),'best',out.get('best'),'accepting',out.get('accepting_count'),'witnesses',len(witnesses),flush=True)
            if witnesses or scan_count>=args.rank22_source_limit:
                break
        if witnesses or scan_count>=args.rank22_source_limit:
            break
    params={'sources':args.sources,'max_hyperplanes':args.max_hyperplanes,'rank22_source_limit':args.rank22_source_limit,'rank22_scan_positions':args.rank22_scan_positions,'positive_controls':args.positive_controls,'no_rank22':args.no_rank22}
    out={'schema':'s0908_rankone_fiber_exchange_v1','meaning':'Exact one-extension fiber scans from retained W-containing spaces. VERIFIED entries are checked Brent decompositions; absent witnesses are local search evidence only.','parameters':params,'positive_record_count':len(pos_records),'seed_record_count':len(seed_records),'scan_record_count':len(records),'records':records,'witness_count':len(witnesses),'witnesses':witnesses,'elapsed_sec':time.time()-t0}
    op=args.outdir/'rankone_fiber_exchange.json'
    op.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    if witnesses:
        wp=args.outdir/'rank22_witness_from_fiber_exchange.json'; wp.write_text(json.dumps(witnesses[0],indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(op),'positive_records':len(pos_records),'seed_records':len(seed_records),'scans':len(records),'witness_count':len(witnesses),'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True))


if __name__=='__main__':
    main()
