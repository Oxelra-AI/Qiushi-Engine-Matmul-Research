#!/usr/bin/env python3
"""Random S tight-space scan for E11 quotient-lift obstruction."""
from __future__ import annotations
import argparse, json, random, sys, time
from collections import Counter
from pathlib import Path
import numpy as np

SCRIPTS=Path('scripts')
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0,str(SCRIPTS))
import e11_s_coset_rank_sat as sc  # noqa: E402
import e11_s_tight_space_scan as tscan  # noqa: E402


def matrix_mask_from_np(M):
    out=0
    for b in range(9):
        row=0
        for c in range(9):
            if int(M[b,c])&1: row |= 1<<c
        out |= row << (9*b)
    return out


def rand81(rng): return rng.getrandbits(81)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--prefix', required=True)
    ap.add_argument('--dim-S', type=int, default=11)
    ap.add_argument('--rank-res', type=int, default=8)
    ap.add_argument('--samples', type=int, default=100)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--out', type=Path, required=True)
    args=ap.parse_args(); t0=time.time(); rng=random.Random(args.seed)
    prefix=[int(x) for x in args.prefix.split(',') if x.strip()]
    Q,ann,phis,Rcoords=sc.quotient_base_residual(prefix)
    Smin=sc.rref_basis([matrix_mask_from_np(Q[i]) for i in range(Q.shape[0])])
    Rphi=tscan.build_Rphi_masks(Rcoords)
    seen=set(); records=[]; attempts=0
    status_counts=Counter(); cover_dist=Counter(); mprof=Counter(); survivor_examples=[]
    while len(records)<args.samples and attempts<args.samples*500:
        attempts+=1
        vecs=list(Smin)
        while len(sc.rref_basis(vecs))<args.dim_S:
            vecs.append(rand81(rng))
        S=sc.rref_basis(vecs)
        if S in seen: continue
        seen.add(S)
        m,mininfo=tscan.mininfo_for_S(S,Rphi)
        mt=tuple(m[p] for p in range(1,16)); mprof[mt]+=1
        covers=sc.enumerate_covers(mt,args.rank_res); cover_dist[len(covers)]+=1
        blocked=0; first_surv=[]
        for ci,cov in enumerate(covers):
            br=tscan.cover_block_record(cov,m,mininfo)
            if br['blocked']:
                blocked+=1
            else:
                if len(first_surv)<3:
                    first_surv.append({'cover_index':ci,'cover':cov,'tight_phis':br['tight_phis'],'tight_count_by_a':br['tight_count_by_a']})
                if len(survivor_examples)<10:
                    survivor_examples.append({'sample_index':len(records),'S_hash':sc.basis_hash(S),'cover_index':ci,'cover':cov,'m_tuple':list(mt),'tight_phis':br['tight_phis'],'tight_count_by_a':br['tight_count_by_a'],'S_basis_hex':[hex(x) for x in S]})
        if not covers: status='NO_VALID_COVER'
        elif blocked==len(covers): status='ALL_COVERS_SPACE_BLOCKED'
        elif blocked==0: status='NO_COVER_SPACE_BLOCKED'
        else: status='SOME_COVERS_SURVIVE_SPACE'
        status_counts[status]+=1
        rec={'sample_index':len(records),'attempt_index':attempts,'S_hash':sc.basis_hash(S),'S_dim':len(S),'m_by_phi':{str(k):int(v) for k,v in m.items()},'sum_m_phi':int(sum(m.values())),'valid_cover_count':len(covers),'space_blocked_cover_count':blocked,'status':status,'first_surviving_covers':first_surv}
        if len(records)<50 or status!='ALL_COVERS_SPACE_BLOCKED': records.append(rec)
        else: records.append({'sample_index':len(records),'S_hash':sc.basis_hash(S),'sum_m_phi':int(sum(m.values())),'valid_cover_count':len(covers),'space_blocked_cover_count':blocked,'status':status})
        if len(records)<=5 or status!='ALL_COVERS_SPACE_BLOCKED' or len(records)%50==0:
            print(f"sample {len(records)-1} sum_m={sum(m.values())} covers={len(covers)} blocked={blocked} status={status}", flush=True)
    result={'purpose':'random S tight row/column-space obstruction controls','field':'F2','prefix':prefix,'annihilator_basis':ann,'phi_vectors':phis,'Smin_dim':len(Smin),'Smin_hash':sc.basis_hash(Smin),'dim_S':args.dim_S,'rank_res':args.rank_res,'samples_requested':args.samples,'samples_recorded':len(records),'attempts':attempts,'seed':args.seed,'status_counts':dict(status_counts),'valid_cover_count_distribution':{str(k):int(v) for k,v in sorted(cover_dist.items())},'m_profile_type_count':len(mprof),'m_profile_counts_head':[{'m_tuple':list(k),'count':int(v)} for k,v in mprof.most_common(20)],'surviving_space_examples':survivor_examples,'records':records,'elapsed_sec':time.time()-t0}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2,sort_keys=True,default=int)+'\n')
    print(json.dumps({k:result[k] for k in ['samples_recorded','status_counts','valid_cover_count_distribution','m_profile_type_count','elapsed_sec']},indent=2,sort_keys=True))
    print('wrote',args.out)

if __name__=='__main__': main()
