#!/usr/bin/env python3
"""analysis: build the inductively reduced E11-core Wang row set.

analysis showed that many dim-5/6 Wang rows are local consequences of their
proper dual subflag rows. This script recomputes that implication row-by-row and
writes a reusable reduced row set:
  keep all dimensions except 5/6 unchanged;
  for dim6 (dual dimension 2), keep only rows whose zero-color bound is not
      implied by the three dual-point rows;
  for dim5 (dual dimension 3), keep only rows whose zero-color bound is not
      implied by all dual-point and dual-line subrows.
Because the dim5 implication can use dim6 subrows, and dim6 dropped rows are
already implied by dim7 rows, the reduction is inductive. It is an equivalent
integer formulation of the Wang occupation system, not a stronger theorem.
"""
from __future__ import annotations
import hashlib, json, pickle, sys, time
from collections import Counter
from pathlib import Path
from typing import Sequence, List

SCRIPTS=Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path: sys.path.insert(0,str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import build_core_constraints
from wang_capacity_lazy import pack_basis, rref_basis, unpack_basis
from flag_local_polytope import local_profile_for_dual_key, max_n0_for_profile

ROOT=Path('research/research_record')
OUTDIR=ROOT/'workspace/data/reduced_wang'
LUT_PATH=ROOT/'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl'


def dot2(a:int,b:int)->int: return (a&b).bit_count()&1

def annihilator_basis(primal_basis:Sequence[int], n:int=8)->List[int]:
    vecs=[q for q in range(1,1<<n) if all(dot2(q,b)==0 for b in primal_basis)]
    return list(rref_basis(vecs,n=n))

def classify_record(rec, L_by_primal_key):
    key8=int(rec['key8']); dim=int(rec['dim8']); L=int(rec['L']); cap=19-L
    if dim not in (5,6):
        return {'status':'kept_other_dimension','keep':True,'reason':'dimension_not_reduced'}
    dual_basis=annihilator_basis(list(unpack_basis(key8)))
    d=len(dual_basis)
    if d != 8-dim:
        raise RuntimeError(f'dual dimension mismatch key={key8} dim={dim} dual_basis={dual_basis}')
    dual_key=pack_basis(rref_basis(dual_basis,n=8))
    prof=local_profile_for_dual_key(int(dual_key), L_by_primal_key)
    if int(prof['primal_key']) != key8:
        raise RuntimeError(f'primal key mismatch key8={key8} profile_primal={prof["primal_key"]}')
    max_n0,witness=max_n0_for_profile(d, tuple(prof['point_L']), tuple(prof['line_L_by_annihilator_color']))
    keep=bool(max_n0>cap)
    status='row_adds_integer_information' if keep else 'proper_flag_implies_row'
    return {
        'status':status,
        'keep':keep,
        'dual_key':int(dual_key),
        'dual_basis':list(dual_basis),
        'point_L':list(prof['point_L']),
        'line_L_by_annihilator_color':list(prof['line_L_by_annihilator_color']),
        'L_Dperp':L,
        'cap':cap,
        'max_n0_from_proper_subflags':int(max_n0),
        'witness_counts_n0_then_nonzero_colors':None if witness is None else list(witness),
    }

def sha_int_list(vals):
    h=hashlib.sha256()
    for v in vals:
        h.update(str(int(v)).encode()); h.update(b'\n')
    return h.hexdigest()

def main():
    t0=time.time(); OUTDIR.mkdir(parents=True,exist_ok=True)
    lut,lut_meta=load_lut(LUT_PATH); core=CoreQuotient(1); records,meta=build_core_constraints(core,lut)
    L_by={int(r['key8']):int(r['L']) for r in records}
    keep_keys=[]; drop_keys=[]; status_by_dim=Counter(); by_dim=Counter(); by_dim_L_status=Counter(); profile_status=Counter(); examples=[]
    for i,rec in enumerate(records):
        cls=classify_record(rec,L_by)
        dim=int(rec['dim8']); L=int(rec['L']); st=cls['status']
        by_dim[dim]+=1; status_by_dim[(dim,st)]+=1; by_dim_L_status((dim,L,st)) if False else None
        by_dim_L_status[(dim,L,st)] += 1
        if cls['keep']:
            keep_keys.append(int(rec['key8']))
        else:
            drop_keys.append(int(rec['key8']))
        if dim in (5,6):
            # profile-level counts independent of number of labelled rows
            profile_key=(dim, tuple(cls['point_L']), tuple(cls['line_L_by_annihilator_color']), int(cls['L_Dperp']), st)
            profile_status[profile_key]+=1
            if len(examples)<30 and (st=='row_adds_integer_information' or len(examples)<10):
                ex={k:cls[k] for k in cls if k not in ('keep',)}
                ex.update({'key8':int(rec['key8']),'dim8':dim,'L':L})
                examples.append(ex)
        if (i+1)%100000==0:
            print(f'processed {i+1:,}/{len(records):,}')
    keep_keys_sorted=sorted(keep_keys); drop_keys_sorted=sorted(drop_keys)
    pkl=OUTDIR/'primitive_reduced_rows.pkl'
    with pkl.open('wb') as f:
        pickle.dump({'kept_key8':keep_keys_sorted,'dropped_key8':drop_keys_sorted,'rank_s':19,'description':'analysis primitive reduced E11-core Wang rows'},f,protocol=pickle.HIGHEST_PROTOCOL)
    manifest={
        'schema':'primitive_reduced_wang_v1',
        'meaning':'Equivalent inductive reduction of E11-core Wang occupation rows using analysis local flag implications. It keeps all non-dim5/6 rows and only primitive dim5/6 rows; dropped rows are local integer consequences of retained lower-dimensional subflag rows.',
        'field':'F2','core':'E11 quotient core','rank_s':19,
        'complete_row_count':len(records),
        'kept_row_count':len(keep_keys_sorted),
        'dropped_row_count':len(drop_keys_sorted),
        'kept_key8_sha256':sha_int_list(keep_keys_sorted),
        'dropped_key8_sha256':sha_int_list(drop_keys_sorted),
        'pickle_path':str(pkl),
        'complete_meta':meta,
        'lut_coverage_ok':lut_meta.get('coverage_ok'),
        'rows_by_dim':{str(k):int(v) for k,v in sorted(by_dim.items())},
        'rows_by_dim_and_status':[
            {'dim8':int(dim),'status':st,'count':int(cnt)} for (dim,st),cnt in sorted(status_by_dim.items())
        ],
        'rows_by_dim_L_status':[
            {'dim8':int(dim),'L':int(L),'status':st,'count':int(cnt)} for (dim,L,st),cnt in sorted(by_dim_L_status.items())
        ],
        'reduced_dim5_dim6_profile_count':len(profile_status),
        'examples_head':examples,
        'elapsed_sec':time.time()-t0,
    }
    out=OUTDIR/'primitive_reduced_wang_manifest.json'
    out.write_text(json.dumps(manifest,indent=2,sort_keys=True)+"\n")
    print(json.dumps({'out':str(out),'pkl':str(pkl),'complete':len(records),'kept':len(keep_keys_sorted),'dropped':len(drop_keys_sorted),'sha':manifest['kept_key8_sha256'],'elapsed_sec':round(time.time()-t0,3)},indent=2))
if __name__=='__main__': main()
