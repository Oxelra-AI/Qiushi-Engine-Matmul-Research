#!/usr/bin/env python3
"""Extract compact provenance assets for the shortened analysis proof chain."""
from __future__ import annotations
import json, pickle, hashlib, sys
from pathlib import Path
from collections import Counter, defaultdict
SCRIPT=Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path: sys.path.insert(0,str(SCRIPT))
import dim2_replay_compat_graph as dg  # type: ignore

CACHE=Path('data/wang_f2_lb20/wang_orbit_closed_cache.pkl')
LUTMETA=Path('data/wang_f2_lb20/wang_subspace_lut.meta.json')
RECEIPT=Path('data/wang_f2_lb20/verify_receipt.json')
COS=Path('data/coset/coset_plane_verify.json')
STRUCT=Path('data/structural/short_saturation_checks.json')
DIM2CORES=Path('data/dim2_caplimited_cores_484_491/dim2_caplimited_cert_manifest.json')
UNARY=Path('data/dim2_unary_certs_484_491/batch_unary_dim2_certs_manifest.json')
OUT=Path('data/structural/short_proof_asset_manifest.json')

def sha(path:Path):
    if not path.exists(): return None
    h=hashlib.sha256()
    with path.open('rb') as f:
        for ch in iter(lambda:f.read(1<<20),b''): h.update(ch)
    return h.hexdigest()

def main():
    cache=pickle.load(open(CACHE,'rb'))
    line=[o for o in cache['orbits'] if int(o['dim'])==1]
    line_summary={'orbit_count':len(line),'total_subspaces':sum(int(o['orbit_size']) for o in line),'lb_hist':dict(Counter(int(o['raw_lb']) for o in line)),'proof_type_hist':dict(Counter(str(o['proof_type']) for o in line)),'records':line}
    cos=json.loads(COS.read_text()) if COS.exists() else {}
    struct=json.loads(STRUCT.read_text()) if STRUCT.exists() else {}
    dim3_indices=Counter()
    for r in cos.get('dim3_records_head',[]):
        pass
    # Recompute all coset dim3 quad orbit positions compactly, because the analysis JSON stores only a head.
    import coset_plane_verify as cv  # type: ignore
    lut=pickle.load(open('data/wang_f2_lb20/wang_subspace_lut.pkl','rb'))
    if isinstance(lut,dict) and 'lut' in lut: lut={int(k):int(v) for k,v in lut['lut'].items()}
    dim3_orbits=Counter(); dim3_prooftypes=Counter(); dim3_lbs=Counter(); examples=[]
    for lower_block in range(1,64):
        p=lower_block<<3; coset=[p|r for r in range(8)]; high=[x for x in coset if dg.rank3(x)>=2]
        for quad in __import__('itertools').combinations(high,4):
            rb=dg.rref_basis(quad,9)
            if len(rb)!=3: continue
            key=dg.pack_basis(rb); pos=int(cache['key_to_orbit'][key]); lb=int(lut[key])
            dim3_orbits[pos]+=1; dim3_lbs[lb]+=1; dim3_prooftypes[str(cache['orbits'][pos]['proof_type'])]+=1
            if len(examples)<20: examples.append({'lower_block':lower_block,'quad':list(quad),'basis':list(rb),'orbit':pos,'lb':lb,'proof_type':cache['orbits'][pos]['proof_type']})
    dim2cores=json.loads(DIM2CORES.read_text()) if DIM2CORES.exists() else None
    unary=json.loads(UNARY.read_text()) if UNARY.exists() else None
    out={'schema':'s0908_short_proof_asset_manifest_v1','meaning':'Compact map of files and finite facts supporting the shortened saturated lower-bound route. The rank>=21 theorem is still pending until all listed finite premises are independently accepted/replayed.','source_files':{'wang_verify_receipt':str(RECEIPT),'wang_verify_receipt_sha256':sha(RECEIPT),'wang_lut_meta':str(LUTMETA),'wang_lut_meta_sha256':sha(LUTMETA),'wang_orbit_cache':str(CACHE),'wang_orbit_cache_sha256':sha(CACHE),'structural_checks':str(STRUCT),'structural_checks_sha256':sha(STRUCT),'coset_plane_verify':str(COS),'coset_plane_verify_sha256':sha(COS),'dim2_caplimited_core_manifest':str(DIM2CORES),'dim2_caplimited_core_manifest_sha256':sha(DIM2CORES),'dim2_unary_cert_manifest':str(UNARY),'dim2_unary_cert_manifest_sha256':sha(UNARY)},'line_lower_bound_19':line_summary,'dim3_affine_plane_lb17':{'quad_count':sum(dim3_orbits.values()),'orbit_hist':{str(k):int(v) for k,v in sorted(dim3_orbits.items())},'lb_hist':{str(k):int(v) for k,v in sorted(dim3_lbs.items())},'proof_type_hist':dict(dim3_prooftypes),'examples_head':examples},'weak_dim2_rankone_difference':struct.get('weak_dim2_premise'), 'rankone_shared_side':struct.get('rankone_shared_side_lemma_check'), 'product_formula_elementary_basis_check':struct.get('product_formula_elementary_basis_check'), 'invertible_A_facts':struct.get('invertible_A_facts'), 'dim2_core_summary':None if dim2cores is None else dim2cores.get('summary'), 'dim2_unary_summary':None if unary is None else unary.get('summary')}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(OUT),'line':line_summary['lb_hist'],'dim3_lb_hist':out['dim3_affine_plane_lb17']['lb_hist'],'dim2_unary_summary':out['dim2_unary_summary']},indent=2,sort_keys=True))
if __name__=='__main__': main()
