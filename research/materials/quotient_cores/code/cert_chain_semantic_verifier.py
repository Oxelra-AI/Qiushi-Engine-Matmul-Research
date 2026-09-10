#!/usr/bin/env python3
"""Semantic verifier for the analysis shortened dim-2 proof assets.

This script independently reconstructs the induced quotient occupation rows for
orbits 484--491 from the verified Wang LUT/cache, checks that every cap-limited
core row used in the unary CNF proofs is a true reconstructed row, checks row
hashes and CNF/DRAT file hashes, and parses CNF headers/line counts.  It does
not by itself verify the third-party cardinality encoding proof theory; it
establishes the file/provenance chain from Wang rows to the generated CNFs that
were replayed by drat-trim.
"""
from __future__ import annotations

import hashlib
import json
import pickle
import sys
from pathlib import Path
from typing import Sequence, Tuple

SCRIPT=Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path: sys.path.insert(0,str(SCRIPT))
import dim2_replay_compat_graph as dg  # type: ignore

CORE_ROOT=Path('data/dim2_caplimited_cores_484_491')
UNARY_MANIFEST=Path('data/dim2_unary_certs_484_491/batch_unary_dim2_certs_manifest.json')
OUT=Path('data/structural/cert_chain_semantic_verifier.json')


def sha256(path: Path) -> str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for ch in iter(lambda:f.read(1<<20),b''):
            h.update(ch)
    return h.hexdigest()


def row_hash(rows: Sequence[Tuple[int,int]]) -> str:
    return hashlib.sha256(';'.join(f'{int(m)}:{int(c)}' for m,c in rows).encode()).hexdigest()


def parse_cnf_header_and_count(path: Path):
    header=None; clauses=0; comments=0; empty=0
    with path.open('rt') as f:
        for line in f:
            if not line.strip():
                empty += 1; continue
            if line.startswith('c'):
                comments += 1; continue
            if line.startswith('p'):
                parts=line.split(); header={'vars':int(parts[2]),'clauses':int(parts[3]),'raw':line.strip()}; continue
            clauses += 1
    return {'header':header,'clause_line_count':clauses,'comment_count':comments,'empty_count':empty,'header_matches_line_count': header is not None and clauses==header['clauses']}


def main():
    lut,cache=dg.load_lut_cache(); raw=dg.orbit_lbs_from_cache(cache,{})
    prof=json.loads(dg.PROFILE.read_text()); byidx={int(r['index']):r for r in prof['dimension_2_orbits']}
    unary=json.loads(UNARY_MANIFEST.read_text()); unary_byidx={int(r['index']):r for r in unary['records']}
    records=[]; all_ok=True
    for idx in range(484,492):
        prec=byidx[idx]; W=[int(x) for x in prec['constraint_values']]; L=int(prec['rank_lower_bound']); k=9-len(dg.rref_basis(W,9))
        rows,meta=dg.node_rows(W,lut,cache,raw,L)
        row_set=set((int(m),int(c)) for m,c in rows)
        up=unary_byidx[idx]
        core_path=Path(up['core_json']); core=json.loads(core_path.read_text())
        core_rows=[(int(r['mask']),int(r['cap'])) for r in core['shrunk_rows']]
        missing=[{'mask':m,'cap':c} for m,c in core_rows if (m,c) not in row_set]
        caplim=int(core['cap_limit'])
        wrong_cap=[{'mask':m,'cap':c} for m,c in core_rows if c>caplim]
        recomputed_core_hash=row_hash(core_rows)
        meta_path=Path(up['meta_path']); umeta=json.loads(meta_path.read_text())
        cnf_path=Path(umeta['cnf_path']); drat_path=Path(umeta['drat_path'])
        cnf_parse=parse_cnf_header_and_count(cnf_path)
        rec={'index':idx,'basis_profile':W,'quotient_dim':k,'old_lb':L,'reconstructed_row_count':len(rows),'reconstructed_row_sha256':row_hash(rows),'reconstructed_row_meta':meta,'cap_limit':caplim,'core_path':str(core_path),'core_file_sha256':sha256(core_path),'core_row_count':len(core_rows),'core_row_sha256_recorded':core.get('shrunk_row_sha256'),'core_row_sha256_recomputed':recomputed_core_hash,'core_rows_all_in_reconstructed_rows':len(missing)==0,'missing_core_rows_head':missing[:10],'core_rows_with_cap_above_limit_head':wrong_cap[:10],'unary_meta_path':str(meta_path),'unary_meta_file_sha256':sha256(meta_path),'unary_source_row_sha256':umeta.get('source',{}).get('source_row_sha256'),'unary_row_count':umeta.get('row_count'),'unary_k':umeta.get('k'),'unary_L':umeta.get('L'),'cnf_path':str(cnf_path),'cnf_sha256_manifest':up.get('cnf_sha256'),'cnf_sha256_meta':umeta.get('cnf_sha256'),'cnf_sha256_recomputed':sha256(cnf_path),'cnf_parse':cnf_parse,'cnf_meta_vars':umeta.get('cnf_meta',{}).get('vars'),'cnf_meta_clauses':umeta.get('cnf_meta',{}).get('clauses'),'drat_path':str(drat_path),'drat_sha256_manifest':up.get('drat_sha256'),'drat_sha256_meta':umeta.get('drat_sha256'),'drat_sha256_recomputed':sha256(drat_path),'cadical_returncode':umeta.get('cadical_returncode'),'drat_returncode':umeta.get('drat_returncode'),'drat_verified':umeta.get('drat_verified')}
        ok=(rec['core_rows_all_in_reconstructed_rows'] and not wrong_cap and rec['core_row_sha256_recorded']==recomputed_core_hash==rec['unary_source_row_sha256'] and rec['unary_row_count']==len(core_rows) and rec['unary_k']==k and rec['unary_L']==L and rec['cnf_sha256_manifest']==rec['cnf_sha256_meta']==rec['cnf_sha256_recomputed'] and rec['drat_sha256_manifest']==rec['drat_sha256_meta']==rec['drat_sha256_recomputed'] and cnf_parse['header_matches_line_count'] and cnf_parse['header']['vars']==rec['cnf_meta_vars'] and cnf_parse['header']['clauses']==rec['cnf_meta_clauses'] and rec['cadical_returncode']==20 and rec['drat_returncode']==0 and rec['drat_verified'] is True)
        rec['semantic_file_chain_ok']=bool(ok); all_ok=all_ok and ok; records.append(rec)
    out={'schema':'s0908_cert_chain_semantic_verifier_v1','meaning':'Reconstructs Wang quotient rows for 484--491 and checks the row-core/CNF/DRAT file chain. Does not replace the mathematical proof of cardinality encoding correctness, but records exact provenance consistency.','core_root':str(CORE_ROOT),'unary_manifest':str(UNARY_MANIFEST),'records':records,'summary':{'total':len(records),'ok':[r['index'] for r in records if r['semantic_file_chain_ok']],'failed':[r['index'] for r in records if not r['semantic_file_chain_ok']],'all_ok':all_ok}}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'ok','out':str(OUT),'summary':out['summary']},indent=2,sort_keys=True))

if __name__=='__main__': main()
