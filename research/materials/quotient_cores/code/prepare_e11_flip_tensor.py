#!/usr/bin/env python3
"""Prepare research_record Wang E11 restricted core for flip-cpd local search.

Input convention from related analysis:
  core tensor shape is (8,9,9) over F2, C-index row-major 3*i+k, A coordinates
  related analysis,related analysis,a10,a11,a12,a20,a21,a22.
flip-cpd expects data/tensors/<name>.npy as int8 COO rows [i,j,k,value] and a
metadata JSON with name,nU,nV,nW.
"""
from pathlib import Path
import argparse, json
import numpy as np


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--input',default='data/restricted_cores/mask_001_E11_core.npy')
    ap.add_argument('--workspace',default='data/e11_flip_workspace')
    ap.add_argument('--name',default='e11core')
    args=ap.parse_args()
    T=np.load(args.input)
    if T.shape!=(8,9,9):
        raise ValueError(f'unexpected shape {T.shape}')
    T=(T.astype(np.int64)%2).astype(np.int8)
    rows=[]
    for i,j,k in zip(*np.nonzero(T)):
        rows.append([int(i),int(j),int(k),int(T[i,j,k])])
    rows=np.array(rows,dtype=np.int8)
    outdir=Path(args.workspace)/'data'/'tensors'
    outdir.mkdir(parents=True,exist_ok=True)
    np.save(outdir/(args.name+'.npy'),rows)
    meta={'name':args.name,'nU':8,'nV':9,'nW':9,
          'op':'restricted_core_E11_from_T333_A_axis_delete_a00','n1':8,'n2':9,'n3':9,
          'source':args.input,
          'convention':'indices [Acoord,Browmajor,Crowmajor], F2 values; A coords related analysis,related analysis,a10,a11,a12,a20,a21,a22; C row-major'}
    (outdir/(args.name+'.meta.json')).write_text(json.dumps(meta,indent=2)+'\n')
    summary={'input':args.input,'workspace':args.workspace,'name':args.name,
             'shape':list(T.shape),'nnz':int(T.sum()),'coo_path':str(outdir/(args.name+'.npy')),
             'meta_path':str(outdir/(args.name+'.meta.json')),
             'coo_rows':rows.tolist()}
    Path(args.workspace).mkdir(parents=True,exist_ok=True)
    (Path(args.workspace)/'prepare_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    main()
