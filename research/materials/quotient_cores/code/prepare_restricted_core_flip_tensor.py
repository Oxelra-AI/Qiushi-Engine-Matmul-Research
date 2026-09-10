#!/usr/bin/env python3
"""Prepare an F2 restricted-core tensor for flip-cpd.

Input is a dense numpy array of shape (m,9,9).  Output is the flip-cpd COO
format data/tensors/<name>.npy with rows [i,j,k,value] and a metadata JSON
containing nU,nV,nW.
"""
from __future__ import annotations
import argparse, json
from pathlib import Path
import numpy as np


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--input',required=True)
    ap.add_argument('--workspace',required=True)
    ap.add_argument('--name',required=True)
    ap.add_argument('--label',default='restricted_core')
    ap.add_argument('--source-meta',default='')
    args=ap.parse_args()
    T=np.load(args.input)
    if T.ndim!=3 or T.shape[1:]!=(9,9):
        raise ValueError(f'expected shape (m,9,9), got {T.shape}')
    T=(T.astype(np.int64)&1).astype(np.int8)
    rows=[]
    for i,j,k in zip(*np.nonzero(T)):
        rows.append([int(i),int(j),int(k),int(T[i,j,k])])
    rows=np.array(rows,dtype=np.int8)
    outdir=Path(args.workspace)/'data'/'tensors'
    outdir.mkdir(parents=True,exist_ok=True)
    np.save(outdir/(args.name+'.npy'),rows)
    source_meta=None
    if args.source_meta:
        try:
            source_meta=json.loads(Path(args.source_meta).read_text())
        except Exception as exc:
            source_meta={'read_error':repr(exc),'path':args.source_meta}
    meta={'name':args.name,'nU':int(T.shape[0]),'nV':int(T.shape[1]),'nW':int(T.shape[2]),
          'nnz_count':int(T.sum()),'op':args.label,'source':args.input,
          'source_meta_path':args.source_meta,'source_meta':source_meta,
          'convention':'COO rows [Acoord,Browmajor,Crowmajor,value] over F2; B,C row-major 3x3 matrix-entry coordinates'}
    (outdir/(args.name+'.meta.json')).write_text(json.dumps(meta,indent=2)+'\n')
    summary={'input':args.input,'workspace':args.workspace,'name':args.name,
             'shape':list(T.shape),'nnz':int(T.sum()),'coo_path':str(outdir/(args.name+'.npy')),
             'meta_path':str(outdir/(args.name+'.meta.json')),'coo_rows':rows.tolist()}
    Path(args.workspace).mkdir(parents=True,exist_ok=True)
    (Path(args.workspace)/'prepare_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':
    main()
