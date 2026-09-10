#!/usr/bin/env python3
from __future__ import annotations
import json, sys
from pathlib import Path
import numpy as np
SCRIPTS=Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path: sys.path.insert(0,str(SCRIPTS))
from fixed_A_saturation import build_matmul_tensor_f2, contraction_matrix, mat_rank_f2
from dual_basis_instrument import gf2_mat_inv, gf2_mat_mul
ROOT=Path('research/research_record')
OUTDIR=ROOT/'workspace/data/pencil_repair'

def row_to_mat(rows):
    M=np.zeros((9,9),dtype=np.uint8)
    for i,r in enumerate(rows):
        for j in range(9):
            M[i,j]=(r>>j)&1
    return M

def row_masks(M):
    out=[]
    for i in range(M.shape[0]):
        m=0
        for j in range(M.shape[1]):
            if int(M[i,j]): m|=1<<j
        out.append(m)
    return out

def Pmat():
    P=np.zeros((9,9),dtype=np.uint8)
    for j in range(3):
        for k in range(3): P[3*k+j,3*j+k]=1
    return P

def block_ranks(M):
    return [[int(mat_rank_f2(M[3*i:3*i+3,3*j:3*j+3])) for j in range(3)] for i in range(3)]

def block_rows(M):
    return [[row_masks(M[3*i:3*i+3,3*j:3*j+3]) for j in range(3)] for i in range(3)]

def main():
    P=Pmat()
    files=list(OUTDIR.glob('pencil_factor_cpsat_line_*minimal.json'))+[OUTDIR/'pencil_factor_cpsat_line_42_87_125.json']
    out=[]
    for f in files:
        if not f.exists(): continue
        data=json.loads(f.read_text())
        for rec in data['results']:
            if 'witness' not in rec: continue
            W=row_to_mat(rec['witness']['W_row_masks'])
            Wg=gf2_mat_mul(gf2_mat_mul(P,W),P.T)%2
            out.append({
                'file':str(f),'line':rec['line'],'budget':rec['budget_c10_c01_c11'],
                'ranks':[rec['witness']['rank_M1_plus_W'],rec['witness']['rank_M2_plus_W'],rec['witness']['rank_W']],
                'W_current_rows':rec['witness']['W_row_masks'],
                'W_grouped_rows':row_masks(Wg),'W_grouped_block_ranks':block_ranks(Wg),
                'W_grouped_blocks':block_rows(Wg)
            })
    p=OUTDIR/'minimal_witness_inspection.json'
    p.write_text(json.dumps({'records':out},indent=2,sort_keys=True)+'\n')
    print(json.dumps({'out':str(p),'records':len(out),'head':out[:2]},indent=2,sort_keys=True)[:4000])
if __name__=='__main__': main()
