#!/usr/bin/env python3
"""Generate quotient tensor and flip-cpd workspace for a given E11 prefix."""
import json, sys, argparse, shutil
from pathlib import Path
import numpy as np

def build_e11_core():
    T = np.zeros((9,9,9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T[1:,:,:]

def gf2_rank_int(vecs):
    basis = {}
    for v in vecs:
        x = int(v)
        while x:
            p = x.bit_length()-1
            if p in basis: x ^= basis[p]
            else: basis[p]=x; break
    return len(basis)

def annihilator_basis(prefix, n=8):
    d = gf2_rank_int(prefix)
    out = []
    for l in range(1, 1<<n):
        if all(bin(l&v).count('1')%2==0 for v in prefix):
            if gf2_rank_int(out+[l]) > len(out):
                out.append(l)
                if len(out) == n-d: return out
    raise RuntimeError

def quotient_core(core, ann):
    q = np.zeros((len(ann), core.shape[1], core.shape[2]), dtype=np.uint8)
    for i,l in enumerate(ann):
        for a in range(core.shape[0]):
            if (l>>a)&1: q[i] ^= core[a]
    return q

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--prefix', required=True, help='comma-separated prefix masks')
    ap.add_argument('--name', required=True, help='tensor name for flip-cpd')
    ap.add_argument('--workspace', type=Path, required=True)
    ap.add_argument('--flip-bin', type=Path, 
                    default=Path('data/e11_flip_workspace/bin/search2'))
    args = ap.parse_args()
    
    prefix = [int(x) for x in args.prefix.split(',') if x.strip()]
    assert len(prefix) == 4 and gf2_rank_int(prefix) == 4
    
    core = build_e11_core()
    ann = annihilator_basis(prefix, 8)
    Q = quotient_core(core, ann)
    
    ws = args.workspace
    (ws / 'data' / 'tensors').mkdir(parents=True, exist_ok=True)
    (ws / 'data' / 'schemes_modp' / args.name).mkdir(parents=True, exist_ok=True)
    (ws / 'data' / 'logs' / args.name).mkdir(parents=True, exist_ok=True)
    (ws / 'bin').mkdir(parents=True, exist_ok=True)
    
    # Save dense tensor
    np.save(ws / 'data' / 'tensors' / f'{args.name}.npy', Q)
    
    # Save sparse tensor for flip-cpd
    sparse = []
    for a in range(Q.shape[0]):
        for b in range(Q.shape[1]):
            for c in range(Q.shape[2]):
                if Q[a,b,c]:
                    sparse.append((a,b,c,1))
    sparse_arr = np.array(sparse, dtype=np.int8)
    sp_path = ws / 'data' / 'tensors' / f'{args.name}.npy'
    np.save(sp_path, sparse_arr)
    
    # Meta file
    meta = {
        'name': args.name,
        'nU': int(Q.shape[0]),
        'nV': int(Q.shape[1]),
        'nW': int(Q.shape[2]),
        'op': f'quotient_core_prefix_{"_".join(str(x) for x in prefix)}',
        'n1': int(Q.shape[0]),
        'n2': int(Q.shape[1]),
        'n3': int(Q.shape[2]),
        'source': f'E11 quotient by prefix {prefix}',
        'prefix': prefix,
        'annihilator': ann,
    }
    (ws / 'data' / 'tensors' / f'{args.name}.meta.json').write_text(
        json.dumps(meta, indent=2) + '\n')
    
    # Link flip-cpd binary
    flip_bin = ws / 'bin' / 'search2'
    if not flip_bin.exists():
        if args.flip_bin.exists():
            flip_bin.symlink_to(args.flip_bin.resolve())
        else:
            print(f"WARNING: flip binary not found at {args.flip_bin}")
    
    # Compute basic properties
    nnz = int(Q.sum())
    flat_A = gf2_rank_int([int(np.packbits(Q[a].reshape(-1), bitorder='little')[0]) if Q[a].sum() > 0 else 0 for a in range(Q.shape[0])])
    
    info = {
        'prefix': prefix, 'ann': ann, 'name': args.name,
        'shape': list(Q.shape), 'nnz': nnz,
        'workspace': str(ws),
    }
    (ws / 'quotient_info.json').write_text(json.dumps(info, indent=2) + '\n')
    
    print(f"Quotient tensor {args.name}: shape={Q.shape}, nnz={nnz}")
    print(f"Workspace: {ws}")
    print(f"Run: cd {ws} && ./bin/search2 {args.name} --target-rank <R> --pool-size 500 --path-limit 2000000 --max-attempts 3000 --stop 5000 --threads 8 --plus --plus-lim 20000 --save --id a")

if __name__ == '__main__':
    main()
