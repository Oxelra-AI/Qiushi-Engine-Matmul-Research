#!/usr/bin/env python3
"""Independent verifier for JSON outputs of general E11 quotient-lift SAT."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np


def bits(mask: int, n: int) -> np.ndarray:
    return np.array([(int(mask) >> i) & 1 for i in range(n)], dtype=np.uint8)


def build_t333() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T


def apply(shape, us, vs, ws):
    out = np.zeros(shape, dtype=np.uint8)
    for u, v, w in zip(us, vs, ws):
        if not (int(u) and int(v) and int(w)):
            continue
        out ^= (bits(u, shape[0]).reshape(-1,1,1) * bits(v, shape[1]).reshape(1,-1,1) * bits(w, shape[2]).reshape(1,1,-1)).astype(np.uint8)
    return out


def verify_dec(dec, shape, tensor):
    us = [int(x) for x in dec.get('u_masks', [])]
    vs = [int(x) for x in dec.get('v_masks', [])]
    ws = [int(x) for x in dec.get('w_masks', [])]
    if not (len(us) == len(vs) == len(ws)):
        return {'ok': False, 'reason': 'length mismatch', 'rank': None, 'diff': None}
    diff = int((apply(shape, us, vs, ws) ^ tensor).sum())
    return {'ok': diff == 0, 'rank': len(us), 'diff': diff, 'nonzero_terms': sum(1 for u,v,w in zip(us,vs,ws) if int(u) and int(v) and int(w))}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--json', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    data = json.loads(args.json.read_text())
    E11 = build_t333()[1:]
    T333 = build_t333()
    checked = []
    for rec in data.get('records', []):
        r = {'scheme_idx': rec.get('scheme_idx')}
        if 'e11_decomposition' in rec:
            r['e11'] = verify_dec(rec['e11_decomposition'], E11.shape, E11)
        if 't333_decomposition' in rec:
            r['t333'] = verify_dec(rec['t333_decomposition'], T333.shape, T333)
        if len(r) > 1:
            checked.append(r)
    result = {
        'purpose': 'independent recomputation of E11/T333 tensor identities from lift JSON masks',
        'source_json': str(args.json),
        'records_checked': len(checked),
        'all_checked_ok': all((v.get('ok') for r in checked for k,v in r.items() if isinstance(v, dict))),
        'checked': checked,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
