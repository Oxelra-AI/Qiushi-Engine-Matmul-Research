#!/usr/bin/env python3
"""related analysis independent re-expansion of Wang's F2 T333 A-side certificate orbits.

The script intentionally avoids importing the related analysis/related analysis Wang helper modules.  It
parses the text-format certificate, regenerates the natural GL(3,2) x GL(3,2)
plus transpose action on 3x3 A-side linear forms, expands every recorded orbit,
and checks coverage/conflicts against the Gaussian-binomial counts for subspaces
of F2^9.  It saves deterministic key/lower-bound arrays plus a concise metadata
record for later comparison.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
import time
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np

N = 9
MASK = (1 << N) - 1


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def decode_bytes_literal(s: str) -> bytes:
    return ast.literal_eval(s).encode('latin1')


def parse_cert(path: Path):
    text = path.read_text(errors='replace')
    top = {}
    for key in ['problem_name', 'characteristic', 'extension_degree', 'na', 'nb', 'nc']:
        m = re.search(rf'^\s*{key}:\s*(.+)$', text, flags=re.M)
        if m:
            raw = m.group(1).strip()
            top[key] = ast.literal_eval(raw) if raw.startswith('"') else int(raw)
    recs = []
    for pos, block in enumerate(text.split('constrained_tensors {')[1:]):
        m_idx = re.search(r'\n\s*index:\s*(\d+)', '\n' + block)
        m_lb = re.search(r'\n\s*rank_lower_bound:\s*(-?\d+)', '\n' + block)
        if not m_lb:
            raise ValueError(f'missing rank_lower_bound in block {pos}')
        m_cons = re.search(r'\n\s*constraints:\s*(".*")', '\n' + block)
        vals = []
        if m_cons:
            b = decode_bytes_literal(m_cons.group(1))
            if len(b) % 2:
                raise ValueError(f'odd bytes in constraints block {pos}')
            vals = [b[i] | (b[i + 1] << 8) for i in range(0, len(b), 2)]
        ptype = 'none'
        for tag, name in [('flatten','flatten_matrix_proof'), ('forced_product','forced_product_proof'), ('degenerate','degenerate_proof'), ('backtracking','backtracking_proof')]:
            if name in block:
                ptype = tag
                break
        recs.append({'pos': pos, 'index': int(m_idx.group(1)) if m_idx else pos, 'basis_raw': vals, 'lb': int(m_lb.group(1)), 'proof_type': ptype})
    return top, recs


def mat_rows_from_mask(x: int):
    return ((x >> 0) & 7, (x >> 3) & 7, (x >> 6) & 7)


def mat_mask(rows) -> int:
    out = 0
    for i, r in enumerate(rows):
        out |= (r & 7) << (3 * i)
    return out


def parity(x: int) -> int:
    return x.bit_count() & 1


def mat_rank(rows) -> int:
    basis = [0, 0, 0]
    rk = 0
    for row in rows:
        v = row
        while v:
            p = v.bit_length() - 1
            if basis[p]:
                v ^= basis[p]
            else:
                basis[p] = v
                rk += 1
                break
    return rk


def mat_mul(A, B):
    rows = []
    for i in range(3):
        row = 0
        ai = A[i]
        for k in range(3):
            if (ai >> k) & 1:
                row ^= B[k]
        rows.append(row)
    return tuple(rows)


def mat_transpose(A):
    rows = []
    for i in range(3):
        row = 0
        for j in range(3):
            if (A[j] >> i) & 1:
                row |= 1 << j
        rows.append(row)
    return tuple(rows)


def gl3():
    mats = [mat_rows_from_mask(x) for x in range(1 << 9) if mat_rank(mat_rows_from_mask(x)) == 3]
    assert len(mats) == 168
    return mats


def elementary(bit: int):
    rows = [0, 0, 0]
    rows[bit // 3] = 1 << (bit % 3)
    return tuple(rows)


def build_actions():
    # Since L and R range over all GL(3,2), using L*X*R and L*X^T*R generates
    # the same orbit group as the inverse/dual convention; the coverage and
    # conflict tests below are insensitive to the particular GL variable names.
    gs = gl3()
    seen = set()
    actions = []
    Es = [elementary(i) for i in range(9)]
    for L in gs:
        for R in gs:
            for tr in (False, True):
                imgs = []
                for E in Es:
                    X = mat_transpose(E) if tr else E
                    imgs.append(mat_mask(mat_mul(mat_mul(L, X), R)))
                tup = tuple(imgs)
                if tup not in seen:
                    seen.add(tup)
                    actions.append(tup)
    assert len(actions) == 2 * 168 * 168
    return actions


def apply_action_vec(v: int, img) -> int:
    out = 0
    x = v & MASK
    while x:
        lb = x & -x
        j = lb.bit_length() - 1
        out ^= img[j]
        x ^= lb
    return out


def rref(rows):
    basis = [0] * N
    for row in rows:
        v = row & MASK
        while v:
            p = v.bit_length() - 1
            if basis[p]:
                v ^= basis[p]
            else:
                basis[p] = v
                break
    for p in range(N):
        if basis[p]:
            for q in range(N):
                if q != p and basis[q] and ((basis[q] >> p) & 1):
                    basis[q] ^= basis[p]
    return tuple(basis[p] for p in range(N - 1, -1, -1) if basis[p])


def pack_key(basis) -> int:
    key = len(basis)
    sh = 4
    for b in basis:
        key |= int(b) << sh
        sh += 9
    return key


def unpack_key(key: int):
    d = key & 15
    out = []
    x = key >> 4
    for _ in range(d):
        out.append(x & MASK)
        x >>= 9
    return tuple(out)


def transform_basis_key(basis, img) -> int:
    return pack_key(rref(apply_action_vec(v, img) for v in basis))


def gaussian_binomial(n: int, k: int, q: int = 2) -> int:
    num = 1
    den = 1
    for i in range(k):
        num *= q**n - q**i
        den *= q**k - q**i
    return num // den


def in_span(v: int, basis) -> bool:
    piv = {b.bit_length() - 1: b for b in basis if b}
    x = v
    while x:
        p = x.bit_length() - 1
        b = piv.get(p)
        if b is None:
            return False
        x ^= b
    return True


def subspace_points(basis):
    pts = [0]
    for b in basis:
        pts += [x ^ b for x in pts]
    return [x for x in pts if x]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cert', type=Path, default=Path('data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt'))
    ap.add_argument('--outdir', type=Path, default=Path('data/wang_reexpansion'))
    ap.add_argument('--save-arrays', action='store_true')
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    top, recs = parse_cert(args.cert)
    actions = build_actions()
    lut = {}
    key_to_orbits = {}
    conflicts = []
    orbit_summaries = []
    for j, rec in enumerate(recs):
        basis = rref(rec['basis_raw'])
        local = set(transform_basis_key(basis, act) for act in actions)
        for key in local:
            old = lut.get(key)
            if old is not None and old != rec['lb']:
                conflicts.append({'key': int(key), 'old_lb': int(old), 'new_lb': int(rec['lb']), 'old_orbits': key_to_orbits.get(key, []), 'new_orbit_pos': rec['pos']})
            lut[key] = max(old, rec['lb']) if old is not None else rec['lb']
            key_to_orbits.setdefault(key, []).append(rec['pos'])
        orbit_summaries.append({'pos': rec['pos'], 'index': rec['index'], 'dim': len(basis), 'lb': rec['lb'], 'proof_type': rec['proof_type'], 'orbit_size': len(local), 'basis': list(map(int, basis))})
        if (j + 1) % 25 == 0 or j + 1 == len(recs):
            print(f'expanded {j+1}/{len(recs)} orbits; subspaces={len(lut)} elapsed={time.time()-t0:.1f}s', flush=True)
    actual = Counter(k & 15 for k in lut)
    expected = {d: gaussian_binomial(N, d) for d in range(N + 1)}
    dim_lb = defaultdict(Counter)
    for k, lb in lut.items():
        dim_lb[k & 15][lb] += 1
    dim1_rank_lb = Counter()
    for k, lb in lut.items():
        if (k & 15) == 1:
            row = unpack_key(k)[0]
            dim1_rank_lb[f'rank{mat_rank(mat_rows_from_mask(row))}_lb{lb}'] += 1
    meta = {
        'purpose': 'related analysis independent expansion of Wang F2 T333 certificate orbits using self-contained parser, GL action and RREF code.',
        'cert_path': str(args.cert),
        'cert_sha256': sha256_file(args.cert),
        'top_fields': top,
        'record_count': len(recs),
        'action_count': len(actions),
        'subspace_count': len(lut),
        'expected_subspace_count': sum(expected.values()),
        'actual_by_dimension': {str(d): actual[d] for d in range(N + 1)},
        'expected_by_dimension': {str(d): expected[d] for d in range(N + 1)},
        'coverage_ok': all(actual[d] == expected[d] for d in range(N + 1)),
        'conflict_count': len(conflicts),
        'conflicts_head': conflicts[:10],
        'orbit_size_sum': sum(o['orbit_size'] for o in orbit_summaries),
        'overlap_key_count': sum(1 for v in key_to_orbits.values() if len(v) > 1),
        'orbit_dim_lb_counts': {str(dim): dict(sorted(cnt.items())) for dim, cnt in sorted(dim_lb.items())},
        'dim1_rank_lb_counts': dict(sorted(dim1_rank_lb.items())),
        'proof_type_count_by_orbit': dict(Counter(r['proof_type'] for r in recs)),
        'orbit_summaries_head': orbit_summaries[:20],
        'orbit_summaries_tail': orbit_summaries[-20:],
        'elapsed_sec': time.time() - t0,
    }
    arrays_path = None
    if args.save_arrays:
        # Packed subspace keys use 4 + 9*d bits and reach 85 bits for d=9,
        # so split into two uint64 words rather than truncating to uint64.
        sorted_keys = sorted(lut)
        low = np.array([int(k) & ((1 << 64) - 1) for k in sorted_keys], dtype=np.uint64)
        high = np.array([int(k) >> 64 for k in sorted_keys], dtype=np.uint64)
        lbs = np.array([lut[int(k)] for k in sorted_keys], dtype=np.uint8)
        arrays_path = args.outdir / 'wang_reexpanded_keys_lbs_split.npz'
        np.savez_compressed(arrays_path, key_low=low, key_high=high, lbs=lbs)
        meta['arrays_path'] = str(arrays_path)
        meta['arrays_format'] = 'sorted keys split as key = key_low + 2^64 * key_high; lbs aligned with sorted keys'
        meta['arrays_sha256'] = sha256_file(arrays_path)
    meta_path = args.outdir / 'wang_reexpanded_meta.json'
    meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: meta[k] for k in ['record_count','action_count','subspace_count','coverage_ok','conflict_count','actual_by_dimension','dim1_rank_lb_counts','elapsed_sec']}, indent=2, sort_keys=True))
    print('wrote', meta_path)
    if arrays_path:
        print('wrote', arrays_path, meta.get('arrays_sha256'))


if __name__ == '__main__':
    main()
