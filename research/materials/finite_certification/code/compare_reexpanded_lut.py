#!/usr/bin/env python3
"""Compare the independent C++ Wang orbit re-expansion against the stored LUT.

Input binary format from wang_lut_reexpand.cpp:
  magic[8] = QWREXP1\0, uint64 count, repeated
  uint64 key_lo, uint64 key_hi, uint16 cert_index, uint16 lb, uint8 dim, uint8 proof_type.

The comparison loads the stored Wang LUT only as the object being audited: every
key/value in the independently generated binary must occur with the same lower
bound, the total count must equal the Gaussian-binomial sum, and every stored LUT
entry must be accounted for.  It also cross-checks the orbit-cache closed values
only as a diagnostic; theorem use should rest on the independent binary plus the
pinned Wang certificate/verifier.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import struct
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterator, Tuple

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
CACHE_PATH = Path("data/wang_f2_lb20/wang_orbit_closed_cache.pkl")
REEXP_BIN = Path("data/wang_reexpand/reexpanded_lut.bin")
REEXP_SUMMARY = Path("data/wang_reexpand/reexpand_summary.json")
OUT = Path("data/wang_reexpand/reexpanded_lut_compare.json")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def gaussian_binomial(n: int, k: int, q: int = 2) -> int:
    num = 1; den = 1
    for i in range(k):
        num *= q**n - q**i
        den *= q**k - q**i
    return num // den


def iter_reexpanded(path: Path) -> Iterator[Tuple[int, int, int, int, int]]:
    with path.open('rb') as f:
        magic = f.read(8)
        if magic != b'QWREXP1\0':
            raise ValueError(f'bad magic {magic!r}')
        count = struct.unpack('<Q', f.read(8))[0]
        for _ in range(count):
            raw = f.read(22)
            if len(raw) != 22:
                raise EOFError('truncated reexpanded binary')
            lo, hi, cert_index, lb, dim, proof_type = struct.unpack('<QQHHBB', raw)
            key = (hi << 64) | lo
            yield key, int(lb), int(cert_index), int(dim), int(proof_type)
        rest = f.read(1)
        if rest:
            raise ValueError('trailing bytes in reexpanded binary')


def key_dim(key: int) -> int:
    return int(key & 0xF)


def load_lut() -> Dict[int, int]:
    with LUT_PATH.open('rb') as f:
        obj = pickle.load(f)
    return obj['lut'] if isinstance(obj, dict) and 'lut' in obj else obj


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--bin', type=Path, default=REEXP_BIN)
    ap.add_argument('--summary', type=Path, default=REEXP_SUMMARY)
    ap.add_argument('--out', type=Path, default=OUT)
    args = ap.parse_args()
    t0 = time.time()
    lut = load_lut()
    seen = set()
    mismatch_head = []
    missing_in_stored_head = []
    count = 0
    by_dim = Counter(); hist = defaultdict(Counter); cert_hist = Counter(); proof_hist = Counter()
    cert_by_dim = defaultdict(Counter)
    for key, lb, cert_index, dim, proof_type in iter_reexpanded(args.bin):
        count += 1
        seen.add(key)
        by_dim[dim] += 1
        hist[dim][lb] += 1
        cert_hist[cert_index] += 1
        proof_hist[proof_type] += 1
        cert_by_dim[dim][cert_index] += 1
        stored = lut.get(key)
        if stored is None:
            if len(missing_in_stored_head) < 20:
                missing_in_stored_head.append({'key': str(key), 'dim': dim, 'lb': lb, 'cert_index': cert_index})
        elif int(stored) != lb:
            if len(mismatch_head) < 20:
                mismatch_head.append({'key': str(key), 'dim': dim, 'reexpanded_lb': lb, 'stored_lb': int(stored), 'cert_index': cert_index})
    stored_missing_head = []
    stored_missing_count = 0
    for key, lb in lut.items():
        if key not in seen:
            stored_missing_count += 1
            if len(stored_missing_head) < 20:
                stored_missing_head.append({'key': str(int(key)), 'dim': key_dim(int(key)), 'stored_lb': int(lb)})
    expected_by_dim = {d: gaussian_binomial(9,d) for d in range(10)}
    expected_total = sum(expected_by_dim.values())
    summary = json.loads(args.summary.read_text()) if args.summary.exists() else None
    out = {
        'schema': 'reexpanded_lut_compare_v1',
        'meaning': 'Independent C++ expansion of the 496 Wang certificate representatives under tensor automorphism generators agrees value-by-value with the stored full LUT.',
        'reexpanded_binary_path': str(args.bin),
        'reexpanded_binary_sha256': sha256(args.bin),
        'reexpanded_summary_path': str(args.summary),
        'reexpanded_summary': summary,
        'stored_lut_path': str(LUT_PATH),
        'stored_lut_sha256': sha256(LUT_PATH),
        'stored_lut_count': len(lut),
        'reexpanded_count': count,
        'expected_subspace_count': expected_total,
        'count_by_dimension': {str(k): int(by_dim[k]) for k in range(10)},
        'expected_by_dimension': {str(k): int(v) for k,v in expected_by_dim.items()},
        'lb_hist_by_dimension': {str(d): {str(k): int(v) for k,v in sorted(hist[d].items())} for d in range(10)},
        'missing_in_stored_count': len(missing_in_stored_head),
        'missing_in_stored_head': missing_in_stored_head,
        'stored_missing_count': stored_missing_count,
        'stored_missing_head': stored_missing_head,
        'value_mismatch_count_head': len(mismatch_head),
        'value_mismatch_head': mismatch_head,
        'unique_cert_indices': len(cert_hist),
        'cert_index_hist_head': {str(k): int(v) for k,v in sorted(cert_hist.items())[:20]},
        'proof_type_hist': {str(k): int(v) for k,v in sorted(proof_hist.items())},
        'elapsed_sec': time.time() - t0,
    }
    out['ok'] = (
        count == expected_total == len(lut)
        and all(by_dim[d] == expected_by_dim[d] for d in range(10))
        and not missing_in_stored_head
        and stored_missing_count == 0
        and not mismatch_head
        and bool(summary is None or summary.get('ok') is True)
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'ok': out['ok'],
        'out': str(args.out),
        'count': count,
        'expected': expected_total,
        'stored': len(lut),
        'stored_missing_count': stored_missing_count,
        'mismatch_head_count': len(mismatch_head),
        'elapsed_sec': out['elapsed_sec'],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
