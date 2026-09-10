#!/usr/bin/env python3
"""Compare related analysis independently re-expanded Wang table with related analysis stored LUT pickle.

No Wang helper modules are imported.  The comparison treats related analysis's pickle as a
serialized mapping from packed subspace keys to lower bounds and checks exact
key/lower-bound equality against related analysis's independently generated split-key arrays.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import time
from collections import Counter
from pathlib import Path

import numpy as np


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def load_a02_arrays(path: Path):
    data = np.load(path)
    low = data['key_low']
    high = data['key_high']
    lbs = data['lbs']
    keys = [int(lo) + (int(hi) << 64) for lo, hi in zip(low, high)]
    return keys, [int(x) for x in lbs]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--related analysis-arrays', type=Path, default=Path('data/wang_reexpansion/wang_reexpanded_keys_lbs_split.npz'))
    ap.add_argument('--related analysis-lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--out', type=Path, default=Path('data/wang_reexpansion/a02_vs_a01_lut_compare.json'))
    args = ap.parse_args()
    t0 = time.time()
    keys, lbs = load_a02_arrays(args.a02_arrays)
    a02 = dict(zip(keys, lbs))
    t_load_a02 = time.time() - t0
    t1 = time.time()
    with args.a01_lut.open('rb') as f:
        payload = pickle.load(f)
    if isinstance(payload, dict) and 'lut' in payload:
        a01 = payload['lut']
        a01_meta = payload.get('meta', {})
    else:
        a01 = payload
        a01_meta = {}
    t_load_a01 = time.time() - t1
    missing_in_a01 = []
    missing_in_a02 = []
    lb_mismatches = []
    for k, lb in a02.items():
        old = a01.get(k)
        if old is None:
            missing_in_a01.append(k)
            if len(missing_in_a01) >= 20:
                break
        elif int(old) != lb:
            lb_mismatches.append({'key': int(k), 'a02_lb': int(lb), 'a01_lb': int(old)})
            if len(lb_mismatches) >= 20:
                break
    if not missing_in_a01 and not lb_mismatches:
        for k in a01.keys():
            if k not in a02:
                missing_in_a02.append(int(k))
                if len(missing_in_a02) >= 20:
                    break
    out = {
        'purpose': 'Exact table comparison after related analysis independent Wang certificate orbit re-expansion.',
        'a02_arrays': str(args.a02_arrays),
        'a02_arrays_sha256': sha256_file(args.a02_arrays),
        'a01_lut': str(args.a01_lut),
        'a01_lut_sha256': sha256_file(args.a01_lut),
        'a02_count': len(a02),
        'a01_count': len(a01),
        'counts_equal': len(a02) == len(a01),
        'exact_match': len(a02) == len(a01) and not missing_in_a01 and not missing_in_a02 and not lb_mismatches,
        'missing_in_a01_head': missing_in_a01[:20],
        'missing_in_a02_head': missing_in_a02[:20],
        'lb_mismatches_head': lb_mismatches[:20],
        'a02_lb_hist': dict(sorted(Counter(a02.values()).items())),
        'a01_lb_hist': dict(sorted(Counter(int(v) for v in a01.values()).items())),
        'a01_meta_brief': {k: a01_meta.get(k) for k in ['coverage_ok','conflict_count','subspace_count','record_count','action_count']},
        'load_a02_sec': t_load_a02,
        'load_a01_sec': t_load_a01,
        'elapsed_sec': time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: out[k] for k in ['a02_count','a01_count','counts_equal','exact_match','a02_lb_hist','elapsed_sec']}, indent=2, sort_keys=True))
    print('wrote', args.out)


if __name__ == '__main__':
    main()
