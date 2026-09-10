#!/usr/bin/env python3
"""analysis correction: canonical LUT key decoding and corrected rep2 base scan.

analysis introduced local diagnostic functions that decoded a Wang LUT key by
reading 9-bit chunks from bit 0.  That is wrong: the low 4 bits store the
subspace dimension d, followed by exactly d nine-bit RREF basis vectors.  This
script imports the canonical decoder from wang_capacity_lazy, demonstrates the
error on the cited key 0x11945003, round-trips the LUT basis encoding, and
recomputes vertex-exclusion/base-graph counts for the rep2 prefixes using the
canonical decoder.

Outputs are diagnostic evidence, not a theorem proof.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import pickle
import sys
import time
from collections import Counter
from typing import Dict, Iterable, List, Sequence, Set, Tuple

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))

from wang_capacity_lazy import (  # noqa:E402
    unpack_basis,
    rref_key,
    subspace_points_from_basis,
    in_rowspace,
)
from graph_coloring_certificate import load_lut, make_pivot_dict, in_span_piv  # noqa:E402
from witness_subset_separation import process_rep2  # noqa:E402


def broken_unpack(key: int) -> List[int]:
    """The incorrect analysis decoder, retained only for comparison."""
    vecs: List[int] = []
    r = int(key)
    while r:
        v = r & 0x1FF
        r >>= 9
        if v:
            vecs.append(v)
    return vecs


def span_points(basis: Sequence[int]) -> Set[int]:
    return set(int(x) for x in subspace_points_from_basis(tuple(int(b) for b in basis)))


def pivot_duplicate_count(basis: Sequence[int]) -> int:
    pivots = [int(b).bit_length() - 1 for b in basis if int(b)]
    return len(pivots) - len(set(pivots))


def canonical_key_audit(lut: Dict[int, int], max_examples: int = 5) -> dict:
    """Audit that keys decode as canonical RREF bases suitable for pivot membership."""
    dim_hist = Counter()
    lb_hist = Counter()
    dim_lb_hist = Counter()
    roundtrip_bad: List[dict] = []
    duplicate_pivot_examples: List[dict] = []
    t0 = time.time()
    for key_raw, lb_raw in lut.items():
        key = int(key_raw)
        lb = int(lb_raw)
        basis = unpack_basis(key)
        d = key & 0xF
        dim_hist[d] += 1
        lb_hist[lb] += 1
        dim_lb_hist[(d, lb)] += 1
        rt = rref_key(basis)
        if rt != key and len(roundtrip_bad) < max_examples:
            roundtrip_bad.append({
                'key': key,
                'key_hex': hex(key),
                'd_low_nibble': d,
                'basis': list(map(int, basis)),
                'roundtrip': int(rt),
                'roundtrip_hex': hex(int(rt)),
            })
        dup = pivot_duplicate_count(basis)
        if dup and len(duplicate_pivot_examples) < max_examples:
            duplicate_pivot_examples.append({
                'key': key,
                'key_hex': hex(key),
                'basis': list(map(int, basis)),
                'duplicate_pivot_count': dup,
            })
    return {
        'elapsed_sec': round(time.time() - t0, 3),
        'row_count': len(lut),
        'dim_hist': {str(k): int(v) for k, v in sorted(dim_hist.items())},
        'lb_hist': {str(k): int(v) for k, v in sorted(lb_hist.items())},
        'high_lb_dim_hist': {
            f'{d},{lb}': int(c)
            for (d, lb), c in sorted(dim_lb_hist.items())
            if lb >= 17
        },
        'roundtrip_mismatch_examples': roundtrip_bad,
        'roundtrip_all_ok': len(roundtrip_bad) == 0,
        'duplicate_pivot_examples': duplicate_pivot_examples,
        'duplicate_pivot_examples_found': len(duplicate_pivot_examples),
    }


def vertex_exclusion_scan(lut: Dict[int, int], prefix: Sequence[int], candidates: Sequence[int]) -> dict:
    """Scan canonical LUT rows for residual-0 vertex exclusions under a fixed prefix."""
    prefix = [int(x) for x in prefix]
    prefix_set = set(prefix)
    cand_set = set(int(x) for x in candidates)
    excluded: Set[int] = set()
    examples: Dict[int, dict] = {}
    by_reason = Counter()
    scanned = 0
    residual0_rows = 0
    t0 = time.time()
    for key_raw, lb_raw in lut.items():
        key = int(key_raw)
        lb = int(lb_raw)
        cap = 20 - lb
        if cap < 0 or cap > len(prefix):
            continue
        # residual=0 needs prefix_count=cap.  A quick lower-bound on lb is implicit here.
        basis = unpack_basis(key)
        cnt = sum(1 for p in prefix if in_rowspace(int(p), basis, n=9))
        if cnt != cap:
            continue
        pts = span_points(basis) & cand_set
        if not pts:
            continue
        scanned += 1
        residual0_rows += 1
        by_reason[(key & 0xF, lb, cnt)] += 1
        for p in pts:
            excluded.add(int(p))
            if p not in examples and len(examples) < 20:
                examples[int(p)] = {
                    'key': key,
                    'key_hex': hex(key),
                    'lb': lb,
                    'dim': key & 0xF,
                    'basis': list(map(int, basis)),
                    'prefix_count': cnt,
                    'cap': cap,
                    'span_size': len(pts),
                }
    return {
        'prefix': prefix,
        'candidate_count': len(candidates),
        'excluded_count': len(excluded),
        'survivor_count': len(cand_set - excluded),
        'survivors_head': sorted(cand_set - excluded)[:50],
        'residual0_rows_with_candidates': residual0_rows,
        'by_dim_lb_prefixcount': {f'{d},{lb},{cnt}': int(c) for (d, lb, cnt), c in sorted(by_reason.items())},
        'examples': {str(k): v for k, v in sorted(examples.items())},
        'elapsed_sec': round(time.time() - t0, 3),
    }


def process_rep2_base_scan(lut: Dict[int, int], prefix: Sequence[int], candidates: Sequence[int]) -> dict:
    """Run the existing base-graph builder and record corrected prefix counts."""
    t0 = time.time()
    info = process_rep2(lut, prefix, candidates)
    elapsed = time.time() - t0
    return {
        'prefix': [int(x) for x in prefix],
        'target': int(info['target']),
        'candidate_count': len(candidates),
        'impossible_rows_count': len(info['impossible_rows']),
        'vertex_exclusions_count': len(info['vertex_key']),
        'survivor_count': len(info['survivors']),
        'survivors_head': list(map(int, info['survivors'][:50])),
        'edge_count': len(info['edge_key']),
        'row_counts': {str(k): int(v) for k, v in info['row_counts'].items()},
        'elapsed_sec': round(elapsed, 3),
    }


def specific_key_audit(keys: Sequence[int]) -> List[dict]:
    out: List[dict] = []
    for key in keys:
        key = int(key)
        basis = unpack_basis(key)
        broken = broken_unpack(key)
        sp = span_points(basis)
        piv = make_pivot_dict(basis)
        out.append({
            'key': key,
            'key_hex': hex(key),
            'dimension_low_nibble': key & 0xF,
            'correct_basis': list(map(int, basis)),
            'correct_basis_len': len(basis),
            'canonical_roundtrip_ok': rref_key(basis) == key,
            'duplicate_pivots_correct_basis': pivot_duplicate_count(basis),
            'broken_basis': list(map(int, broken)),
            'broken_basis_len': len(broken),
            'span_contains': {str(p): (p in sp) for p in [1, 2, 3, 17, 100, 256, 273, 511]},
            'pivot_membership_agrees_on_test_points': {
                str(p): (in_span_piv(piv, p) == (p in sp))
                for p in [1, 2, 3, 17, 100, 256, 273, 511]
            },
        })
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', default='data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--out-dir', default='data/decode_correction')
    ap.add_argument('--skip-full-key-audit', action='store_true')
    args = ap.parse_args()

    lut_path = pathlib.Path(args.lut)
    out_dir = pathlib.Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    print(f'Loading LUT {lut_path}...')
    lut = load_lut(lut_path)
    print(f'  rows: {len(lut):,}')

    result = {
        'schema': 'corrected_decode_and_rep2_base_v1',
        'lut_path': str(lut_path),
        'specific_key_audit': specific_key_audit([0x11945003, 0x809B103, 0x13D61203]),
    }

    if not args.skip_full_key_audit:
        print('Auditing canonical key roundtrip / pivot uniqueness over the full LUT...')
        result['canonical_key_audit'] = canonical_key_audit(lut)
        print(json.dumps({
            'roundtrip_all_ok': result['canonical_key_audit']['roundtrip_all_ok'],
            'duplicate_pivot_examples_found': result['canonical_key_audit']['duplicate_pivot_examples_found'],
            'audit_sec': result['canonical_key_audit']['elapsed_sec'],
        }, sort_keys=True))

    prefix12 = [1, 2]
    cands12 = [p for p in range(1, 512) if p not in set(prefix12)]
    print('Scanning canonical vertex exclusions for prefix [1,2]...')
    result['canonical_vertex_scan_prefix_12'] = vertex_exclusion_scan(lut, prefix12, cands12)
    print(json.dumps({
        'prefix': prefix12,
        'excluded': result['canonical_vertex_scan_prefix_12']['excluded_count'],
        'survivors': result['canonical_vertex_scan_prefix_12']['survivor_count'],
        'sec': result['canonical_vertex_scan_prefix_12']['elapsed_sec'],
    }, sort_keys=True))

    prefix123 = [1, 2, 3]
    cands123 = [p for p in range(1, 512) if p not in set(prefix123)]
    print('Scanning canonical vertex exclusions for prefix [1,2,3]...')
    result['canonical_vertex_scan_prefix_123'] = vertex_exclusion_scan(lut, prefix123, cands123)
    print(json.dumps({
        'prefix': prefix123,
        'excluded': result['canonical_vertex_scan_prefix_123']['excluded_count'],
        'survivors': result['canonical_vertex_scan_prefix_123']['survivor_count'],
        'sec': result['canonical_vertex_scan_prefix_123']['elapsed_sec'],
    }, sort_keys=True))

    print('Running existing process_rep2 base graph builder for prefix [1,2]...')
    result['process_rep2_prefix_12'] = process_rep2_base_scan(lut, prefix12, cands12)
    print(json.dumps({
        'prefix': prefix12,
        'vex': result['process_rep2_prefix_12']['vertex_exclusions_count'],
        'survivors': result['process_rep2_prefix_12']['survivor_count'],
        'edges': result['process_rep2_prefix_12']['edge_count'],
        'sec': result['process_rep2_prefix_12']['elapsed_sec'],
    }, sort_keys=True))

    print('Running existing process_rep2 base graph builder for prefix [1,2,3]...')
    result['process_rep2_prefix_123'] = process_rep2_base_scan(lut, prefix123, cands123)
    print(json.dumps({
        'prefix': prefix123,
        'vex': result['process_rep2_prefix_123']['vertex_exclusions_count'],
        'survivors': result['process_rep2_prefix_123']['survivor_count'],
        'edges': result['process_rep2_prefix_123']['edge_count'],
        'sec': result['process_rep2_prefix_123']['elapsed_sec'],
    }, sort_keys=True))

    out_path = out_dir / 'corrected_decode_and_rep2_base.json'
    out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'Saved {out_path}')


if __name__ == '__main__':
    main()
