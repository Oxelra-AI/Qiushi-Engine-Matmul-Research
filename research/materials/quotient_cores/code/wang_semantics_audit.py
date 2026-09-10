#!/usr/bin/env python3
"""analysis semantic audit for the Wang lower-bound/coset route.

This script is intentionally independent of the row generator used in analysis.
It implements the Wang LUT key unpacking, RREF packing, subspace span masks,
and matrix transpose directly, then checks:
  * a WANG512 row binary is exactly the semantic image of the LUT at a length n:
      row mask = nonzero points in W, cap = n - LB(W), dim = dim(W),
    with dim-0 and cap>max_cap rows skipped as in the binary metadata;
  * the LUT is invariant under A-matrix transpose, LB(W)=LB(W^T);
  * the dim-2 orbit records that are load-bearing for the coset theorem are
    exactly the all-high-rank orbits 484--491, not orbit 479.
"""
from __future__ import annotations
import argparse, hashlib, json, pickle, struct, time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

NBITS = 9
MAGIC = b"WANG512\x01"
DEFAULT_LUT = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
DEFAULT_BIN20 = Path("data/wang_native/full_tensor/full_wang512_cap19_len20_all_dim9_allbinding.bin")
DEFAULT_DIM2 = Path("data/wang_analysis/dim2_reduction_audit.json")
DEFAULT_OUT = Path("data/audit/wang_semantics_audit.json")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def load_lut(path: Path) -> Dict[int, int]:
    obj = pickle.load(path.open('rb'))
    lut = obj['lut'] if isinstance(obj, dict) and 'lut' in obj else obj
    return {int(k): int(v) for k, v in lut.items()}


def unpack_key(key: int) -> Tuple[int, ...]:
    d = int(key) & 0xF
    packed = int(key) >> 4
    return tuple((packed >> (NBITS * i)) & ((1 << NBITS) - 1) for i in range(d))


def rref_basis(rows: Iterable[int]) -> Tuple[int, ...]:
    basis: List[int] = []
    for x0 in rows:
        x = int(x0)
        if x == 0:
            continue
        for rb in basis:
            p = rb.bit_length() - 1
            if (x >> p) & 1:
                x ^= rb
        if x == 0:
            continue
        p = x.bit_length() - 1
        for i, rb in enumerate(basis):
            if (rb >> p) & 1:
                basis[i] = rb ^ x
        basis.append(x)
        basis.sort(key=lambda z: z.bit_length(), reverse=True)
    return tuple(basis)


def pack_basis(basis: Sequence[int]) -> int:
    x = 0
    for i, b in enumerate(basis):
        x |= int(b) << (NBITS * i)
    return (x << 4) | len(basis)


def key_from_rows(rows: Iterable[int]) -> int:
    return pack_basis(rref_basis(rows))


def span_words_from_basis(basis: Sequence[int]) -> Tuple[int, ...]:
    words = [0] * 8
    d = len(basis)
    for m in range(1, 1 << d):
        v = 0
        for i, b in enumerate(basis):
            if (m >> i) & 1:
                v ^= int(b)
        if 1 <= v <= 511:
            words[v >> 6] |= 1 << (v & 63)
    return tuple(words)


def transpose_mask(a: int) -> int:
    out = 0
    for i in range(3):
        for j in range(3):
            if (a >> (3 * i + j)) & 1:
                out |= 1 << (3 * j + i)
    return out


def gf2_rank_rows(rows: Sequence[int], ncols: int = 3) -> int:
    basis: List[int] = []
    for x0 in rows:
        x = int(x0)
        for rb in basis:
            p = rb.bit_length() - 1
            if (x >> p) & 1:
                x ^= rb
        if x == 0:
            continue
        p = x.bit_length() - 1
        for i, rb in enumerate(basis):
            if (rb >> p) & 1:
                basis[i] = rb ^ x
        basis.append(x)
        basis.sort(key=lambda z: z.bit_length(), reverse=True)
    return len(basis)


def mat_rank(a: int) -> int:
    rows = []
    for i in range(3):
        row = 0
        for j in range(3):
            if (a >> (3 * i + j)) & 1:
                row |= 1 << j
        rows.append(row)
    return gf2_rank_rows(rows, 3)


def read_bin_header(path: Path) -> Dict:
    with path.open('rb') as f:
        magic = f.read(8)
        nrows = struct.unpack('<I', f.read(4))[0]
    return {'path': str(path), 'magic': magic.decode('latin1'), 'nrows': int(nrows), 'size_bytes': path.stat().st_size,
            'expected_size_bytes': 12 + 68 * int(nrows), 'size_matches': path.stat().st_size == 12 + 68 * int(nrows)}


def audit_binary(lut: Dict[int, int], path: Path, length: int, max_cap: int) -> Dict:
    t0 = time.time()
    header = read_bin_header(path)
    cap_hist = Counter(); dim_hist = Counter(); pop_hist = Counter()
    expected_rows = 0; skipped_dim0 = 0; skipped_cap = 0; compared = 0
    first_mismatches = []
    with path.open('rb') as f:
        magic = f.read(8)
        if magic != MAGIC:
            raise ValueError(f'bad magic {magic!r}')
        file_rows = struct.unpack('<I', f.read(4))[0]
        for key, lb in lut.items():
            dim = int(key) & 0xF
            cap = int(length) - int(lb)
            if dim == 0:
                skipped_dim0 += 1
                continue
            if cap < 0 or cap > max_cap:
                skipped_cap += 1
                continue
            basis = unpack_key(key)
            words_expected = span_words_from_basis(basis)
            rec = f.read(68)
            if len(rec) != 68:
                first_mismatches.append({'kind': 'unexpected_eof', 'expected_row': expected_rows, 'key': str(key)})
                break
            cap_b, dim_b, reserved = struct.unpack('<BBH', rec[:4])
            words_b = struct.unpack('<8Q', rec[4:68])
            if cap_b != cap or dim_b != dim or reserved != 0 or tuple(words_b) != words_expected:
                if len(first_mismatches) < 10:
                    first_mismatches.append({
                        'kind': 'row_mismatch', 'row': expected_rows, 'key': str(key), 'lb': int(lb),
                        'expected': {'cap': cap, 'dim': dim, 'words': [int(w) for w in words_expected]},
                        'binary': {'cap': int(cap_b), 'dim': int(dim_b), 'reserved': int(reserved), 'words': [int(w) for w in words_b]},
                    })
            cap_hist[cap] += 1; dim_hist[dim] += 1; pop_hist[sum(int(w).bit_count() for w in words_expected)] += 1
            expected_rows += 1; compared += 1
        leftover = f.read(1)
    return {
        'schema': 'binary_semantics_audit_v1',
        'binary': header,
        'length': int(length), 'max_cap': int(max_cap),
        'source_lut_rows': len(lut), 'expected_rows': expected_rows, 'compared_rows': compared,
        'file_rows': int(header['nrows']), 'row_count_matches': expected_rows == int(header['nrows']),
        'binary_exact_match': (expected_rows == int(header['nrows']) and not first_mismatches and leftover == b''),
        'first_mismatches': first_mismatches,
        'leftover_after_expected': bool(leftover),
        'skipped_dim0': skipped_dim0, 'skipped_cap': skipped_cap,
        'cap_hist': dict(sorted((int(k), int(v)) for k, v in cap_hist.items())),
        'dim_hist': dict(sorted((int(k), int(v)) for k, v in dim_hist.items())),
        'popcount_hist_head_tail': {
            'head': dict(list(sorted((int(k), int(v)) for k, v in pop_hist.items()))[:10]),
            'tail': dict(list(sorted((int(k), int(v)) for k, v in pop_hist.items()))[-10:]),
        },
        'elapsed_sec': time.time() - t0,
    }


def audit_transpose(lut: Dict[int, int], max_mismatches: int = 20) -> Dict:
    t0 = time.time(); mismatches = []; dim_hist = Counter(); checked = 0
    for key, lb in lut.items():
        basis = unpack_key(key)
        tkey = key_from_rows(transpose_mask(b) for b in basis)
        tlb = lut.get(tkey)
        if tlb != lb and len(mismatches) < max_mismatches:
            mismatches.append({'key': str(key), 'basis': list(basis), 'lb': int(lb), 'transpose_key': str(tkey), 'transpose_lb': None if tlb is None else int(tlb), 'transpose_basis': list(unpack_key(tkey))})
        elif tlb != lb:
            # keep counting but do not store every mismatch
            pass
        dim_hist[int(key) & 0xF] += 1; checked += 1
    # Recount mismatch count exactly in a second lightweight way only if needed would be costly;
    # instead increment in-loop.
    mismatch_count = 0
    for key, lb in lut.items():
        tkey = key_from_rows(transpose_mask(b) for b in unpack_key(key))
        if lut.get(tkey) != lb:
            mismatch_count += 1
    return {'schema': 'lut_transpose_audit_v1', 'checked': checked, 'mismatch_count': mismatch_count,
            'first_mismatches': mismatches, 'dim_hist': dict(sorted((int(k), int(v)) for k, v in dim_hist.items())),
            'elapsed_sec': time.time() - t0}


def audit_dim2(path: Path) -> Dict:
    obj = json.loads(path.read_text())
    rows = obj['records']
    by_idx = {int(r['index']): r for r in rows}
    all_high = [i for i, r in by_idx.items() if int(r['rank_ge2_count']) == 3]
    one_rank_one_two_high = [i for i, r in by_idx.items() if int(r['rank_ge2_count']) == 2 and r.get('rank_hist', {}).get('1') == 1]
    two_or_more_rank_one = [i for i, r in by_idx.items() if int(r['rank_ge2_count']) <= 1]
    raised_all_high = [i for i in all_high if int(by_idx[i]['current_overlay_lb']) >= 19 and by_idx[i]['occupation_raise_status'] == 'INFEASIBLE']
    return {
        'schema': 'dim2_loadbearing_audit_v1',
        'source': str(path),
        'all_high_rank_pair_orbits_load_bearing': sorted(all_high),
        'all_high_rank_pair_orbits_count': len(all_high),
        'all_high_rank_raised_to_19': sorted(raised_all_high),
        'all_high_all_raised': sorted(all_high) == sorted(raised_all_high),
        'coset_compatible_exactly_one_rank1_orbits_not_load_bearing_for_coset_failure': sorted(one_rank_one_two_high),
        'orbits_with_at_most_one_high_rank_cannot_host_high_pair': sorted(two_or_more_rank_one),
        'orbit479_record': by_idx.get(479),
        'rank_patterns_484_491': {str(i): by_idx[i]['rank_pattern'] for i in range(484, 492) if i in by_idx},
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=DEFAULT_LUT)
    ap.add_argument('--binary', type=Path, default=DEFAULT_BIN20)
    ap.add_argument('--dim2', type=Path, default=DEFAULT_DIM2)
    ap.add_argument('--length', type=int, default=20)
    ap.add_argument('--max-cap', type=int, default=19)
    ap.add_argument('--out', type=Path, default=DEFAULT_OUT)
    ap.add_argument('--skip-transpose', action='store_true')
    args = ap.parse_args()
    t0 = time.time()
    lut = load_lut(args.lut)
    result = {
        'schema': 'wang_semantics_combined_v1',
        'lut_path': str(args.lut), 'lut_sha256': sha256(args.lut), 'lut_entries': len(lut),
        'binary_path': str(args.binary), 'binary_sha256': sha256(args.binary),
        'binary_audit': audit_binary(lut, args.binary, args.length, args.max_cap),
        'dim2_loadbearing_audit': audit_dim2(args.dim2),
    }
    if not args.skip_transpose:
        result['transpose_audit'] = audit_transpose(lut)
    result['elapsed_sec'] = time.time() - t0
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'out': str(args.out),
        'binary_exact_match': result['binary_audit']['binary_exact_match'],
        'binary_sha256': result['binary_sha256'],
        'lut_sha256': result['lut_sha256'],
        'dim2_loadbearing': result['dim2_loadbearing_audit']['all_high_rank_pair_orbits_load_bearing'],
        'all_high_all_raised': result['dim2_loadbearing_audit']['all_high_all_raised'],
        'transpose_mismatch_count': None if args.skip_transpose else result['transpose_audit']['mismatch_count'],
        'elapsed_sec': result['elapsed_sec'],
    }, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
