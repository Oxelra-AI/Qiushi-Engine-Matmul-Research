#!/usr/bin/env python3
"""analysis transport witnesses for the shortened rank>=21 proof package.

The analysis file-chain checker proved that core rows, CNF files and DRAT files
match the row generator.  This script adds a more mathematical layer: for each
used occupation row it exposes

  * the quotient subspace S in the 7-dimensional quotient,
  * the full A-kernel U = W + lift(S),
  * the Wang certificate orbit/node supplying LB(U), and
  * an explicit GL(3,2)xGL(3,2) (optionally transpose) A-side transport that
    maps the certificate representative kernel to U.

The same witness mechanism is also used for the 511 line bounds and the 651+651
normalized affine-plane bounds.  The output is a witness file for later proof
review; it is not a new lower-bound algorithm.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

S04 = Path('scripts')
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
import wang_capacity_lazy as wc  # type: ignore

SCRIPTS = Path('scripts')
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import dim2_replay_compat_graph as dg  # type: ignore

PROFILE = Path('data/wang_f2_lb20/cert_profile.json')
LUT_PATH = Path('data/wang_f2_lb20/wang_subspace_lut.pkl')
CACHE_PATH = Path('data/wang_f2_lb20/wang_orbit_closed_cache.pkl')
CORE_ROOT = Path('data/dim2_caplimited_cores_484_491')
OUT = Path('data/transport_witnesses/transport_witness_layer.json')
JSONL = Path('data/transport_witnesses/dim2_core_row_witnesses.jsonl')


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def rows_to_mask(rows: Sequence[int]) -> int:
    m = 0
    for i, row in enumerate(rows):
        for j in range(3):
            if (int(row) >> j) & 1:
                m |= 1 << (3 * i + j)
    return m


def make_actions_with_witnesses():
    gl = wc.generate_gl3()
    out = []
    aid = 0
    for L in gl:
        for R in gl:
            for tr in (False, True):
                img = wc.basis_image_for_action(L, R, tr)
                out.append({
                    'action_id': aid,
                    'transpose_branch': bool(tr),
                    'left_rows': [int(x) for x in L],
                    'right_rows': [int(x) for x in R],
                    'left_mask': rows_to_mask(L),
                    'right_mask': rows_to_mask(R),
                    'basis_image': [int(x) for x in img],
                })
                aid += 1
    # The construction should not duplicate A-side actions.
    assert len({tuple(a['basis_image']) for a in out}) == 2 * 168 * 168
    return out


def transform_basis_key(basis: Sequence[int], img: Sequence[int]) -> int:
    return wc.transform_key(tuple(int(x) for x in basis), tuple(int(y) for y in img))


class TransportFinder:
    def __init__(self, cache):
        self.cache = cache
        self.actions = make_actions_with_witnesses()
        self.need_by_orbit: Dict[int, set[int]] = defaultdict(set)
        self.witness_by_key: Dict[int, Dict] = {}
        self.missing_by_orbit: Dict[int, List[int]] = {}

    def add_need(self, key: int) -> None:
        pos = int(self.cache['key_to_orbit'][int(key)])
        self.need_by_orbit[pos].add(int(key))

    def solve(self) -> None:
        for pos, need0 in sorted(self.need_by_orbit.items()):
            need = set(need0)
            rep = [int(x) for x in self.cache['orbits'][pos]['basis']]
            for a in self.actions:
                key = transform_basis_key(rep, a['basis_image'])
                if key in need and key not in self.witness_by_key:
                    self.witness_by_key[key] = {
                        'orbit_pos': pos,
                        'cert_index': int(self.cache['orbits'][pos].get('cert_index', pos)),
                        'cert_basis': rep,
                        'action_id': int(a['action_id']),
                        'transpose_branch': bool(a['transpose_branch']),
                        'left_mask': int(a['left_mask']),
                        'right_mask': int(a['right_mask']),
                        'left_rows': a['left_rows'],
                        'right_rows': a['right_rows'],
                    }
                    need.remove(key)
                    if not need:
                        break
            if need:
                self.missing_by_orbit[pos] = sorted(need)[:20]


def qbasis_from_mask(mask: int, k: int) -> Tuple[int, ...]:
    return wc.rref_basis([q + 1 for q in range((1 << k) - 1) if (int(mask) >> q) & 1], n=k)


def free_bits(W: Sequence[int], nbits: int = 9) -> List[int]:
    piv = {int(rb).bit_length() - 1 for rb in W if int(rb)}
    return [i for i in range(nbits) if i not in piv]


def lift_q(q: int, fb: Sequence[int]) -> int:
    v = 0
    for i, bit in enumerate(fb):
        if (int(q) >> i) & 1:
            v |= 1 << bit
    return v


def full_U_key_from_W_mask(W: Sequence[int], mask: int, k: int) -> Tuple[int, Tuple[int, ...], Tuple[int, ...]]:
    Wr = wc.rref_basis(W, n=9); fb = free_bits(Wr, 9)
    qb = qbasis_from_mask(mask, k)
    lifts = [lift_q(q, fb) for q in qb]
    Ub = wc.rref_basis(list(Wr) + lifts, n=9)
    return wc.pack_basis(Ub), qb, Ub


def nonzero_span(basis: Sequence[int]) -> List[int]:
    out = []
    for m in range(1, 1 << len(basis)):
        v = 0
        for i, b in enumerate(basis):
            if (m >> i) & 1:
                v ^= int(b)
        out.append(v)
    return sorted(out)


def transpose_mask(x: int) -> int:
    z = 0
    for i in range(3):
        for j in range(3):
            if (int(x) >> (3 * i + j)) & 1:
                z |= 1 << (3 * j + i)
    return z


def affine_planes_ag3():
    planes = set()
    for base in range(8):
        for u, v in combinations(range(1, 8), 2):
            P = tuple(sorted({base, base ^ u, base ^ v, base ^ u ^ v}))
            if len(P) == 4:
                planes.add(P)
    return sorted(planes)


def plane_count(S: Sequence[int]) -> int:
    ss = set(S)
    return sum(1 for P in affine_planes_ag3() if set(P).issubset(ss))


def firstrow(x: int) -> int:
    return x & 7


def firstcol_bits(x: int) -> int:
    return ((x >> 0) & 1) | (((x >> 3) & 1) << 1) | (((x >> 6) & 1) << 2)


def collect_line_keys(cache) -> List[Dict]:
    recs = []
    for a in range(1, 512):
        key = wc.pack_basis(wc.rref_basis([a], n=9)); pos = int(cache['key_to_orbit'][key])
        recs.append({'a': a, 'rank': wc.matrix_rank_of_mask(a), 'key': key, 'orbit_pos': pos, 'lb': int(cache['orbits'][pos]['raw_lb'])})
    return recs


def collect_dim2_core_rows(lut, cache) -> Tuple[List[Dict], Dict]:
    prof = json.loads(PROFILE.read_text()); byidx = {int(r['index']): r for r in prof['dimension_2_orbits']}
    records = []
    summary = {'by_orbit': {}, 'total_rows': 0}
    for idx in range(484, 492):
        core_path = sorted((CORE_ROOT / f'orbit{idx}').glob(f'orbit{idx}_cap*_core.json'))[0]
        core = json.loads(core_path.read_text())
        W = [int(x) for x in core['basis']]
        k = int(core['quotient_dim']); L = int(core['old_lb'])
        assert W == [int(x) for x in byidx[idx]['constraint_values']] or wc.rref_basis(W, 9) == wc.rref_basis(byidx[idx]['constraint_values'], 9)
        row_recs = []
        for rno, r in enumerate(core['shrunk_rows']):
            mask = int(r['mask']); cap = int(r['cap'])
            key, qb, Ub = full_U_key_from_W_mask(W, mask, k)
            pos = int(cache['key_to_orbit'][key])
            lb = int(lut[key])
            if L - lb != cap:
                raise RuntimeError(f'cap mismatch orbit {idx} row {rno}: cap={cap} L-lb={L-lb} U={Ub}')
            row_recs.append({'outer_orbit': idx, 'row_index': rno, 'mask': mask, 'cap': cap, 'quotient_basis': list(qb), 'U_key': key, 'U_basis': list(Ub), 'U_dim': len(Ub), 'source_orbit_pos': pos, 'source_cert_index': int(cache['orbits'][pos].get('cert_index', pos)), 'source_lb': lb, 'source_proof_type': cache['orbits'][pos].get('proof_type')})
        records.extend(row_recs)
        summary['by_orbit'][str(idx)] = {'core_path': str(core_path), 'rows': len(row_recs), 'outer_basis': W, 'old_lb': L, 'cap_limit': core.get('cap_limit'), 'source_orbit_hist': {str(k0): int(v) for k0, v in sorted(Counter(rr['source_orbit_pos'] for rr in row_recs).items())}}
        summary['total_rows'] += len(row_recs)
    return records, summary


def collect_affine_plane_keys(lut, cache) -> Tuple[List[Dict], Dict]:
    recs = []
    # Column model: varying first row, fixed lower two rows.
    for lower in range(1, 64):
        p = lower << 3
        coset = [p | r for r in range(8)]
        highpts = [x for x in coset if wc.matrix_rank_of_mask(x) >= 2]
        for quad in combinations(highpts, 4):
            rb = wc.rref_basis(quad, n=9)
            if len(rb) != 3:
                continue
            key = wc.pack_basis(rb); pos = int(cache['key_to_orbit'][key]); lb = int(lut[key])
            recs.append({'model': 'column', 'quad': list(quad), 'firstrows': [firstrow(x) for x in quad], 'U_key': key, 'U_basis': list(rb), 'orbit_pos': pos, 'cert_index': int(cache['orbits'][pos].get('cert_index', pos)), 'lb': lb, 'proof_type': cache['orbits'][pos].get('proof_type')})
    # Row model: varying first column, fixed right two columns.
    for fixed in range(1, 64):
        p = 0
        for i in range(3):
            for jj in range(2):
                if (fixed >> (2 * i + jj)) & 1:
                    p |= 1 << (3 * i + (jj + 1))
        coset = []
        for col in range(8):
            x = p
            for i in range(3):
                if (col >> i) & 1:
                    x |= 1 << (3 * i)
            coset.append(x)
        highpts = [x for x in coset if wc.matrix_rank_of_mask(x) >= 2]
        for quad in combinations(highpts, 4):
            rb = wc.rref_basis(quad, n=9)
            if len(rb) != 3:
                continue
            key = wc.pack_basis(rb); pos = int(cache['key_to_orbit'][key]); lb = int(lut[key])
            recs.append({'model': 'row', 'quad': list(quad), 'firstcols': [firstcol_bits(x) for x in quad], 'U_key': key, 'U_basis': list(rb), 'orbit_pos': pos, 'cert_index': int(cache['orbits'][pos].get('cert_index', pos)), 'lb': lb, 'proof_type': cache['orbits'][pos].get('proof_type')})
    summary = {'total': len(recs), 'by_model': {str(k): int(v) for k, v in sorted(Counter(r['model'] for r in recs).items())}, 'lb_hist': {str(k): int(v) for k, v in sorted(Counter(r['lb'] for r in recs).items())}, 'orbit_hist': {str(k): int(v) for k, v in sorted(Counter(r['orbit_pos'] for r in recs).items())}}
    return recs, summary


def collect_highrank_pair_classification(cache) -> Dict:
    high = [a for a in range(1, 512) if wc.matrix_rank_of_mask(a) >= 2]
    hist = Counter(); bad_not_forbidden = []; forbidden_bad = Counter(); rankone_allowed = Counter()
    forbidden = set(range(484, 492))
    for a, b in combinations(high, 2):
        key = wc.pack_basis(wc.rref_basis([a, b], n=9)); pos = int(cache['key_to_orbit'][key]); hist[pos] += 1
        rsum = wc.matrix_rank_of_mask(a ^ b)
        if rsum != 1 and pos not in forbidden:
            if len(bad_not_forbidden) < 20:
                bad_not_forbidden.append({'a': a, 'b': b, 'orbit': pos, 'ranks': [wc.matrix_rank_of_mask(a), wc.matrix_rank_of_mask(b), rsum]})
        if pos in forbidden and rsum != 1:
            forbidden_bad[pos] += 1
        if pos not in forbidden and rsum == 1:
            rankone_allowed[pos] += 1
    return {'high_rank_vertex_count': len(high), 'pair_orbit_hist': {str(k): int(v) for k, v in sorted(hist.items())}, 'forbidden_orbits': sorted(forbidden), 'bad_not_forbidden_sum_not_rankone_count': len(bad_not_forbidden), 'bad_not_forbidden_head': bad_not_forbidden, 'forbidden_non_rankone_sum_hist': {str(k): int(v) for k, v in sorted(forbidden_bad.items())}, 'allowed_rankone_sum_hist': {str(k): int(v) for k, v in sorted(rankone_allowed.items())}}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', type=Path, default=OUT)
    ap.add_argument('--jsonl', type=Path, default=JSONL)
    args = ap.parse_args(); args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    lut_obj = pickle.load(open(LUT_PATH, 'rb'))
    lut = {int(k): int(v) for k, v in (lut_obj['lut'] if isinstance(lut_obj, dict) and 'lut' in lut_obj else lut_obj).items()}
    cache = pickle.load(open(CACHE_PATH, 'rb'))
    dim2_rows, dim2_summary = collect_dim2_core_rows(lut, cache)
    line_rows = collect_line_keys(cache)
    plane_rows, plane_summary = collect_affine_plane_keys(lut, cache)
    finder = TransportFinder(cache)
    for r in dim2_rows:
        finder.add_need(r['U_key'])
    for r in line_rows:
        finder.add_need(r['key'])
    for r in plane_rows:
        finder.add_need(r['U_key'])
    finder.solve()
    # Attach row witnesses to the JSONL stream.  Keep the main JSON compact.
    args.jsonl.parent.mkdir(parents=True, exist_ok=True)
    missing_core = 0
    with args.jsonl.open('wt') as f:
        for r in dim2_rows:
            w = finder.witness_by_key.get(r['U_key'])
            if w is None:
                missing_core += 1
            rec = dict(r); rec['transport_witness'] = w
            f.write(json.dumps(rec, sort_keys=True) + '\n')
    line_missing = sum(1 for r in line_rows if r['key'] not in finder.witness_by_key)
    plane_missing = sum(1 for r in plane_rows if r['U_key'] not in finder.witness_by_key)
    line_summary = {'total': len(line_rows), 'lb_hist': {str(k): int(v) for k, v in sorted(Counter(r['lb'] for r in line_rows).items())}, 'rank_orbit_lb_hist': {str(k): int(v) for k, v in sorted(Counter((r['rank'], r['orbit_pos'], r['lb']) for r in line_rows).items())}, 'missing_transport_witnesses': line_missing, 'examples': [{**{kk: vv for kk, vv in r.items() if kk != 'key'}, 'transport_witness': finder.witness_by_key.get(r['key'])} for r in line_rows[:12]]}
    out = {
        'schema': 's0908_transport_witness_layer_v1',
        'meaning': 'Witness layer connecting the proof-used occupation rows and finite premises to explicit Wang certificate nodes and GL(3,2)xGL(3,2) or transpose transports. Core row details are in the JSONL file.',
        'source_files': {'profile': str(PROFILE), 'lut': str(LUT_PATH), 'cache': str(CACHE_PATH), 'core_root': str(CORE_ROOT)},
        'source_hashes': {'profile': sha256(PROFILE), 'lut': sha256(LUT_PATH), 'cache': sha256(CACHE_PATH)},
        'action_count': len(finder.actions),
        'needed_orbit_count': len(finder.need_by_orbit),
        'needed_key_count': sum(len(v) for v in finder.need_by_orbit.values()),
        'witnessed_key_count': len(finder.witness_by_key),
        'missing_by_orbit_head': {str(k): v for k, v in list(sorted(finder.missing_by_orbit.items()))[:20]},
        'all_needed_transports_found': not finder.missing_by_orbit,
        'dim2_core_rows': {**dim2_summary, 'jsonl_path': str(args.jsonl), 'jsonl_sha256': sha256(args.jsonl), 'missing_transport_witnesses': missing_core, 'U_dim_hist': {str(k): int(v) for k, v in sorted(Counter(r['U_dim'] for r in dim2_rows).items())}, 'source_lb_hist': {str(k): int(v) for k, v in sorted(Counter(r['source_lb'] for r in dim2_rows).items())}, 'source_proof_type_hist': {str(k): int(v) for k, v in sorted(Counter(r['source_proof_type'] for r in dim2_rows).items())}},
        'line_LB19_witnesses': line_summary,
        'affine_plane_LB17_witnesses': {**plane_summary, 'missing_transport_witnesses': plane_missing, 'examples': [{**r, 'transport_witness': finder.witness_by_key.get(r['U_key'])} for r in plane_rows[:12]]},
        'highrank_pair_classification': collect_highrank_pair_classification(cache),
        'AG32_every_five_has_plane': all(plane_count(S) > 0 for k in range(5, 9) for S in combinations(range(8), k)),
        'transport_formula': {
            'nontranspose_A_action': 'A -> L^{-T} A R^{-T}; one companion tensor automorphism is B -> R^T B and C -> L C',
            'transpose_A_action': 'A -> R^{-1} A^T L^{-1}; one companion tensor automorphism is B -> L C and C -> R^T B after the A-transpose/B-C-swap symmetry',
            'note': 'These are the same A-side transformations used to expand Wang certificate orbits in wang_capacity_lazy.basis_image_for_action.'
        },
        'elapsed_sec': time.time() - t0,
    }
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'ok', 'out': str(args.out), 'jsonl': str(args.jsonl), 'all_needed_transports_found': out['all_needed_transports_found'], 'dim2_rows': dim2_summary['total_rows'], 'line_missing': line_missing, 'plane_missing': plane_missing, 'elapsed_sec': out['elapsed_sec']}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
