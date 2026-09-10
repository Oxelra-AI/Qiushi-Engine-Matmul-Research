#!/usr/bin/env python3
"""S-free tight row/column-space scan for E11 four-dimensional V-orbits.

This tests how far the analysis tight contraction mechanism survives after
removing the sampled quotient CPD and retaining only V and the quotient slice
space S0 = span(Q_V slices).  It deliberately does NOT prove anything about all
larger quotient-generated S spaces; it is a fast structural probe of the bare
slice-space version of the mechanism across the 620 V-orbits.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

import numpy as np
from scipy.optimize import LinearConstraint, Bounds, milp

SCRIPTS = Path('scripts')
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import e11_s_coset_rank_sat as sc  # noqa: E402
import e11_s_tight_space_obstruction as tso  # noqa: E402

INC = np.zeros((15, 15), dtype=float)
for phi in range(1, 16):
    for v in range(1, 16):
        INC[phi - 1, v - 1] = 1.0 if ((phi & v).bit_count() & 1) else 0.0


def matrix_mask_from_np(M: np.ndarray) -> int:
    out = 0
    for b in range(9):
        row = 0
        for c in range(9):
            if int(M[b, c]) & 1:
                row |= 1 << c
        out |= row << (9 * b)
    return out


def gf2_basis_81(vecs: Iterable[int]) -> Tuple[int, ...]:
    return sc.rref_basis([int(v) for v in vecs])


def s0_basis_from_Q(Q: np.ndarray) -> Tuple[int, ...]:
    return gf2_basis_81(matrix_mask_from_np(Q[i]) for i in range(Q.shape[0]))


def build_Rphi_masks(Rcoords: np.ndarray) -> Dict[int, int]:
    Rphi = {}
    for phi in range(1, 16):
        M = np.zeros((9, 9), dtype=np.uint8)
        for k in range(4):
            if (phi >> k) & 1:
                M ^= Rcoords[k]
        Rphi[phi] = matrix_mask_from_np(M)
    return Rphi


def mininfo_for_S0(S0: Tuple[int, ...], Rphi: Dict[int, int]):
    m = {}
    info = {}
    for phi in range(1, 16):
        best, mins = tso.min_matrices(Rphi[phi], S0)
        m[phi] = int(best)
        b_union = set()
        c_union = set()
        for mat in mins:
            rows = sc.rows_from_mask81(mat)
            cb = tso.row_basis_mask(tso.col_rows_from_rows(rows))
            rb = tso.row_basis_mask(rows)
            b_union |= (tso.span_set(cb) - {0})
            c_union |= (tso.span_set(rb) - {0})
        info[phi] = {
            'm': int(best),
            'min_count': int(len(mins)),
            'b_union': b_union,
            'c_union': c_union,
            'b_union_count': int(len(b_union)),
            'c_union_count': int(len(c_union)),
        }
    return m, info


def exact_cover_minimum(m_tuple: Tuple[int, ...]) -> int | None:
    """Small integer covering optimum over nonzero vectors of F2^4."""
    m = np.array(m_tuple, dtype=float)
    lc = LinearConstraint(INC, lb=m, ub=np.full(15, np.inf))
    res = milp(c=np.ones(15), integrality=np.ones(15), bounds=Bounds(np.zeros(15), np.full(15, 19)), constraints=lc,
               options={'time_limit': 10.0, 'mip_rel_gap': 0.0})
    if not res.success:
        return None
    return int(round(float(res.fun)))


def cover_block_record(cover: Tuple[int, ...], m: Dict[int, int], mininfo) -> dict:
    cov = {phi: sum(1 for a in cover if ((phi & a).bit_count() & 1)) for phi in range(1, 16)}
    tight = [phi for phi in range(1, 16) if cov[phi] == m[phi]]
    empty_terms = []
    for ti, a in enumerate(cover):
        phis = [phi for phi in tight if ((phi & a).bit_count() & 1)]
        allowed_b = set(range(1, 512))
        allowed_c = set(range(1, 512))
        for phi in phis:
            allowed_b &= mininfo[phi]['b_union']
            allowed_c &= mininfo[phi]['c_union']
        if (not allowed_b) or (not allowed_c):
            empty_terms.append({
                'term': int(ti),
                'a': int(a),
                'tight_phis': [int(x) for x in phis],
                'allowed_b_count': int(len(allowed_b)),
                'allowed_c_count': int(len(allowed_c)),
            })
    return {
        'tight_phis': [int(x) for x in tight],
        'blocked': bool(empty_terms),
        'empty_terms_head': empty_terms[:5],
    }


def iter_exact_covers(m_tuple: Tuple[int, ...], s: int, cap: int = 0):
    """Generate nondecreasing covers of exact size s satisfying INC*n >= m."""
    m = list(map(int, m_tuple))
    cov = [0] * 15
    cur: List[int] = []
    yielded = 0

    # Precompute incidence columns as 0/1 lists.
    cols = [[int(INC[phi - 1, v - 1]) for phi in range(1, 16)] for v in range(1, 16)]

    def rec(start_v: int, rem: int):
        nonlocal yielded
        if cap and yielded >= cap:
            return
        # Even if all remaining terms hit a row, this row cannot reach m.
        for i in range(15):
            if cov[i] + rem < m[i]:
                return
        if rem == 0:
            if all(cov[i] >= m[i] for i in range(15)):
                yielded += 1
                yield tuple(cur)
            return
        for v in range(start_v, 16):
            col = cols[v - 1]
            for i in range(15):
                cov[i] += col[i]
            cur.append(v)
            yield from rec(v, rem - 1)
            cur.pop()
            for i in range(15):
                cov[i] -= col[i]
            if cap and yielded >= cap:
                return

    yield from rec(1, s)


def analyze_prefix(prefix: List[int], flat_lb_hint: int | None, cover_cap: int = 0) -> dict:
    Q, ann, phis, Rcoords = sc.quotient_base_residual(prefix)
    S0 = s0_basis_from_Q(Q)
    Rphi = build_Rphi_masks(Rcoords)
    m, mininfo = mininfo_for_S0(S0, Rphi)
    mt = tuple(m[phi] for phi in range(1, 16))
    exact_s = exact_cover_minimum(mt)
    if exact_s is None:
        raise RuntimeError(f'cover MILP failed for prefix {prefix}')
    flat_A = len(S0)
    # Recompute the B/C flattening lower bounds of Q for a self-contained record.
    B_vecs = []
    for b in range(9):
        vv = 0
        for a in range(Q.shape[0]):
            for c in range(9):
                if int(Q[a, b, c]) & 1:
                    vv |= 1 << (Q.shape[0] * c + a)
        B_vecs.append(vv)
    C_vecs = []
    for c in range(9):
        vv = 0
        for a in range(Q.shape[0]):
            for b in range(9):
                if int(Q[a, b, c]) & 1:
                    vv |= 1 << (Q.shape[0] * b + a)
        C_vecs.append(vv)
    flat_B = sc.gf2_rank_int(B_vecs)
    flat_C = sc.gf2_rank_int(C_vecs)
    flat_lb = max(flat_A, flat_B, flat_C)
    q_allowed_by_cover = 19 - exact_s

    cover_count = 0
    blocked_count = 0
    first_survivors = []
    first_blocked = []
    tight_phi_counter = Counter()
    for cov in iter_exact_covers(mt, exact_s, cap=cover_cap):
        cover_count += 1
        br = cover_block_record(cov, m, mininfo)
        for phi in br['tight_phis']:
            tight_phi_counter[phi] += 1
        if br['blocked']:
            blocked_count += 1
            if len(first_blocked) < 3:
                first_blocked.append({'cover': list(cov), **br})
        else:
            if len(first_survivors) < 10:
                first_survivors.append({'cover': list(cov), **br})
    scan_truncated = bool(cover_cap and cover_count >= cover_cap)
    if cover_count == 0:
        status = 'NO_EXACT_COVER_GENERATED'
    elif blocked_count == cover_count and not scan_truncated:
        status = 'ALL_MIN_COVERS_BLOCKED_AT_S0'
    elif first_survivors:
        status = 'HAS_MIN_COVER_SURVIVING_AT_S0'
    else:
        status = 'TRUNCATED_NO_SURVIVOR_SEEN'
    return {
        'prefix': [int(x) for x in prefix],
        'annihilator_basis': [int(x) for x in ann],
        'phi_vectors': [int(x) for x in phis],
        'S0_dim': int(len(S0)),
        'S0_hash': sc.basis_hash(S0),
        'flat_lb': int(flat_lb),
        'flat_lb_hint': None if flat_lb_hint is None else int(flat_lb_hint),
        'flat_A': int(flat_A),
        'flat_B': int(flat_B),
        'flat_C': int(flat_C),
        'm_tuple': [int(x) for x in mt],
        'sum_m': int(sum(mt)),
        'exact_min_residual_s_for_S0_cover': int(exact_s),
        'q_allowed_max_by_S0_cover': int(q_allowed_by_cover),
        'q_lower_flattening': int(flat_lb),
        'q_window_nonempty_from_flattening_and_S0_cover': bool(flat_lb <= q_allowed_by_cover),
        'min_cover_count_scanned': int(cover_count),
        'min_cover_scan_truncated': scan_truncated,
        'space_blocked_min_cover_count': int(blocked_count),
        'surviving_min_cover_count': int(cover_count - blocked_count),
        'status': status,
        'first_surviving_min_covers': first_survivors,
        'first_blocked_min_covers': first_blocked,
        'tight_phi_frequency': {str(k): int(v) for k, v in sorted(tight_phi_counter.items())},
        'm_mininfo_counts': {str(phi): {'m': int(mininfo[phi]['m']), 'min_count': int(mininfo[phi]['min_count']), 'b_union_count': int(mininfo[phi]['b_union_count']), 'c_union_count': int(mininfo[phi]['c_union_count'])} for phi in range(1, 16)},
    }


def load_orbit_reps(path: Path):
    data = json.loads(path.read_text())
    if 'records' in data:
        return [{'orbit_id': r.get('orbit_id', i), 'basis': r['prefix'], 'flat_lb': r.get('flat_lb'), 'orbit_size': r.get('orbit_size', 0)} for i, r in enumerate(data['records'])]
    reps = data.get('high_Wang_cap_low_qnnz_head', data.get('low_qnnz_representatives_head', []))
    return reps


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--orbits', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--max-orbits', type=int, default=0)
    ap.add_argument('--cover-cap', type=int, default=0, help='0 means complete scan of minimum covers')
    args = ap.parse_args()
    t0 = time.time()
    reps = load_orbit_reps(args.orbits)
    if args.max_orbits:
        reps = reps[:args.max_orbits]
    records = []
    status_counts = Counter()
    exact_s_dist = Counter()
    q_window_dist = Counter()
    m_profile_dist = Counter()
    correction_examples = []
    for i, rep in enumerate(reps):
        rec = analyze_prefix([int(x) for x in rep['basis']], rep.get('flat_lb'), cover_cap=args.cover_cap)
        rec['orbit_id'] = int(rep.get('orbit_id', i))
        rec['orbit_size'] = int(rep.get('orbit_size', 0))
        records.append(rec)
        status_counts[rec['status']] += 1
        exact_s_dist[rec['exact_min_residual_s_for_S0_cover']] += 1
        q_window_dist[rec['q_allowed_max_by_S0_cover'] - rec['q_lower_flattening']] += 1
        m_profile_dist[tuple(rec['m_tuple'])] += 1
        # Record cases where analysis LP-derived best s would differ from exact cover optimum.
        if rec['sum_m'] == 45 and rec['exact_min_residual_s_for_S0_cover'] != 6 and len(correction_examples) < 8:
            correction_examples.append({'orbit_id': rec['orbit_id'], 'prefix': rec['prefix'], 'sum_m': rec['sum_m'], 'exact_s': rec['exact_min_residual_s_for_S0_cover']})
        if i < 10 or rec['status'] != 'ALL_MIN_COVERS_BLOCKED_AT_S0' or i % 100 == 0:
            print(f"{i}/{len(reps)} orbit={rec['orbit_id']} flat={rec['flat_lb']} sum_m={rec['sum_m']} "
                  f"exact_s={rec['exact_min_residual_s_for_S0_cover']} qwin={rec['q_allowed_max_by_S0_cover']-rec['q_lower_flattening']} "
                  f"covers={rec['min_cover_count_scanned']} blocked={rec['space_blocked_min_cover_count']} status={rec['status']}", flush=True)
    result = {
        'purpose': 'test the S-free bare quotient-slice version of the tight row/column-space mechanism across E11 four-dimensional V-orbits',
        'field': 'F2',
        'meaning': 'For each V, S0 is the quotient slice span. ALL_MIN_COVERS_BLOCKED_AT_S0 is only a bare S0 obstruction; larger quotient-generated S may lower m_phi or enlarge row/column allowances, so this file does not prove global E11 nonexistence.',
        'orbits_scanned': len(records),
        'status_counts': dict(status_counts),
        'exact_min_residual_s_distribution': {str(k): int(v) for k, v in sorted(exact_s_dist.items())},
        'q_window_gap_distribution': {str(k): int(v) for k, v in sorted(q_window_dist.items())},
        'distinct_m_profile_count': len(m_profile_dist),
        'm_profile_distribution_head': [{'m_tuple': list(k), 'count': int(v), 'sum_m': int(sum(k))} for k, v in m_profile_dist.most_common(20)],
        'lp_rounding_correction_examples': correction_examples,
        'elapsed_sec': time.time() - t0,
        'records': records,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True, default=int) + '\n')
    print(json.dumps({
        'orbits_scanned': result['orbits_scanned'],
        'status_counts': result['status_counts'],
        'exact_min_residual_s_distribution': result['exact_min_residual_s_distribution'],
        'q_window_gap_distribution': result['q_window_gap_distribution'],
        'distinct_m_profile_count': result['distinct_m_profile_count'],
        'lp_rounding_correction_examples': result['lp_rounding_correction_examples'],
        'elapsed_sec': result['elapsed_sec'],
    }, indent=2, sort_keys=True))
    print('wrote', args.out)


if __name__ == '__main__':
    main()
