#!/usr/bin/env python3
r"""analysis: E11 core rank-19 search with saturation filtering (corrected).

CRITICAL FIX: The contraction L(q) for an 8-bit functional q is the XOR
of core_T[e_j] for each basis bit j set in q, NOT the sum over the
affine hyperplane {a: <q,a>=1}.  The correct rank distribution for the
E11 core is {3: 33, 6: 150, 9: 72}, giving nontrivial contraction lower
bounds and saturation constraints.

A rank-19 core decomposition would give R_F2(T) <= 22 after adding the
removed rank-3 A-slice.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from pathlib import Path
from collections import Counter

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

from wang_capacity_lazy import (
    pack_basis, rref_basis, unpack_basis, subspace_points_from_basis
)
from core_capacity_from_wang_lut import CoreQuotient, load_lut


def build_core_tensor_f2(pivot: int = 1) -> np.ndarray:
    """Build the E11-restricted core tensor as (256, 9, 9) over F2."""
    core_q = CoreQuotient(pivot)
    full_T = np.zeros((512, 9, 9), dtype=np.int32)
    for i1 in range(3):
        for j1 in range(3):
            for k in range(3):
                a = 3 * i1 + j1
                b = 3 * j1 + k
                c = 3 * k + i1
                full_T[1 << a, b, c] = 1
    for a in range(1, 512):
        lb_bit = a & -a
        rest = a ^ lb_bit
        full_T[a] = (full_T[lb_bit] + full_T[rest]) % 2
    core_T = np.zeros((256, 9, 9), dtype=np.int32)
    for q8 in range(256):
        core_T[q8] = full_T[core_q.lift8(q8)]
    return core_T


def correct_contraction(core_T: np.ndarray, q: int) -> np.ndarray:
    """Contraction L(q) = XOR_{j: bit j set in q} core_T[e_j].
    This is the correct linear contraction over F2."""
    L = np.zeros((9, 9), dtype=np.int32)
    for j in range(8):
        if (q >> j) & 1:
            L = (L + core_T[1 << j]) % 2
    return L


def gf2_rank_mat(M: np.ndarray) -> int:
    rows = [int(sum(int(M[r, c]) << c for c in range(9))) for r in range(9)]
    rank = 0
    for r in range(9):
        if rows[r] == 0:
            continue
        p = (rows[r] & -rows[r]).bit_length() - 1
        rank += 1
        for r2 in range(9):
            if r2 != r and (rows[r2] >> p) & 1:
                rows[r2] ^= rows[r]
    return rank


def rref_basis_9(rows_set):
    basis = [0] * 9
    for row in rows_set:
        if not row:
            continue
        v = row & 0x1FF
        while v:
            p = v.bit_length() - 1
            if basis[p]:
                v ^= basis[p]
            else:
                basis[p] = v
                break
    for p in range(9):
        if basis[p]:
            for qq in range(9):
                if qq != p and basis[qq] and (basis[qq] >> p) & 1:
                    basis[qq] ^= basis[p]
    return [b for b in basis if b]


def span_set(basis):
    s = {0}
    for b in basis:
        s = s | {v ^ b for v in s}
    return s


def intersect_spans(spaces):
    if not spaces:
        return [1 << i for i in range(9)]
    current = span_set(spaces[0])
    for sp in spaces[1:]:
        current = current & span_set(sp)
    return rref_basis_9(current)


def compute_core_saturation(core_T, support, c_ranks):
    """Compute saturated-contraction domains for each term in support."""
    # For each contraction q (8-bit), compute weight and saturation
    sat_info = []
    for q in range(1, 256):
        rk = c_ranks[q]
        if rk == 0:
            continue
        # Weight: number of support elements a with L(q) involving a
        # For the LINEAR contraction L(q) = XOR of basis slices,
        # the "participating terms" are those s where a_s has a component
        # in the support of q. That is, q(a_s) = popcount(q & a_s) mod 2 = 1.
        # Wait - this is the evaluation of the linear functional q at the
        # projected point a_s. For the decomposition T_core = sum_s a_s ⊗ b_s ⊗ c_s,
        # L(q) = sum_{s: q(a_s)=1} b_s c_s^T. So I_q = {s: q(a_s)=1}.
        I_q = [i for i, a in enumerate(support) if bin(q & a).count('1') % 2 == 1]
        w = len(I_q)
        if w < rk:
            # Undersaturated: violation of contraction lower bound
            sat_info.append({'q': q, 'rank': rk, 'weight': w, 'terms': I_q,
                             'type': 'undersaturated'})
        elif w == rk:
            # Saturated: extract column and row spaces
            L = correct_contraction(core_T, q)
            col_vecs = set()
            row_vecs = set()
            for c in range(9):
                v = 0
                for r in range(9):
                    if L[r, c]:
                        v |= 1 << r
                col_vecs.add(v)
            for r in range(9):
                v = 0
                for c in range(9):
                    if L[r, c]:
                        v |= 1 << c
                row_vecs.add(v)
            col_basis = rref_basis_9(col_vecs)
            row_basis = rref_basis_9(row_vecs)
            sat_info.append({'q': q, 'rank': rk, 'weight': w, 'terms': I_q,
                             'col_basis': col_basis, 'row_basis': row_basis,
                             'type': 'saturated'})

    # Build per-term domains
    undersat_count = sum(1 for s in sat_info if s['type'] == 'undersaturated')
    sat_count = sum(1 for s in sat_info if s['type'] == 'saturated')

    term_domains = []
    for i, a in enumerate(support):
        B_spaces = []
        C_spaces = []
        n_sat = 0
        for si in sat_info:
            if si['type'] == 'saturated' and i in si['terms']:
                B_spaces.append(si['col_basis'])
                C_spaces.append(si['row_basis'])
                n_sat += 1
        B_basis = intersect_spans(B_spaces) if B_spaces else [1 << j for j in range(9)]
        C_basis = intersect_spans(C_spaces) if C_spaces else [1 << j for j in range(9)]
        B_dim = len(B_basis)
        C_dim = len(C_basis)
        term_domains.append({'term': i, 'a': a, 'B_dim': B_dim, 'C_dim': C_dim,
                             'sat_contractions': n_sat})

    zero_terms = [t for t in term_domains if t['B_dim'] == 0 or t['C_dim'] == 0]
    domain_hist = Counter(f"B{t['B_dim']}_C{t['C_dim']}" for t in term_domains)

    return {
        'term_domains': term_domains,
        'saturated_count': sat_count,
        'undersaturated_count': undersat_count,
        'zero_domain_terms': zero_terms,
        'domain_hist': dict(domain_hist),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', default='data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--rank', type=int, default=19)
    ap.add_argument('--max-rounds', type=int, default=20)
    ap.add_argument('--solver-time', type=float, default=120.0)
    ap.add_argument('--out', type=Path, default=Path('data/dual_ruling/core_e11_saturation_v2.json'))
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

    pivot = 1
    core = CoreQuotient(pivot)
    s = args.rank

    print('Building E11 core tensor...')
    core_T = build_core_tensor_f2(pivot)

    print('Computing core contraction ranks (correct method)...')
    c_ranks = {}
    for q in range(1, 256):
        L = correct_contraction(core_T, q)
        c_ranks[q] = gf2_rank_mat(L)
    rank_dist = Counter(c_ranks.values())
    print(f'  rank distribution: {dict(sorted(rank_dist.items()))}')

    print('Loading LUT...')
    t0 = time.time()
    lut, meta = load_lut(Path(args.lut))
    lut = {int(k): int(v) for k, v in lut.items()}
    print(f'  lut={len(lut):,} load_sec={time.time()-t0:.1f}')

    from ortools.sat.python import cp_model
    model = cp_model.CpModel()
    points = list(range(1, 256))
    x = {p: model.NewBoolVar(f'x_{p}') for p in points}
    model.Add(sum(x[p] for p in points) == s)

    # Wang upper constraints: dim-1 and dim-2
    wang_added = set()
    for q8 in points:
        key8 = core.key8_from_rows([q8])
        if key8 not in wang_added:
            key9 = core.key9_from_key8(key8)
            if key9 in lut:
                lb = lut[key9]
                cap = s - lb
                if cap >= 0:
                    model.Add(x[q8] <= cap)
                    wang_added.add(key8)

    for q1 in points:
        for q2 in range(q1 + 1, 256):
            q3 = q1 ^ q2
            if q3 == 0 or q3 > q2:
                continue
            key8 = core.key8_from_rows([q1, q2])
            if key8 in wang_added:
                continue
            key9 = core.key9_from_key8(key8)
            if key9 not in lut:
                continue
            lb = lut[key9]
            cap = s - lb
            if cap >= 0:
                model.Add(sum(x[p] for p in [q1, q2, q3]) <= cap)
                wang_added.add(key8)

    # CORRECT contraction lower bounds
    lower_count = 0
    for q in range(1, 256):
        rk = c_ranks[q]
        if rk <= 0:
            continue
        ci = [p for p in points if bin(q & p).count('1') % 2 == 1]
        if len(ci) >= rk:
            model.Add(sum(x[p] for p in ci) >= rk)
            lower_count += 1
    print(f'  wang_dim1+dim2={len(wang_added)}  contraction_lower={lower_count}')

    # Iterative search
    rounds = []
    final_status = None
    excluded_supports = 0

    for rnd in range(args.max_rounds):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = args.solver_time
        solver.parameters.num_workers = 8
        solver.parameters.random_seed = 1900 + rnd * 13
        tsolve = time.time()
        status = solver.Solve(model)
        solve_sec = time.time() - tsolve
        status_name = {
            cp_model.OPTIMAL: 'OPTIMAL', cp_model.FEASIBLE: 'FEASIBLE',
            cp_model.INFEASIBLE: 'INFEASIBLE', cp_model.UNKNOWN: 'UNKNOWN',
        }.get(status, str(status))
        print(f'\nRound {rnd}: status={status_name} solve_sec={solve_sec:.1f} wang={len(wang_added)}')

        rec = {'round': rnd, 'status': status_name, 'solve_sec': round(solve_sec, 2),
               'wang_count': len(wang_added)}

        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            rounds.append(rec)
            final_status = status_name
            break

        support = sorted(p for p in points if solver.Value(x[p]))
        rec['support'] = support

        # Check Wang violations by enumerating generated subspaces (up to dim 5)
        violations = []
        checked = set()
        for mask in range(1, 1 << len(support)):
            if bin(mask).count('1') > 5:
                continue
            pts_in = [support[j] for j in range(len(support)) if (mask >> j) & 1]
            key8 = core.key8_from_rows(pts_in)
            if key8 in checked:
                continue
            checked.add(key8)
            key9 = core.key9_from_key8(key8)
            if key9 not in lut:
                continue
            lb = lut[key9]
            cap = s - lb
            span_pts = subspace_points_from_basis(unpack_basis(key8))
            occ = sum(1 for p in span_pts if p in set(support))
            if occ > cap:
                violations.append({'key8': key8, 'key9': key9, 'lb': lb, 'cap': cap,
                                   'occ': occ, 'excess': occ - cap, 'dim': key8 & 0xF})
        rec['wang_violations'] = len(violations)

        # Saturation analysis
        sat = compute_core_saturation(core_T, support, c_ranks)
        rec['saturation'] = {
            'saturated': sat['saturated_count'],
            'undersaturated': sat['undersaturated_count'],
            'zero_domains': len(sat['zero_domain_terms']),
            'domain_hist': sat['domain_hist'],
        }

        if len(violations) == 0 and len(sat['zero_domain_terms']) == 0 and sat['undersaturated_count'] == 0:
            rec['candidate_status'] = 'CANDIDATE_PASS'
            rounds.append(rec)
            final_status = 'CANDIDATE_FOUND'
            print(f'  *** CANDIDATE rank-19 core A-support! ***')
            print(f'  support: {support}')
            break

        # Add Wang violations
        added = 0
        for v in sorted(violations, key=lambda v: (-v['excess'], -v['lb'])):
            key8 = v['key8']
            if key8 in wang_added:
                continue
            key9 = v['key9']
            lb = lut[key9]
            cap = s - lb
            span_pts = subspace_points_from_basis(unpack_basis(key8))
            sel = [p for p in span_pts if p in set(points)]
            model.Add(sum(x[p] for p in sel) <= cap)
            wang_added.add(key8)
            added += 1
        rec['added_wang'] = added

        # If zero-domain or undersaturated, exclude this exact support
        if sat['zero_domain_terms'] or sat['undersaturated_count'] > 0:
            model.AddBoolOr([x[p].Not() for p in support])
            excluded_supports += 1
            rec['excluded_support'] = True

        print(f'  wang_viol={len(violations)} undersat={sat["undersaturated_count"]} zero_dom={len(sat["zero_domain_terms"])} added={added} hist={sat["domain_hist"]}')
        rounds.append(rec)
        final_status = status_name

    result = {
        'schema': 'core_e11_saturation_v2',
        'core': 'E11',
        'pivot': pivot,
        'target_rank': s,
        'contraction_rank_dist': dict(sorted(rank_dist.items())),
        'contraction_lower_count': lower_count,
        'final_wang_constraints': len(wang_added),
        'excluded_supports': excluded_supports,
        'final_status': final_status,
        'total_rounds': len(rounds),
        'rounds': rounds,
        'total_elapsed_sec': round(time.time() - t0, 2),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'\nSaved to {args.out}')
    print(json.dumps({'final_status': final_status, 'rounds': len(rounds)}, sort_keys=True))


if __name__ == '__main__':
    main()
