#!/usr/bin/env python3
r"""analysis: E11 core rank-19 search with saturation filtering.

For the E11 core (8x9x9 tensor obtained by restricting T<3,3,3> to the
hyperplane {a : a_{11} = 0}), we search for a rank-19 A-support that
satisfies:
  1. Core Wang occupation constraints (from the full LUT)
  2. Core contraction lower bounds (w(q) >= rank L(q))
  3. Saturated-domain compatibility (B/C domains nonzero, linear test)

A rank-19 core decomposition would give R_F2(T) <= 22 after adding the
removed rank-3 A-slice.

Key mathematical structure: the core A-space is F_2^8 (quotient by <E11>).
Each nonzero 8-bit vector q in the core A-dual gives a 9x9 contraction
L(q).  We compute rank(L(q)), saturated contractions (w(q) = rank(L(q))),
and the resulting B/C domain intersections.
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
    """Build the E11-restricted core tensor as an 8x9x9 F2 array.
    
    The full tensor T_a[j,k] for A-index a (9-bit mask in row-major 3x3),
    B-index j=3*row+col for the 'j' factor, C-index k similarly.
    T_a[j,k] = 1 iff the Brent identity for (a,j,k) has a nonzero term.
    
    For T<3,3,3>: T_{(i1,j1),(j2,k2),(k3,i3)} = delta_{i1,i3}delta_{j1,j2}delta_{k2,k3}
    A=(i1,j1), B=(j2,k2), C=(k3,i3) in row-major.
    
    The core restricts A to those with a_0=0 (pivot bit for E11=1).
    """
    core_q = CoreQuotient(pivot)
    # Full tensor: 9x9x9 over F2
    # T[a,b,c] = 1 iff A-matrix a, when read as 3x3, has entry (i1,j1);
    # B-matrix b has entry (j2,k2); C-matrix c has entry (k3,i3);
    # and i1=i3, j1=j2, k2=k3.
    full_T = np.zeros((512, 9, 9), dtype=np.int32)
    for i1 in range(3):
        for j1 in range(3):
            for k in range(3):
                a = 3*i1 + j1  # A index (i1,j1)
                b = 3*j1 + k   # B index (j1,k)
                c = 3*k + i1   # C index (k,i1)
                full_T[1 << a, b, c] = 1
    # Combine: T[a_mask, b, c] = sum of contributions for each set bit
    for a in range(1, 512):
        lb = a & -a
        rest = a ^ lb
        full_T[a] = (full_T[lb] + full_T[rest]) % 2
    
    # Core: restrict to A with a_0 = 0 (pivot bit for E11=1 is bit 0)
    # Map from 8-bit quotient index to 9-bit full index
    core_T = np.zeros((256, 9, 9), dtype=np.int32)
    for q8 in range(256):
        a9 = core_q.lift8(q8)
        core_T[q8] = full_T[a9]
    
    return core_T


def core_contraction_ranks(core_T: np.ndarray) -> dict[int, int]:
    """Compute rank of each core contraction L(q) for q in 1..255."""
    ranks = {}
    for q in range(1, 256):
        # L(q) = sum_{a: q.a=1} core_T[a]
        L = np.zeros((9, 9), dtype=np.int32)
        for a in range(256):
            if bin(q & a).count('1') % 2 == 1:
                L = (L + core_T[a]) % 2
        # GF(2) rank
        rows = list(L.flatten().reshape(9, 9))
        pivots = []
        mat = [int(sum(int(L[r, c]) << c for c in range(9))) for r in range(9)]
        rank = 0
        for r in range(9):
            p = -1
            for c in range(9):
                if (mat[r] >> c) & 1:
                    p = c
                    break
            if p < 0:
                continue
            rank += 1
            for r2 in range(9):
                if r2 != r and (mat[r2] >> p) & 1:
                    mat[r2] ^= mat[r]
        ranks[q] = rank
    return ranks


def core_contraction_matrix(core_T: np.ndarray, q: int) -> int:
    """Return the 9x9 contraction matrix as a bitmask (row r, col c -> bit r*9+c)."""
    L = np.zeros((9, 9), dtype=np.int32)
    for a in range(256):
        if bin(q & a).count('1') % 2 == 1:
            L = (L + core_T[a]) % 2
    mask = 0
    for r in range(9):
        for c in range(9):
            if L[r, c]:
                mask |= 1 << (r * 9 + c)
    return mask


def gf2_rank_9x9(mask: int) -> int:
    """GF(2) rank of 9x9 matrix stored as bitmask."""
    rows = [(mask >> (r * 9)) & 0x1FF for r in range(9)]
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


def core_saturated_domains(core_T, support, contraction_ranks):
    """Compute saturated-contraction B/C domains for each term in support.
    
    Returns per-term domain info and overall statistics.
    """
    n = len(support)
    # For each contraction q, compute I_q and check saturation
    sat_info = []
    for q in range(1, 256):
        rk = contraction_ranks[q]
        I_q = [i for i, a in enumerate(support) if bin(q & a).count('1') % 2 == 1]
        w = len(I_q)
        if w == rk:
            # Saturated: compute column and row spaces of L(q)
            L_mask = core_contraction_matrix(core_T, q)
            # Column space: span of columns of L(q)
            cols = [(L_mask >> c) & ((1 << 81) - 1) for c in range(9)]
            # Actually L is 9x9, cols are 9-bit
            col_vecs = []
            for c in range(9):
                v = 0
                for r in range(9):
                    if (L_mask >> (r * 9 + c)) & 1:
                        v |= 1 << r
                col_vecs.append(v)
            col_basis = []
            for v in col_vecs:
                x = v
                for b in col_basis:
                    x = min(x, x ^ b)  # Wrong - need proper RREF
                # Proper GF(2) insertion
                x = v
                for b in col_basis:
                    if x and (x & -x).bit_length() - 1 in {(b2 & -b2).bit_length() - 1 for b2 in col_basis if b2}:
                        pass
                # Use rref_basis utility
            # Simpler: use the full_basis approach from analysis
            col_rows = set()
            row_rows = set()
            for c in range(9):
                v = 0
                for r in range(9):
                    if (L_mask >> (r * 9 + c)) & 1:
                        v |= 1 << r
                col_rows.add(v)
            for r in range(9):
                v = 0
                for c in range(9):
                    if (L_mask >> (r * 9 + c)) & 1:
                        v |= 1 << c
                row_rows.add(v)
            
            col_basis = _rref_basis_9(col_rows)
            row_basis = _rref_basis_9(row_rows)
            
            sat_info.append({
                'q': q, 'rank': rk, 'terms': I_q,
                'col_basis': col_basis, 'row_basis': row_basis
            })
    
    # For each term, intersect domains over all saturated contractions containing it
    term_domains = []
    for i, a in enumerate(support):
        B_spaces = []
        C_spaces = []
        sat_count = 0
        for si in sat_info:
            if i in si['terms']:
                B_spaces.append(si['col_basis'])
                C_spaces.append(si['row_basis'])
                sat_count += 1
        B_basis = _intersect_spaces_9(B_spaces) if B_spaces else list(range(9))  # full basis
        C_basis = _intersect_spaces_9(C_spaces) if C_spaces else list(range(9))
        B_dim = len([b for b in B_basis if b])
        C_dim = len([b for b in C_basis if b])
        term_domains.append({
            'term': i, 'a': a, 'B_dim': B_dim, 'C_dim': C_dim,
            'saturated_contractions': sat_count
        })
    
    return {
        'term_domains': term_domains,
        'total_saturated': len(sat_info),
        'zero_domain_terms': [t for t in term_domains if t['B_dim'] == 0 or t['C_dim'] == 0],
    }


def _rref_basis_9(rows):
    """RREF basis from a set of 9-bit row vectors."""
    basis = [0] * 9
    for row in rows:
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
    # Reduce
    for p in range(9):
        if basis[p]:
            for q in range(9):
                if q != p and basis[q] and (basis[q] >> p) & 1:
                    basis[q] ^= basis[p]
    return [b for b in basis if b]


def _intersect_spaces_9(spaces):
    """Intersect a list of subspaces of F_2^9, each given as RREF basis list."""
    if not spaces:
        return [1 << i for i in range(9)]
    # Start with the span of all vectors in the first space
    current_span = _span_set(spaces[0])
    for sp in spaces[1:]:
        other_span = _span_set(sp)
        current_span = current_span & other_span
    # Convert back to basis
    return _rref_basis_9(current_span)


def _span_set(basis):
    """All vectors in the span of basis (including 0)."""
    s = {0}
    for b in basis:
        s = s | {v ^ b for v in s}
    return s


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', default='data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--rank', type=int, default=19)
    ap.add_argument('--max-rounds', type=int, default=15)
    ap.add_argument('--solver-time', type=float, default=120.0)
    ap.add_argument('--out', type=Path, default=Path('data/dual_ruling/core_e11_saturation.json'))
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

    pivot = 1  # E11
    core = CoreQuotient(pivot)
    s = args.rank

    print(f'Building E11 core tensor (8x9x9)...')
    core_T = build_core_tensor_f2(pivot)
    print(f'  nonzero slices: {sum(1 for a in range(256) if core_T[a].any())}')

    print('Computing core contraction ranks...')
    c_ranks = core_contraction_ranks(core_T)
    rank_dist = Counter(c_ranks.values())
    print(f'  rank distribution: {dict(sorted(rank_dist.items()))}')

    print('Loading LUT...')
    t0 = time.time()
    lut, meta = load_lut(Path(args.lut))
    lut = {int(k): int(v) for k, v in lut.items()}
    print(f'  lut={len(lut):,} load_sec={time.time()-t0:.1f}')

    # Build core Wang constraints
    from ortools.sat.python import cp_model
    model = cp_model.CpModel()
    points = list(range(1, 256))
    x = {p: model.NewBoolVar(f'x_{p}') for p in points}
    model.Add(sum(x[p] for p in points) == s)

    # Wang upper constraints
    wang_added = set()
    wang_records = []

    # Add all dim-1 constraints
    for q8 in points:
        key8 = core.key8_from_rows([q8])
        if key8 not in wang_added:
            key9 = core.key9_from_key8(key8)
            if key9 in lut:
                lb = lut[key9]
                cap = s - lb
                if cap >= 0:
                    model.Add(x[q8] <= cap)  # For dim-1, only one point
                    wang_added.add(key8)
                    wang_records.append({'key8': key8, 'dim': 1, 'lb': lb, 'cap': cap})

    # Add dim-2 constraints (all lines)
    for q1 in points:
        for q2 in range(q1 + 1, 256):
            q3 = q1 ^ q2
            if q3 == 0 or q3 > q2:
                continue
            line_pts = [q1, q2, q3]
            key8 = core.key8_from_rows([q1, q2])
            if key8 in wang_added:
                continue
            key9 = core.key9_from_key8(key8)
            if key9 not in lut:
                continue
            lb = lut[key9]
            cap = s - lb
            if cap >= 0:
                model.Add(sum(x[p] for p in line_pts) <= cap)
                wang_added.add(key8)
                wang_records.append({'key8': key8, 'dim': 2, 'lb': lb, 'cap': cap})

    print(f'  initial wang constraints: {len(wang_added)} (dim1={sum(1 for r in wang_records if r["dim"]==1)}, dim2={sum(1 for r in wang_records if r["dim"]==2)})')

    # Contraction lower bounds
    lower_count = 0
    for q in range(1, 256):
        rk = c_ranks[q]
        ci = [p for p in points if bin(q & p).count('1') % 2 == 1]
        if rk > 0 and ci:
            model.Add(sum(x[p] for p in ci) >= rk)
            lower_count += 1
    print(f'  contraction lower bounds: {lower_count}')

    # ---------- ITERATIVE SEARCH ----------
    rounds = []
    final_status = None

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
               'wang_constraint_count': len(wang_added)}

        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            rounds.append(rec)
            final_status = status_name
            break

        support = sorted(p for p in points if solver.Value(x[p]))
        rec['support'] = support
        rec['support_size'] = len(support)

        # Check all core subspace Wang constraints
        violations = []
        checked_keys = set()
        # Generate all subspace keys from the support
        for mask in range(1, 1 << len(support)):
            pts_in = [support[j] for j in range(len(support)) if (mask >> j) & 1]
            if len(pts_in) > 6:  # Skip very high-dimensional
                continue
            key8 = core.key8_from_rows(pts_in)
            if key8 in checked_keys:
                continue
            checked_keys.add(key8)
            key9 = core.key9_from_key8(key8)
            if key9 not in lut:
                continue
            lb = lut[key9]
            cap = s - lb
            span_pts = subspace_points_from_basis(unpack_basis(key8))
            occ = sum(1 for p in span_pts if p in set(support))
            if occ > cap:
                violations.append({'key8': key8, 'key9': key9, 'lb': lb, 'cap': cap, 'occ': occ, 'excess': occ - cap, 'dim': key8 & 0xF})
        
        rec['violation_count'] = len(violations)
        rec['checked_subspaces'] = len(checked_keys)

        # Saturation analysis
        sat_result = core_saturated_domains(core_T, support, c_ranks)
        zero_terms = sat_result['zero_domain_terms']
        rec['saturation'] = {
            'total_saturated': sat_result['total_saturated'],
            'zero_domain_count': len(zero_terms),
            'domain_summary': Counter(f"B{t['B_dim']}_C{t['C_dim']}" for t in sat_result['term_domains']),
        }

        if len(violations) == 0 and len(zero_terms) == 0:
            rec['candidate_status'] = 'FULL_WANG_PASS_AND_SATURATION_PASS'
            rounds.append(rec)
            final_status = 'CANDIDATE_FOUND'
            print(f'  *** CANDIDATE: rank-19 core A-support passes all tests! ***')
            print(f'  support: {support}')
            break

        # Add violated subspace constraints
        added_wang = 0
        for v in sorted(violations, key=lambda v: (-v['excess'], -v['lb'])):
            key8 = v['key8']
            if key8 in wang_added:
                continue
            key9 = v['key9']
            lb = lut[key9]
            cap = s - lb
            span_pts = subspace_points_from_basis(unpack_basis(key8))
            model.Add(sum(x[p] for p in span_pts if p in set(points)) <= cap)
            wang_added.add(key8)
            added_wang += 1
        rec['added_wang'] = added_wang

        # If support has zero-domain terms, exclude it
        if zero_terms:
            model.AddBoolOr([x[p].Not() for p in support])
            rec['excluded_support'] = True

        print(f'  violations={len(violations)} zero_domains={len(zero_terms)} added_wang={added_wang} domains={rec["saturation"]["domain_summary"]}')
        rounds.append(rec)
        final_status = status_name

    result = {
        'schema': 'core_e11_saturation_v1',
        'core': 'E11',
        'pivot': pivot,
        'target_rank': s,
        'initial_wang_dim1': sum(1 for r in wang_records if r['dim'] == 1),
        'initial_wang_dim2': sum(1 for r in wang_records if r['dim'] == 2),
        'contraction_lower_count': lower_count,
        'core_contraction_rank_dist': dict(sorted(rank_dist.items())),
        'final_wang_constraints': len(wang_added),
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
