#!/usr/bin/env python3
"""Orbit-symmetrized CP-SAT for fixed-E11 Wang support with lex-leader breaking.

This script improves on wang_fixed_e11_range_cpsat.py by:
1. Computing Stab(E11, rep) inside GL(3,2)×GL(3,2)⋊C2.
2. Orbit-closing all violation seed rows under Stab(E11, rep) before
   adding them as cuts, so the solver cannot relocate violations to
   conjugate subspaces.
3. Adding lex-leader symmetry breaking on the remaining variable vector,
   preventing orbit-equivalent solutions.

These changes target the rep2/rep16 mid-range branches where unseeded
CP-SAT found supports violating 246/555 full-LUT rows and re-seeding
with those specific rows let the solver drift to conjugate violations.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence, Set, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import (
    N, in_rowspace, make_actions, matrix_rank_of_mask,
    pack_basis, rref_basis, subspace_points_from_basis,
    transform_mask, unpack_basis,
)
from wang_capacity_cnf_e11_fixed import (
    E11, collect_violation_keys, parse_dims, stab_e11_orbits,
)
from rank1_capacity_profile import load_or_build as load_or_build_rank1_projection


# ── group computation ────────────────────────────────────────────────

def compute_joint_stab(rep: int, stab_e11: List) -> List:
    """Return elements of Stab(E11) that also fix rep."""
    return [g for g in stab_e11 if transform_mask(rep, g) == rep]


def variable_permutation(pts: List[int], g) -> List[int]:
    """Permutation of variable indices induced by group element g."""
    idx = {p: i for i, p in enumerate(pts)}
    return [idx[transform_mask(p, g)] for p in pts]


def non_identity_perms(pts: List[int], stab: List) -> List[List[int]]:
    """Non-identity permutations of the variable indices."""
    identity = list(range(len(pts)))
    perms = []
    seen = set()
    for g in stab:
        perm = variable_permutation(pts, g)
        key = tuple(perm)
        if key != tuple(identity) and key not in seen:
            seen.add(key)
            perms.append(perm)
    return perms


# ── orbit closure of LUT keys ───────────────────────────────────────

def orbit_close_keys(seed_keys: Set[int], stab: List, lut: Dict[int, int]) -> Set[int]:
    """Close seed LUT keys under the joint stabilizer action on subspaces."""
    closed = set()
    for key in seed_keys:
        if key in closed:
            continue
        basis = unpack_basis(key)
        for g in stab:
            new_basis = tuple(transform_mask(v, g) for v in basis)
            new_rref = rref_basis(list(new_basis), n=N)
            new_key = pack_basis(new_rref)
            if new_key in lut:
                closed.add(new_key)
    return closed


# ── branch setup (reused from range model) ──────────────────────────

def branch_points(fixed_extra: Sequence[int], exclude_second_orbits_before: bool):
    fixed = [E11] + [int(p) for p in fixed_extra if int(p) != E11]
    if len(set(fixed)) != len(fixed):
        raise ValueError(f'duplicate fixed point in {fixed}')
    excluded: Set[int] = set()
    if exclude_second_orbits_before:
        if len(fixed_extra) != 1:
            raise ValueError('need exactly one --fixed-extra')
        second_rep = int(fixed_extra[0])
        found = False
        for orb in stab_e11_orbits():
            if orb['rep'] == second_rep:
                found = True
                break
            excluded.update(int(p) for p in orb['members'])
        if not found:
            raise ValueError(f'{second_rep} not a Stab(E11) rep')
        for p in fixed:
            excluded.discard(p)
    pts = [p for p in range(1, 512) if p not in excluded]
    idx = {p: i for i, p in enumerate(pts)}
    for p in fixed:
        if p not in idx:
            raise ValueError(f'fixed point {p} excluded')
    return fixed, excluded, pts, idx


def row_contains_all(pts, basis):
    return all(in_rowspace(int(p), basis, n=N) for p in pts)


# ── CP-SAT model ────────────────────────────────────────────────────

def parse_ints(s):
    if not s.strip(): return []
    return [int(x) for x in s.replace(';', ',').split(',') if x.strip()]


def parse_groups(spec):
    spec = spec.strip()
    if not spec: return None
    out = set()
    for p in spec.replace(';', ',').split(','):
        p = p.strip()
        if not p: continue
        a, b = (p.split(':', 1) if ':' in p else p.split('/', 1))
        out.add((int(a), int(b)))
    return out


def load_lut(path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def solve(lut, lut_meta, *, lut_path, rank_s, fixed_extra, exclude_second_orbits_before,
          min_rank1, max_rank1, exact_rank1,
          include_dims, through_fixed_dims,
          seed_keys, seed_dims,
          rank1_cache, rank1_max_isz, rank1_groups,
          time_limit, workers, use_symm, out):
    from ortools.sat.python import cp_model

    t0 = time.time()
    fixed, excluded, pts, idx = branch_points(fixed_extra, exclude_second_orbits_before)
    fixed_set = set(fixed)

    # ── joint stabilizer ──
    stab_info = {}
    perms_for_lex = []
    if use_symm and len(fixed_extra) == 1:
        rep = int(fixed_extra[0])
        actions = make_actions()
        stab_e11 = [img for img in actions if transform_mask(E11, img) == E11]
        stab_both = compute_joint_stab(rep, stab_e11)
        stab_info['stab_e11_size'] = len(stab_e11)
        stab_info['stab_both_size'] = len(stab_both)

        # orbit-close seed keys
        raw_seed_count = len(seed_keys)
        seed_keys = orbit_close_keys(seed_keys, stab_both, lut)
        stab_info['raw_seed_count'] = raw_seed_count
        stab_info['orbit_closed_seed_count'] = len(seed_keys)

        # non-identity permutations on variable indices
        perms_for_lex = non_identity_perms(pts, stab_both)
        stab_info['distinct_nontrivial_perms'] = len(perms_for_lex)
    else:
        stab_info['stab_both_size'] = 0
        stab_info['distinct_nontrivial_perms'] = 0

    # ── model ──
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f'x_{p}') for p in pts]
    model.Add(sum(x) == rank_s)
    for p in fixed:
        model.Add(x[idx[p]] == 1)

    rank1_lits = [x[idx[p]] for p in pts if matrix_rank_of_mask(p) == 1]
    if exact_rank1 is not None:
        model.Add(sum(rank1_lits) == exact_rank1)
    if min_rank1 is not None:
        model.Add(sum(rank1_lits) >= min_rank1)
    if max_rank1 is not None:
        model.Add(sum(rank1_lits) <= max_rank1)

    # ── lex-leader symmetry breaking ──
    lex_added = 0
    has_lex = hasattr(model, 'AddLexLessOrEqual')
    if perms_for_lex:
        for pi, perm in enumerate(perms_for_lex):
            permuted = [x[perm[i]] for i in range(len(x))]
            if has_lex:
                model.AddLexLessOrEqual(x, permuted)
                lex_added += 1
            else:
                # manual lex chain via eq-prefix indicators
                prev_eq = model.NewBoolVar(f'leq_{pi}_init')
                model.Add(prev_eq == 1)
                for k in range(len(x)):
                    j = perm[k]
                    if k == j:
                        continue
                    # if prev_eq: x[k] <= x[j]
                    model.Add(x[k] <= x[j]).OnlyEnforceIf(prev_eq)
                    new_eq = model.NewBoolVar(f'leq_{pi}_{k}')
                    # new_eq => prev_eq AND x[k]==x[j]
                    model.AddImplication(new_eq, prev_eq)
                    model.Add(x[k] == x[j]).OnlyEnforceIf(new_eq)
                    # NOT prev_eq => NOT new_eq
                    model.AddImplication(prev_eq.Not(), new_eq.Not())
                    prev_eq = new_eq
                lex_added += 1
    stab_info['lex_constraints_added'] = lex_added
    stab_info['lex_method'] = 'AddLexLessOrEqual' if has_lex else 'manual_chain'

    # ── Wang rows ──
    wang_added = 0; wang_skip = 0; wang_empty = 0
    dim_hist = Counter(); src_hist = Counter()
    for i, (key, lb0) in enumerate(lut.items(), 1):
        d = int(key) & 0xF
        basis = None; source = None
        if d in include_dims:
            source = 'include_dim'
        elif d in through_fixed_dims:
            basis = unpack_basis(key)
            if row_contains_all(fixed, basis):
                source = 'through_fixed'
        if source is None and key in seed_keys and d in seed_dims:
            source = 'seed'
        if source is None:
            continue
        if basis is None:
            basis = unpack_basis(key)
        pts_in = subspace_points_from_basis(basis)
        cap = rank_s - int(lb0)
        fixed_in = sum(1 for p in fixed if p in pts_in)
        cap_rem = cap - fixed_in
        lits = [x[idx[p]] for p in pts_in if p in idx and p not in fixed_set]
        dim_hist[d] += 1; src_hist[source] += 1
        if cap_rem < 0:
            model.AddBoolOr([]); wang_added += 1; wang_empty += 1
        elif len(lits) <= cap_rem:
            wang_skip += 1
        else:
            model.Add(sum(lits) <= cap_rem); wang_added += 1
        if i % 1_000_000 == 0:
            print(f'scanned {i:,}/{len(lut):,}; wang_added={wang_added:,}; elapsed={time.time()-t0:.1f}s', flush=True)

    # ── rank-1 projection ──
    r1_pts, r1_cons, r1_meta, r1_lmeta = load_or_build_rank1_projection(
        rank1_cache, lut_path, rank_s, False)
    r1_index = {p: i for i, p in enumerate(r1_pts)}
    fixed_rank1 = [p for p in fixed if matrix_rank_of_mask(p) == 1]
    r1_added = 0; r1_skip = 0
    for mask0, cap0, rkey in r1_cons:
        mask = int(mask0); cap = int(cap0); size = mask.bit_count()
        if rank1_groups is not None and (size, cap) not in rank1_groups:
            continue
        if rank1_groups is None and rank1_max_isz is not None and size > rank1_max_isz:
            continue
        fixed_in = 0
        for p in fixed_rank1:
            j = r1_index.get(p)
            if j is not None and ((mask >> j) & 1):
                fixed_in += 1
        cap_rem = cap - fixed_in
        lits = []
        y = mask
        while y:
            lb = y & -y; j = lb.bit_length() - 1; y ^= lb
            p = int(r1_pts[j])
            if p in idx and p not in fixed_set:
                lits.append(x[idx[p]])
        if cap_rem < 0:
            model.AddBoolOr([]); r1_added += 1
        elif len(lits) <= cap_rem:
            r1_skip += 1
        else:
            model.Add(sum(lits) <= cap_rem); r1_added += 1

    build_elapsed = time.time() - t0

    # ── solve ──
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_search_workers = workers
    t1 = time.time()
    st = solver.Solve(model)
    solve_elapsed = time.time() - t1
    names = {cp_model.OPTIMAL: 'OPTIMAL', cp_model.FEASIBLE: 'FEASIBLE',
             cp_model.INFEASIBLE: 'INFEASIBLE', cp_model.UNKNOWN: 'UNKNOWN',
             cp_model.MODEL_INVALID: 'MODEL_INVALID'}
    sol = None
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        sol = [p for p in pts if solver.Value(x[idx[p]])]

    payload = {
        'problem': 'orbit-symmetrized fixed-E11 Wang support CP-SAT',
        'field': 'F2',
        'rank_s': rank_s,
        'fixed_points': fixed,
        'fixed_extra': list(fixed_extra),
        'min_rank1': min_rank1,
        'max_rank1': max_rank1,
        'exact_rank1': exact_rank1,
        'include_dims': sorted(include_dims),
        'through_fixed_dims': sorted(through_fixed_dims),
        'seed_dims': sorted(seed_dims),
        'variable_count': len(pts),
        'wang_rows_added': wang_added,
        'wang_rows_skipped': wang_skip,
        'wang_empty': wang_empty,
        'wang_dim_hist': dict(sorted(dim_hist.items())),
        'wang_source_hist': dict(sorted(src_hist.items())),
        'rank1_projection_added': r1_added,
        'rank1_projection_skipped': r1_skip,
        'symmetry': stab_info,
        'solver_status': names.get(st, str(st)),
        'solver_walltime': float(solver.WallTime()),
        'solver_conflicts': int(solver.NumConflicts()),
        'solver_branches': int(solver.NumBranches()),
        'build_elapsed_sec': build_elapsed,
        'solve_elapsed_sec': solve_elapsed,
        'support': sol,
        'support_size': None if sol is None else len(sol),
        'support_rank_hist': None if sol is None else
            dict(sorted(Counter(matrix_rank_of_mask(p) for p in sol).items())),
        'support_rank1_count': None if sol is None else
            sum(1 for p in sol if matrix_rank_of_mask(p) == 1),
        'lut_meta_brief': {
            'coverage_ok': lut_meta.get('coverage_ok'),
            'conflict_count': lut_meta.get('conflict_count'),
            'subspace_count': lut_meta.get('subspace_count'),
        },
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: payload[k] for k in [
        'solver_status', 'support_size', 'support_rank_hist',
        'wang_rows_added', 'rank1_projection_added',
        'symmetry', 'build_elapsed_sec', 'solve_elapsed_sec',
    ]}, indent=2, sort_keys=True))
    print('saved', out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path,
                    default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--fixed-extra', default='')
    ap.add_argument('--exclude-second-orbits-before', action='store_true')
    ap.add_argument('--min-rank1', type=int, default=None)
    ap.add_argument('--max-rank1', type=int, default=None)
    ap.add_argument('--exact-rank1', type=int, default=None)
    ap.add_argument('--include-dims', default='1,2,3')
    ap.add_argument('--through-fixed-dims', default='4-8')
    ap.add_argument('--seed-json', type=Path, action='append', default=[])
    ap.add_argument('--seed-dims', default='4-8')
    ap.add_argument('--rank1-cache', type=Path,
                    default=Path('data/wang_capacity_rank1_profile/rank1_intersection_cache.pkl'))
    ap.add_argument('--rank1-max-intersection-size', type=int, default=None)
    ap.add_argument('--rank1-include-groups', default='')
    ap.add_argument('--time-limit', type=float, default=600)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--no-symm', action='store_true', help='disable symmetry features')
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()

    fixed_extra = parse_ints(args.fixed_extra)
    seed_keys: Set[int] = set()
    for path in args.seed_json:
        got = collect_violation_keys(path)
        print(f'seed {path}: {len(got)} keys', flush=True)
        seed_keys.update(got)

    lut, meta = load_lut(args.lut)
    print(f'loaded LUT {len(lut):,} coverage={meta.get("coverage_ok")} conflicts={meta.get("conflict_count")}', flush=True)

    solve(
        lut, meta, lut_path=args.lut, rank_s=args.rank,
        fixed_extra=fixed_extra,
        exclude_second_orbits_before=args.exclude_second_orbits_before,
        min_rank1=args.min_rank1, max_rank1=args.max_rank1,
        exact_rank1=args.exact_rank1,
        include_dims=parse_dims(args.include_dims),
        through_fixed_dims=parse_dims(args.through_fixed_dims),
        seed_keys=seed_keys, seed_dims=parse_dims(args.seed_dims),
        rank1_cache=args.rank1_cache,
        rank1_max_isz=args.rank1_max_intersection_size,
        rank1_groups=parse_groups(args.rank1_include_groups),
        time_limit=args.time_limit, workers=args.workers,
        use_symm=not args.no_symm, out=args.out,
    )


if __name__ == '__main__':
    main()
