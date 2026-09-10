#!/usr/bin/env python3
"""Superseded vectorized skeleton prototype from analysis.

The highest-set-bit membership repair is kept, but the analysis single-point-orbit
triple scan is not a valid symmetry reduction: actual high-point sets must be
classified under one common branch stabilizer element.  For fixed-rank1-count
queries and genuine joint-orbit pilots use `skeleton_oracle_joint_pilot.py`.
"""
from __future__ import annotations

import argparse, json, pickle, sys, time
from collections import Counter, defaultdict
from pathlib import Path
from typing import List, Set, Tuple
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import (
    make_actions, transform_mask, matrix_rank_of_mask,
    unpack_basis, subspace_points_from_basis,
)

E11 = 1

# ======== Group orbit utilities ========

def rank1_points() -> list[int]:
    return [p for p in range(1, 512) if matrix_rank_of_mask(p) == 1]

def compute_stab_e11():
    actions = make_actions()
    stab = [img for img in actions if transform_mask(E11, img) == E11]
    unseen = set(range(2, 512))
    orbits = []
    while unseen:
        rep = min(unseen)
        members = {transform_mask(rep, img) for img in stab}
        orbits.append({'rep': rep, 'size': len(members), 'members': sorted(members),
                       'rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in members).items()))})
        unseen -= members
    orbits.sort(key=lambda o: o['rep'])
    return orbits, stab

def compute_stab_pair(stab_e11, rep):
    return [img for img in stab_e11 if transform_mask(rep, img) == rep]

def compute_orbits(stab, points):
    unseen = set(points)
    orbits = []
    while unseen:
        rep = min(unseen)
        members = set()
        for img in stab:
            q = transform_mask(rep, img)
            if q in unseen:
                members.add(q)
        if not members:
            members = {rep}
        orbits.append({'rep': rep, 'size': len(members), 'members': sorted(members),
                       'rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in members).items()))})
        unseen -= members
    orbits.sort(key=lambda o: o['rep'])
    return orbits

# ======== Numpy vectorized membership ========

def pack_bases_numpy(lut) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Pack all LUT bases and lower bounds into numpy arrays.
    Returns: bases (N,9) uint16, dims (N,) uint8, lbs (N,) uint8.
    """
    N = len(lut)
    bases = np.zeros((N, 9), dtype=np.uint16)
    lbs = np.zeros(N, dtype=np.uint8)
    dims = np.zeros(N, dtype=np.uint8)
    for i, (key, lb) in enumerate(lut.items()):
        vecs = unpack_basis(int(key))
        for j, v in enumerate(vecs):
            bases[i, j] = v
        dims[i] = len(vecs)
        lbs[i] = int(lb)
    return bases, dims, lbs

def highest_set_bit_np(b: np.ndarray) -> np.ndarray:
    """Compute highest-set-bit mask for uint16 array (0 for b==0)."""
    v = b.astype(np.uint16).copy()
    v |= v >> 1
    v |= v >> 2
    v |= v >> 4
    v |= v >> 8
    return (v - (v >> 1)).astype(np.uint16)

def vectorized_membership(bases: np.ndarray, point: int) -> np.ndarray:
    """Check if 'point' is in the span of each basis row set.
    Returns: bool array of shape (N,).
    Uses RREF convention: pivot = highest set bit of each basis vector.
    """
    N = bases.shape[0]
    reduced = np.full(N, point, dtype=np.uint16)
    for j in range(bases.shape[1]):
        b = bases[:, j]
        valid = b > 0
        # RREF pivot is the HIGHEST set bit (not lowest)
        pivot = highest_set_bit_np(b)
        mask = (reduced & pivot) != 0
        active = valid & mask
        reduced = np.where(active, reduced ^ b, reduced)
    return reduced == 0

def vectorized_multi_membership(bases: np.ndarray, points: list) -> np.ndarray:
    """Check membership for multiple points.
    Returns: int array of shape (N,) counting how many of 'points' are in each span.
    """
    N = bases.shape[0]
    count = np.zeros(N, dtype=np.int8)
    for p in points:
        count += vectorized_membership(bases, p).astype(np.int8)
    return count

# ======== Precompute base system ========

def precompute_base(bases, lbs, fixed_rank1, free_r1, rank_s=20):
    """Compute rank-1 masks and base capacities using vectorized membership.
    Returns: r1_masks (N,) uint64, base_caps (N,) int16.
    """
    N = bases.shape[0]
    print(f'  Computing rank-1 masks for {len(free_r1)} free r1 points...', flush=True)
    t0 = time.time()

    # Compute fixed-point membership counts
    fixed_count = np.zeros(N, dtype=np.int8)
    for p in fixed_rank1:
        fixed_count += vectorized_membership(bases, p).astype(np.int8)

    base_caps = rank_s - lbs.astype(np.int16) - fixed_count.astype(np.int16)

    # Compute rank-1 membership masks (as array of uint64)
    r1_masks = np.zeros(N, dtype=np.uint64)
    for idx, p in enumerate(free_r1):
        mem = vectorized_membership(bases, p)
        r1_masks |= np.where(mem, np.uint64(1 << idx), np.uint64(0))
        if (idx + 1) % 10 == 0:
            print(f'    r1 point {idx+1}/{len(free_r1)} done, {time.time()-t0:.1f}s', flush=True)

    print(f'  Base precomputation done in {time.time()-t0:.1f}s', flush=True)
    return r1_masks, base_caps

def build_tight_dict(r1_masks, caps):
    """Deduplicate: for each unique mask, keep minimum cap."""
    tight = {}
    for i in range(len(r1_masks)):
        m = int(r1_masks[i])
        c = int(caps[i])
        old = tight.get(m)
        if old is None or c < old:
            tight[m] = c
    return tight

# ======== Skeleton query ========

def skeleton_query_fast(base_tight, r1_masks, base_caps, bases,
                        fixed_high, n_free_r1, excluded_r1_indices,
                        *, time_limit=60, workers=8):
    """Fast skeleton query using precomputed base + numpy membership."""
    from ortools.sat.python import cp_model
    t0 = time.time()

    # Compute HR adjustment
    if fixed_high:
        hr_count = vectorized_multi_membership(bases, fixed_high)
        adjusted_caps = base_caps - hr_count.astype(np.int16)
    else:
        adjusted_caps = base_caps

    # Build adjusted tight dict (start from base, update affected entries)
    adjusted_tight = dict(base_tight)
    if fixed_high:
        affected = np.where(hr_count > 0)[0]
        for i in affected:
            m = int(r1_masks[i])
            c = int(adjusted_caps[i])
            old = adjusted_tight.get(m)
            if old is None or c < old:
                adjusted_tight[m] = c

    # Check for empty-mask negative cap
    if adjusted_tight.get(0, 999) < 0:
        return 'INFEASIBLE', None, {'immediate': True, 'build_sec': round(time.time()-t0,3)}

    # Build CP-SAT
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f'x{i}') for i in range(n_free_r1)]
    for i in excluded_r1_indices:
        model.Add(x[i] == 0)

    needed = 18 - len(fixed_high)
    if needed < 0:
        return 'INFEASIBLE', None, {'immediate': True, 'reason': 'too_many_high', 'build_sec': round(time.time()-t0,3)}
    if needed > n_free_r1 - len(excluded_r1_indices):
        return 'INFEASIBLE', None, {'immediate': True, 'reason': 'not_enough_r1', 'build_sec': round(time.time()-t0,3)}
    model.Add(sum(x) == needed)

    added = 0
    for mask, cap in adjusted_tight.items():
        if mask == 0:
            if cap < 0:
                model.AddBoolOr([])
                added += 1
            continue
        bits = [i for i in range(n_free_r1) if (mask >> i) & 1]
        if cap < 0:
            model.AddBoolOr([])
            added += 1
        elif len(bits) > cap:
            model.Add(sum(x[i] for i in bits) <= cap)
            added += 1

    build_sec = time.time() - t0
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_search_workers = workers
    t1 = time.time()
    st = solver.Solve(model)
    solve_sec = time.time() - t1
    status = solver.StatusName(st)
    sol = None
    if status in ('OPTIMAL', 'FEASIBLE'):
        sol = [i for i in range(n_free_r1) if solver.Value(x[i])]

    stats = {'status': status, 'constraints': added, 'build_sec': round(build_sec,3),
             'solve_sec': round(solve_sec,3), 'conflicts': int(solver.NumConflicts()),
             'branches': int(solver.NumBranches())}
    return status, sol, stats

# ======== Main ========

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rep', type=int, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--rank-s', type=int, default=20)
    ap.add_argument('--time-limit', type=float, default=60)
    args = ap.parse_args()

    # Load LUT
    print('Loading LUT...', flush=True)
    with args.lut.open('rb') as f:
        payload = pickle.load(f)
    lut = payload['lut']
    meta = payload.get('meta', {})
    print(f'  {len(lut):,} subspaces', flush=True)

    # Pack into numpy
    print('Packing bases into numpy...', flush=True)
    t0 = time.time()
    bases, dims, lbs = pack_bases_numpy(lut)
    print(f'  Packed in {time.time()-t0:.1f}s, shape={bases.shape}', flush=True)

    # Group structure
    print('Computing group structure...', flush=True)
    t0 = time.time()
    e11_orbits, stab_e11 = compute_stab_e11()
    stab_pair = compute_stab_pair(stab_e11, args.rep)
    print(f'  |Stab(E11)|={len(stab_e11)}, |Stab(E11,{args.rep})|={len(stab_pair)}, time={time.time()-t0:.1f}s', flush=True)

    # Determine branch
    r1_all = rank1_points()
    excluded = set()
    for orb in e11_orbits:
        if orb['rep'] == args.rep:
            break
        excluded.update(orb['members'])
    excluded.discard(E11)
    excluded.discard(args.rep)

    fixed_rank1 = [E11, args.rep]
    fixed_set = set(fixed_rank1)
    free_r1 = [p for p in r1_all if p not in fixed_set and p not in excluded]
    r1_index = {p: i for i, p in enumerate(free_r1)}
    excluded_r1_idx = []  # all excluded r1 are already removed from free_r1

    avail_all = [p for p in range(1, 512) if p not in fixed_set and p not in excluded]
    avail_hr = [p for p in avail_all if p not in set(free_r1)]

    print(f'  free_r1={len(free_r1)}, avail_hr={len(avail_hr)}', flush=True)

    # Compute HR orbits under Stab(E11, rep)
    hr_orbits = compute_orbits(stab_pair, avail_hr)
    print(f'  {len(hr_orbits)} HR orbits under Stab(E11,{args.rep})', flush=True)
    orbit_by_rep = {orb['rep']: orb for orb in hr_orbits}

    # Precompute base system
    print('Precomputing base constraints...', flush=True)
    r1_masks, base_caps = precompute_base(bases, lbs, fixed_rank1, free_r1, args.rank_s)
    base_tight = build_tight_dict(r1_masks, base_caps)
    print(f'  {len(base_tight):,} unique rank-1 masks', flush=True)

    results = {
        'branch': {'rep': args.rep, 'fixed_rank1': fixed_rank1,
                   'free_r1_count': len(free_r1), 'avail_hr_count': len(avail_hr),
                   'excluded_count': len(excluded), 'stab_order': len(stab_pair)},
        'hr_orbits': [{'rep': o['rep'], 'size': o['size'], 'rank_hist': o['rank_hist']}
                      for o in hr_orbits],
        'base_mask_count': len(base_tight),
    }

    # === Test known infeasible configurations ===
    print('\n=== Known configuration tests ===', flush=True)
    known_tests = []
    if args.rep == 2:
        known_tests = [
            ('rep2_wit_k17', [25, 194, 217]),
            ('rep2_wit_k16', [34, 52, 278, 304]),
        ]
    elif args.rep == 16:
        known_tests = [
            ('rep16_wit_k14', [19, 21, 23, 25, 33, 41]),
        ]

    test_results = []
    for name, fh in known_tests:
        status, sol, stats = skeleton_query_fast(
            base_tight, r1_masks, base_caps, bases,
            fh, len(free_r1), excluded_r1_idx,
            time_limit=args.time_limit, workers=8)
        test_results.append({'name': name, 'fixed_high': fh, 'status': status, 'stats': stats,
                             'sol_size': len(sol) if sol else None})
        print(f'  {name}: {status} (build={stats["build_sec"]}s, solve={stats.get("solve_sec","N/A")}s)', flush=True)
    results['known_tests'] = test_results

    # === Find minimal forbidden subsets ===
    print('\n=== Minimal forbidden subset search ===', flush=True)
    min_forbidden = []
    for name, fh in known_tests:
        print(f'\n  Analyzing {name} ({fh})...', flush=True)
        # First check full set is infeasible (confirm)
        status_full, _, _ = skeleton_query_fast(
            base_tight, r1_masks, base_caps, bases,
            fh, len(free_r1), excluded_r1_idx,
            time_limit=args.time_limit, workers=8)
        if status_full != 'INFEASIBLE':
            print(f'  WARNING: full set is {status_full}, not infeasible', flush=True)
            min_forbidden.append({'name': name, 'full_status': status_full, 'subsets': []})
            continue

        # Try removing each element
        subset_results = []
        for i, removed in enumerate(fh):
            subset = [h for j, h in enumerate(fh) if j != i]
            status, sol, stats = skeleton_query_fast(
                base_tight, r1_masks, base_caps, bases,
                subset, len(free_r1), excluded_r1_idx,
                time_limit=args.time_limit, workers=8)
            r = {'removed': removed, 'remaining': subset, 'status': status,
                 'stats': stats, 'sol_size': len(sol) if sol else None}
            subset_results.append(r)
            tag = 'INFEAS' if status == 'INFEASIBLE' else 'FEAS' if 'FEASIBLE' in status or 'OPTIMAL' in status else 'UNK'
            print(f'    \\{{{removed}}}: {tag} (build={stats["build_sec"]}s, solve={stats.get("solve_sec","N/A")}s)', flush=True)

        # If any pairs are infeasible, try singletons
        infeasible_pairs = [(r['remaining'], r['removed']) for r in subset_results if r['status'] == 'INFEASIBLE']
        singleton_tests = []
        if infeasible_pairs:
            print(f'  Found {len(infeasible_pairs)} infeasible subsets of size {len(fh)-1}. Testing deeper...', flush=True)
            # For each infeasible pair, try removing one more element
            for pair, _ in infeasible_pairs[:3]:  # limit depth
                for i, removed in enumerate(pair):
                    sub = [h for j, h in enumerate(pair) if j != i]
                    if len(sub) == 0:
                        continue
                    status, sol, stats = skeleton_query_fast(
                        base_tight, r1_masks, base_caps, bases,
                        sub, len(free_r1), excluded_r1_idx,
                        time_limit=args.time_limit, workers=8)
                    st = {'subset': sub, 'status': status, 'stats': stats}
                    singleton_tests.append(st)
                    tag = 'INFEAS' if status == 'INFEASIBLE' else 'FEAS' if 'FEASIBLE' in status or 'OPTIMAL' in status else 'UNK'
                    print(f'      {sub}: {tag}', flush=True)

        min_forbidden.append({
            'name': name, 'full_status': status_full,
            'subsets': subset_results, 'deeper': singleton_tests})
    results['minimal_forbidden'] = min_forbidden

    # === Orbit representative triple scan for k=17 (rep2 only) ===
    if args.rep == 2:
        print('\n=== Orbit-rep triple scan (k=17, m=3) ===', flush=True)
        # For k=17: need 3 HR points. The available HR orbits give representatives.
        # Check: for each triple of orbit reps, is the skeleton feasible?
        hr_reps = [o['rep'] for o in hr_orbits]
        n_reps = len(hr_reps)
        print(f'  {n_reps} HR orbit reps, C({n_reps},3) = {n_reps*(n_reps-1)*(n_reps-2)//6} triples', flush=True)

        # Start with a manageable pilot: check all triples where at least one rep is
        # from the witness higher-rank parts
        witness_reps_set = set()
        for name, fh in known_tests:
            for h in fh:
                # Find which orbit h belongs to
                for orb in hr_orbits:
                    if h in orb['members']:
                        witness_reps_set.add(orb['rep'])
                        break

        print(f'  Witness-adjacent orbit reps: {sorted(witness_reps_set)}', flush=True)

        triple_results = []
        # Test triples containing witness orbit reps
        tested = 0
        infeasible_count = 0
        feasible_count = 0
        from itertools import combinations
        for triple in combinations(hr_reps, 3):
            # Prioritize triples with witness connections
            if not witness_reps_set.intersection(triple):
                continue
            if tested >= 200:  # limit
                break
            status, sol, stats = skeleton_query_fast(
                base_tight, r1_masks, base_caps, bases,
                list(triple), len(free_r1), excluded_r1_idx,
                time_limit=30, workers=8)
            triple_results.append({'triple': list(triple), 'status': status, 'stats': stats,
                                   'sol_size': len(sol) if sol else None})
            tested += 1
            if status == 'INFEASIBLE':
                infeasible_count += 1
            elif status in ('OPTIMAL', 'FEASIBLE'):
                feasible_count += 1
            if tested % 20 == 0:
                print(f'    tested {tested}: {infeasible_count} infeas, {feasible_count} feas', flush=True)
            if feasible_count > 0:
                # Found a feasible triple!
                r1_sol = sol
                full_support = list(triple) + [free_r1[i] for i in r1_sol] + fixed_rank1
                print(f'  FEASIBLE triple found: {triple}', flush=True)
                print(f'  Full support ({len(full_support)} pts): {sorted(full_support)[:10]}...', flush=True)
                triple_results[-1]['full_support'] = sorted(full_support)
                break

        print(f'  Pilot complete: {tested} tested, {infeasible_count} infeas, {feasible_count} feas', flush=True)
        results['triple_scan'] = {
            'tested': tested, 'infeasible': infeasible_count, 'feasible': feasible_count,
            'witness_reps': sorted(witness_reps_set),
            'results': triple_results[:50],  # keep first 50
        }

    # Save
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(results, indent=2, sort_keys=True, default=str) + '\n')
    print(f'\nSaved to {args.out}')


if __name__ == '__main__':
    main()
