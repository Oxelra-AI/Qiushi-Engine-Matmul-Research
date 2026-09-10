#!/usr/bin/env python3
"""Enumerate rank-1-heavy Wang support skeletons and test exact-18 completions.

This script is an execution instrument for the remaining F2 T-level rank-20
Wang occupation support problem.  analysis proved that any admissible length-20
support has at most 18 rank-1 A-directions; exact-18 rank-1 skeletons are thus
a finite near-saturated surface.  The script enumerates exact-K rank-1 subsets
(optionally fixing E11) satisfying selected projected Wang inequalities, modulo
the Stab(E11) action, and can check whether a skeleton satisfies the complete
rank-1 projection.

It deliberately separates three notions:
  * projected rank-1 feasibility: only rank-1 intersections of Wang rows;
  * full T-level support feasibility after adding higher-rank points;
  * tensor decomposition feasibility, which is not tested here.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import pickle
import signal
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Set, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rank1_capacity_profile import load_or_build as load_rank1_projection  # noqa: E402
from wang_capacity_cnf_e11_fixed import E11  # noqa: E402
from wang_capacity_lazy import make_actions, matrix_rank_of_mask, transform_mask  # noqa: E402


def parse_groups(spec: str) -> Set[Tuple[int, int]] | None:
    spec = spec.strip()
    if not spec:
        return None
    out: Set[Tuple[int, int]] = set()
    for part in spec.replace(';', ',').split(','):
        part = part.strip()
        if not part:
            continue
        if ':' in part:
            a, b = part.split(':', 1)
        elif '/' in part:
            a, b = part.split('/', 1)
        else:
            raise ValueError(f"bad group spec {part!r}")
        out.add((int(a), int(b)))
    return out


def select_projected_rows(cons: Iterable[Tuple[int, int, int]], *, exact_count: int,
                          max_intersection_size: int | None,
                          include_groups: Set[Tuple[int, int]] | None,
                          full: bool) -> List[Tuple[int, int, int]]:
    rows: List[Tuple[int, int, int]] = []
    for mask, cap, key in cons:
        size = int(mask).bit_count()
        cap = int(cap)
        if size <= cap:
            continue
        if cap >= exact_count:
            # With exactly exact_count rank-1 points this projected row cannot
            # be violated, even if its raw intersection is larger.
            continue
        if not full:
            if include_groups is not None:
                if (size, cap) not in include_groups:
                    continue
            elif max_intersection_size is not None and size > max_intersection_size:
                continue
        rows.append((int(mask), cap, int(key)))
    return rows


def build_cnf(rank1_pts: List[int], rows: List[Tuple[int, int, int]], *, exact_count: int,
              fixed_point: int | None, direct_comb_limit: int):
    from pysat.card import CardEnc, EncType
    clauses: List[List[int]] = []
    top = len(rank1_pts)
    base_lits = list(range(1, len(rank1_pts) + 1))
    enc = CardEnc.equals(lits=base_lits, bound=exact_count, top_id=top, encoding=EncType.seqcounter)
    clauses.extend([list(c) for c in enc.clauses])
    top = enc.nv
    if fixed_point is not None:
        try:
            clauses.append([rank1_pts.index(fixed_point) + 1])
        except ValueError:
            clauses.append([])
    hist = Counter(); direct_rows = 0; direct_clauses = 0; card_rows = 0; card_clauses = 0; aux = 0
    for mask, cap, key in rows:
        lits = [i + 1 for i in range(len(rank1_pts)) if (mask >> i) & 1]
        if len(lits) <= cap:
            continue
        hist[(len(lits), cap)] += 1
        combs = math.comb(len(lits), cap + 1) if cap + 1 <= len(lits) else 0
        if combs <= direct_comb_limit:
            for comb in itertools.combinations(lits, cap + 1):
                clauses.append([-v for v in comb])
            direct_rows += 1; direct_clauses += combs
        else:
            old = top
            enc = CardEnc.atmost(lits=lits, bound=cap, top_id=top, encoding=EncType.seqcounter)
            clauses.extend([list(c) for c in enc.clauses])
            top = enc.nv; card_rows += 1; card_clauses += len(enc.clauses); aux += max(0, top - old)
    stats = {
        'num_vars': top,
        'num_clauses': len(clauses),
        'global_exact_count_clauses': len(CardEnc.equals(lits=base_lits, bound=exact_count, top_id=len(rank1_pts), encoding=EncType.seqcounter).clauses),
        'row_hist': {f'{a},{b}': c for (a, b), c in sorted(hist.items())},
        'direct_rows': direct_rows,
        'direct_clauses': direct_clauses,
        'card_rows': card_rows,
        'card_clauses': card_clauses,
        'aux_vars': aux,
    }
    return clauses, top, stats


def rank1_stabilizer_actions(fixed_point: int | None):
    actions = make_actions()
    if fixed_point is not None:
        actions = [img for img in actions if transform_mask(fixed_point, img) == fixed_point]
    return actions


def orbit_images(sset: frozenset[int], actions: Sequence[Sequence[int]]) -> Set[frozenset[int]]:
    return {frozenset(transform_mask(p, img) for p in sset) for img in actions}


def canonical_set(sset: frozenset[int], actions: Sequence[Sequence[int]]) -> Tuple[int, ...]:
    return min(tuple(sorted(imgset)) for imgset in orbit_images(sset, actions))


def projection_violations(sset: Set[int], rank1_pts: List[int], cons: Sequence[Tuple[int, int, int]], max_report: int = 20):
    idx = {p: i for i, p in enumerate(rank1_pts)}
    smask = 0
    for p in sset:
        smask |= 1 << idx[p]
    nviol = 0; max_excess = 0; by_group = Counter(); head = []
    for mask, cap, key in cons:
        occ = (smask & int(mask)).bit_count()
        excess = occ - int(cap)
        if excess > 0:
            nviol += 1; max_excess = max(max_excess, excess); by_group[(int(mask).bit_count(), int(cap))] += 1
            if len(head) < max_report:
                head.append({'key': int(key), 'dim': int(key) & 0xF, 'intersection_size': int(mask).bit_count(), 'cap': int(cap), 'occupancy': occ, 'excess': excess})
    return {'violation_count': nviol, 'max_excess': max_excess, 'violations_by_intersection_cap': {f'{a},{b}': c for (a, b), c in sorted(by_group.items())}, 'violations_head': head}


def enumerate_solutions(clauses: List[List[int]], rank1_pts: List[int], *, exact_count: int,
                        fixed_point: int | None, actions, max_orbits: int, max_models: int,
                        time_limit: float, full_cons: Sequence[Tuple[int, int, int]],
                        complete_projection_required: bool,
                        orbit_block: bool, witness_limit: int):
    from pysat.solvers import Solver
    t0 = time.time(); deadline = t0 + time_limit if time_limit > 0 else None
    seen_can: Set[Tuple[int, ...]] = set(); witnesses = []; full_ok = 0; model_count = 0; orbit_block_clauses = 0
    interrupted = False
    def handler(signum, frame):
        raise TimeoutError
    old_handler = signal.signal(signal.SIGALRM, handler)
    if time_limit > 0:
        signal.setitimer(signal.ITIMER_REAL, time_limit)
    try:
        with Solver(name='cadical153', bootstrap_with=clauses) as solver:
            while True:
                if max_models and model_count >= max_models:
                    break
                if max_orbits and len(seen_can) >= max_orbits:
                    break
                sat = solver.solve()
                if not sat:
                    break
                model_count += 1
                vals = set(v for v in solver.get_model() if 1 <= v <= len(rank1_pts))
                sset = frozenset(rank1_pts[v - 1] for v in vals)
                if len(sset) != exact_count:
                    raise RuntimeError(f'model selected {len(sset)} base vars, expected {exact_count}')
                can = canonical_set(sset, actions) if orbit_block else tuple(sorted(sset))
                if can not in seen_can:
                    seen_can.add(can)
                    proj = projection_violations(set(sset), rank1_pts, full_cons)
                    ok = proj['violation_count'] == 0
                    if ok:
                        full_ok += 1
                    if (not complete_projection_required or ok) and len(witnesses) < witness_limit:
                        witnesses.append({'support': sorted(sset), 'canonical': list(can), 'full_projection_check': proj})
                # Block this exact set or the whole stabilizer orbit.  Exact count
                # is part of the formula, so a negative clause on all selected
                # base variables removes exactly that selected subset.
                if orbit_block:
                    for imgset in orbit_images(sset, actions):
                        solver.add_clause([-(rank1_pts.index(p) + 1) for p in imgset])
                        orbit_block_clauses += 1
                else:
                    solver.add_clause([-(rank1_pts.index(p) + 1) for p in sset])
                    orbit_block_clauses += 1
    except TimeoutError:
        interrupted = True
    finally:
        if time_limit > 0:
            signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old_handler)
    return {
        'elapsed_sec': time.time() - t0,
        'interrupted_by_time_limit': interrupted,
        'raw_models_seen': model_count,
        'orbits_seen': len(seen_can),
        'full_projection_ok_orbits_seen': full_ok,
        'orbit_block_clauses_added': orbit_block_clauses,
        'witnesses': witnesses,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--cache', type=Path, default=Path('data/wang_capacity_rank1_profile/rank1_intersection_cache.pkl'))
    ap.add_argument('--rank-s', type=int, default=20)
    ap.add_argument('--exact-count', type=int, default=18)
    ap.add_argument('--fixed-point', type=int, default=E11)
    ap.add_argument('--no-fixed', action='store_true')
    ap.add_argument('--full-projection', action='store_true', help='encode every projected row with cap < exact-count')
    ap.add_argument('--max-intersection-size', type=int, default=9)
    ap.add_argument('--include-groups', default='')
    ap.add_argument('--direct-comb-limit', type=int, default=2000)
    ap.add_argument('--max-orbits', type=int, default=0)
    ap.add_argument('--max-models', type=int, default=0)
    ap.add_argument('--time-limit', type=float, default=300)
    ap.add_argument('--no-orbit-block', action='store_true')
    ap.add_argument('--complete-projection-required', action='store_true')
    ap.add_argument('--witness-limit', type=int, default=20)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()

    t0 = time.time()
    rank1_pts, full_cons, cmeta, lmeta = load_rank1_projection(args.cache, args.lut, args.rank_s, False)
    fixed = None if args.no_fixed else args.fixed_point
    selected = select_projected_rows(full_cons, exact_count=args.exact_count,
                                     max_intersection_size=args.max_intersection_size,
                                     include_groups=parse_groups(args.include_groups),
                                     full=args.full_projection)
    clauses, nv, cnf_stats = build_cnf(rank1_pts, selected, exact_count=args.exact_count,
                                       fixed_point=fixed, direct_comb_limit=args.direct_comb_limit)
    actions = rank1_stabilizer_actions(fixed)
    enum = enumerate_solutions(clauses, rank1_pts, exact_count=args.exact_count, fixed_point=fixed,
                               actions=actions, max_orbits=args.max_orbits, max_models=args.max_models,
                               time_limit=args.time_limit, full_cons=full_cons,
                               complete_projection_required=args.complete_projection_required,
                               orbit_block=not args.no_orbit_block, witness_limit=args.witness_limit)
    payload = {
        'problem': 'exact-K rank-1 projected Wang skeleton enumeration',
        'field': 'F2',
        'rank_s_for_capacities': args.rank_s,
        'exact_rank1_count': args.exact_count,
        'fixed_point': fixed,
        'rank1_point_count': len(rank1_pts),
        'rank1_points': rank1_pts,
        'projection_filter': {'full_projection': args.full_projection, 'max_intersection_size': args.max_intersection_size, 'include_groups': None if parse_groups(args.include_groups) is None else sorted([list(g) for g in parse_groups(args.include_groups)])},
        'selected_constraint_count': len(selected),
        'selected_constraint_hist': {f'{a},{b}': c for (a,b),c in sorted(Counter((m.bit_count(), cap) for m, cap, _ in selected).items())},
        'cnf_stats': cnf_stats,
        'stabilizer_action_count': len(actions),
        'enumeration': enum,
        'compression_meta_brief': {'compressed_intersections': cmeta.get('compressed_intersections'), 'nonvacuous_constraints': cmeta.get('nonvacuous_constraints'), 'constraint_size_cap_hist': cmeta.get('constraint_size_cap_hist')},
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'elapsed_total_sec': time.time() - t0,
        'meaning': 'Enumerates rank-1 skeletons only. A full-rank projection-feasible skeleton plus two higher-rank A-points is still only a Wang support candidate; B/C factors and Brent identities are not tested here.'
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'selected_constraint_count': len(selected),
        'cnf_vars': cnf_stats['num_vars'],
        'cnf_clauses': cnf_stats['num_clauses'],
        'stabilizer_action_count': len(actions),
        **{k: enum[k] for k in ['raw_models_seen','orbits_seen','full_projection_ok_orbits_seen','orbit_block_clauses_added','interrupted_by_time_limit','elapsed_sec']},
        'out': str(args.out),
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
