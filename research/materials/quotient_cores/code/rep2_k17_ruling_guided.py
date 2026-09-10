#!/usr/bin/env python3
"""Ruling-aware guided test for the rep2 adjacent-pair branch at exact k=17.

This script is an execution probe, not a theorem certificate.  It asks a narrow
question raised after analysis:

    Do the proof-backed transported ruling-line exclusions change the remaining
    mixed-rank rep2 search, beyond the old Wang skeleton necessary condition?

The parent branch is the adjacent rank-1 pair {1,2} = {E11,E12}.  Since the
exact-k=18 completion layer is already closed, the top remaining adjacent-pair
rank count is k=17: two fixed rank-1 points, 15 further rank-1 points, and three
higher-rank A-points.  The script recovers the earlier actual-set pair/clique
machinery, builds the conservative graph of still-possible higher-rank triples
under Stab({1,2}), and queries full high triples with a CP-SAT skeleton oracle
that includes all Wang occupation rows plus the transported rank-1 ruling-line
clauses.

For every ruling-INFEASIBLE subset found during shrinking, it also queries the
old Wang-only skeleton oracle on the same subset.  This distinguishes a genuinely
new ruling-enabled incompatibility (Wang-only feasible/optimal, ruling infeasible)
from an old Wang incompatibility that simply had not yet been recorded.

All outputs are scoped as CP-SAT skeleton evidence.  UNSAT/infeasible CP-SAT rows
are not formal proof leaves until converted to proof-producing CNF/DRAT or an
independent proof object.
"""
from __future__ import annotations

import argparse
import itertools
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from general_singleton_pair_survey import GeneralExactKOracle, build_branch_general  # noqa: E402
from precompute_skeleton_system import compute_stab_e11, pack_bases_numpy, vectorized_multi_membership  # noqa: E402
from skeleton_oracle_joint_pilot import canonical_set, orbit_image_count  # noqa: E402
from guided_clique_oracle import find_clique_with_hyperedges, max_clique_size  # noqa: E402
from ruling_line_transport import all_ruling_triples, simplify_ruling  # noqa: E402
from wang_capacity_lazy import make_actions, matrix_rank_of_mask, transform_mask  # noqa: E402

FEAS = {'OPTIMAL', 'FEASIBLE'}


def load_lut_pickle(path: Path) -> tuple[dict[int, int], dict]:
    with path.open('rb') as f:
        payload = pickle.load(f)
    if isinstance(payload, dict) and 'lut' in payload:
        return payload['lut'], payload.get('meta', {})
    return payload, {}


def setwise_stabilizer_pair(p: int = 1, q: int = 2) -> list:
    pair = {int(p), int(q)}
    return [g for g in make_actions() if {transform_mask(p, g), transform_mask(q, g)} == pair]


def all_images(points: Sequence[int], group: Sequence[Sequence[int]]) -> list[tuple[int, ...]]:
    return sorted({tuple(sorted(transform_mask(int(p), g) for p in points)) for g in group})


def add_pair_images(adj: list[int], pt_to_i: dict[int, int], images: Iterable[Sequence[int]]) -> int:
    changed = 0
    for img in images:
        if len(img) != 2:
            continue
        a, b = int(img[0]), int(img[1])
        if a == b or a not in pt_to_i or b not in pt_to_i:
            continue
        i, j = pt_to_i[a], pt_to_i[b]
        if (adj[i] >> j) & 1:
            adj[i] &= ~(1 << j)
            adj[j] &= ~(1 << i)
            changed += 1
    return changed


def add_singleton_images(forbidden_vertices: set[int], pt_to_i: dict[int, int],
                         images: Iterable[Sequence[int]]) -> int:
    before = len(forbidden_vertices)
    for img in images:
        if len(img) == 1 and int(img[0]) in pt_to_i:
            forbidden_vertices.add(pt_to_i[int(img[0])])
    return len(forbidden_vertices) - before


def hyperedge_images(points: Sequence[int], group, pt_to_i: dict[int, int]) -> list[tuple[int, ...]]:
    out = []
    for img in all_images(points, group):
        if all(int(p) in pt_to_i for p in img):
            out.append(tuple(sorted(pt_to_i[int(p)] for p in img)))
    return sorted(set(out))


def load_json(path: Path | None) -> dict | None:
    if path is None:
        return None
    if not path.exists() or path.stat().st_size == 0:
        raise FileNotFoundError(f'{path} missing/empty')
    return json.loads(path.read_text())


def singleton_status_rows(data: dict | None) -> list[dict]:
    if data is None:
        return []
    if 'phase1_results' in data:
        return list(data['phase1_results'])
    if 'singleton_results' in data:
        return list(data['singleton_results'])
    if 'k_results' in data:
        out = []
        for e in data['k_results']:
            out.extend(e.get('singleton_results', []))
        return out
    return []


def old_pair_constraints(data: dict | None, branch_rep: int, k: int) -> list[dict]:
    if data is None:
        return []
    rows = []
    if 'constraints' in data:
        rows = list(data['constraints'])
    elif 'pair_results' in data:
        for r in data['pair_results']:
            if r.get('status') == 'INFEASIBLE':
                rows.append({
                    'branch_second_rep': branch_rep,
                    'exact_rank1_count': data.get('k', k),
                    'canonical_subset': r.get('canonical'),
                    'forbidden_subset_size': len(r.get('canonical', [])),
                    'source': 'pair_results',
                })
    elif 'k_results' in data:
        for e in data['k_results']:
            for r in e.get('pair_results', []):
                if r.get('status') == 'INFEASIBLE':
                    rows.append({
                        'branch_second_rep': branch_rep,
                        'exact_rank1_count': e.get('k', k),
                        'canonical_subset': r.get('canonical'),
                        'forbidden_subset_size': len(r.get('canonical', [])),
                        'source': 'k_results.pair_results',
                    })
    out = []
    for c in rows:
        if int(c.get('branch_second_rep', branch_rep)) != int(branch_rep):
            continue
        k0 = int(c.get('exact_rank1_count', k))
        # Infeasible at k0 is monotone upward for these upper-bound skeleton systems.
        if k0 > int(k):
            continue
        pts = [int(x) for x in c.get('canonical_subset', c.get('source_subset', []))]
        if not pts:
            continue
        out.append({**c, 'exact_rank1_count': k0, 'canonical_subset': pts})
    return out


class RulingExactKOracle(GeneralExactKOracle):
    """GeneralExactKOracle plus transported ruling-line clauses on rank-1 variables."""

    def __init__(self, *, branch, bases, lbs, keys, rank_s, prefix: Sequence[int]):
        super().__init__(branch=branch, bases=bases, lbs=lbs, keys=keys, rank_s=rank_s)
        self.prefix = [int(x) for x in prefix]
        rcl = simplify_ruling(all_ruling_triples(), set(self.prefix))
        self.ruling_point_clauses: list[tuple[int, ...]] = []
        for kind in ('unit', 'binary', 'ternary'):
            for item in rcl[kind]:
                pts = (int(item),) if kind == 'unit' else tuple(int(x) for x in item)
                # Fixed prefix has already been simplified away; skip clauses outside free rank1.
                if all(p in self.free_r1 for p in pts):
                    self.ruling_point_clauses.append(tuple(sorted(pts)))
        self.ruling_point_clauses = sorted(set(self.ruling_point_clauses))
        self.ruling_meta = {
            'total_ruling_triples': 98,
            'simplified_counts': {
                'unit': len(rcl['unit']),
                'binary': len(rcl['binary']),
                'ternary': len(rcl['ternary']),
                'contradictions': int(rcl['contradictions']),
            },
            'encoded_clause_count': len(self.ruling_point_clauses),
            'encoded_size_hist': dict(sorted(Counter(len(c) for c in self.ruling_point_clauses).items())),
            'proof_source': 'transport of the analysis fixed-prefix [1,2,3] exclusion across all Segre ruling lines',
        }

    def query(self, additional_high, exact_rank1_count, *, time_limit, workers, capture_support=True):
        from ortools.sat.python import cp_model
        t0 = time.time()
        additional_high = sorted(int(p) for p in additional_high)
        if len(set(additional_high)) != len(additional_high):
            return {'status': 'INVALID_DUPLICATE_HIGH_POINTS', 'additional_high': additional_high}
        overlap_perm = sorted(set(additional_high) & set(self.fixed_hr_permanent))
        if overlap_perm:
            return {'status': 'INVALID_HIGH_POINTS', 'reason': 'additional_high_overlaps_fixed_hr_permanent', 'bad': overlap_perm}
        avail_hr_set = set(self.branch['avail_hr'])
        bad = [p for p in additional_high if p not in avail_hr_set]
        if bad:
            return {'status': 'INVALID_HIGH_POINTS', 'bad': bad}
        free_needed = int(exact_rank1_count) - len(self.fixed_rank1)
        if free_needed < 0 or free_needed > len(self.free_r1):
            return {'status': 'PARAMETER_OUT_OF_RANGE', 'reason': 'rank1_count_bounds', 'free_needed': int(free_needed)}

        if additional_high:
            hr_count = vectorized_multi_membership(self.bases, additional_high)
            adjusted_caps = self.base_caps - hr_count.astype(np.int16)
        else:
            adjusted_caps = self.base_caps

        adjusted_tight = dict(self.base_tight)
        if additional_high:
            affected = np.where(hr_count > 0)[0]
            for i in affected:
                m = int(self.r1_masks[i])
                c = int(adjusted_caps[i])
                old = adjusted_tight.get(m)
                if old is None or c < old:
                    adjusted_tight[m] = c

        model = cp_model.CpModel()
        x = [model.NewBoolVar(f'x_{p}') for p in self.free_r1]
        point_to_i = {p: i for i, p in enumerate(self.free_r1)}
        model.Add(sum(x) == free_needed)
        constraints_added = 0
        empty_constraints = 0
        for mask, cap in adjusted_tight.items():
            bc = int(mask).bit_count()
            if bc > cap:
                if cap < 0:
                    model.AddBoolOr([])
                    empty_constraints += 1
                else:
                    inds = [i for i in range(len(self.free_r1)) if (int(mask) >> i) & 1]
                    model.Add(sum(x[i] for i in inds) <= int(cap))
                constraints_added += 1

        for pts in self.ruling_point_clauses:
            inds = [point_to_i[p] for p in pts]
            # forbid selecting the entire transported ruling-line residual set
            model.Add(sum(x[i] for i in inds) <= len(inds) - 1)
        ruling_constraints_added = len(self.ruling_point_clauses)

        build_sec = time.time() - t0
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(time_limit)
        solver.parameters.num_search_workers = int(workers)
        t1 = time.time()
        st = solver.Solve(model)
        solve_sec = time.time() - t1
        status = solver.StatusName(st)

        support_rank1 = None
        if capture_support and status in FEAS:
            support_free = [self.free_r1[i] for i in range(len(self.free_r1)) if solver.Value(x[i])]
            support_rank1 = sorted(self.fixed_rank1 + support_free)
        all_high = sorted(self.fixed_hr_permanent + additional_high)
        return {
            'status': status,
            'additional_high': additional_high,
            'all_fixed_high': all_high,
            'exact_rank1_count': int(exact_rank1_count),
            'free_needed': int(free_needed),
            'constraints_added': constraints_added,
            'ruling_constraints_added': ruling_constraints_added,
            'empty_constraints': empty_constraints,
            'build_sec': build_sec,
            'solve_sec': solve_sec,
            'support_rank1': support_rank1,
            'support_all': (sorted(support_rank1 + all_high) if support_rank1 else None),
            'num_conflicts': int(solver.NumConflicts()),
            'num_branches': int(solver.NumBranches()),
        }


def support_ruling_occupancy(support: Sequence[int]) -> dict:
    rank1_support = set(p for p in support if matrix_rank_of_mask(int(p)) == 1)
    hist = Counter()
    max_occ = 0
    bad = []
    for tri in all_ruling_triples():
        occ = len(set(int(x) for x in tri) & rank1_support)
        hist[occ] += 1
        max_occ = max(max_occ, occ)
        if occ >= 3:
            bad.append(sorted(int(x) for x in tri))
    return {'max_occ': max_occ, 'occupancy_hist': dict(sorted(hist.items())), 'violating_triples': bad[:20], 'violating_count': len(bad)}


def scan_support_vectorized(bases: np.ndarray, lbs: np.ndarray, support: Sequence[int]) -> dict:
    cnt = np.zeros(bases.shape[0], dtype=np.int16)
    for p in support:
        # inline vectorized membership imported through vectorized_multi_membership would loop anyway;
        # use it for one point at a time by passing singleton list.
        cnt += vectorized_multi_membership(bases, [int(p)]).astype(np.int16)
    caps = 20 - lbs.astype(np.int16)
    viol = np.where(cnt > caps)[0]
    return {
        'support_size': len(support),
        'violation_count': int(len(viol)),
        'max_excess': int(np.max(cnt[viol] - caps[viol])) if len(viol) else 0,
        'first_violation_indices': [int(x) for x in viol[:10]],
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--survivor-json', type=Path, default=Path('data/coverage/rep2_k17_survivors_corrected.json'))
    ap.add_argument('--constraint-json', type=Path, action='append', default=[Path('data/guided_clique/merged_guided_constraints_v3.json')])
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--k', type=int, default=17)
    ap.add_argument('--iterations', type=int, default=4)
    ap.add_argument('--time-limit-full', type=float, default=25.0)
    ap.add_argument('--time-limit-shrink', type=float, default=15.0)
    ap.add_argument('--time-limit-compare', type=float, default=15.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--max-search-nodes', type=int, default=2_000_000)
    args = ap.parse_args()

    t_all = time.time()
    print(f'Loading LUT {args.lut}...', flush=True)
    lut, meta = load_lut_pickle(args.lut)
    keys = list(lut.keys())
    print(f'  LUT rows={len(lut):,}', flush=True)
    bases, dims, lbs = pack_bases_numpy(lut)

    _, stab_e11 = compute_stab_e11()
    branch = build_branch_general(2, stab_e11)
    stab_setwise = setwise_stabilizer_pair(1, 2)
    print(f'  pointwise_stab={len(branch["stab_pair"])} setwise_stab={len(stab_setwise)}', flush=True)

    # Candidate high-rank vertices after old singleton eliminations.
    all_hr = sorted(p for p in range(1, 512) if matrix_rank_of_mask(p) > 1)
    pt_to_i_all = {p: i for i, p in enumerate(all_hr)}
    forbidden_vertex_idx: set[int] = set()
    singleton_sources = []
    sdata = load_json(args.survivor_json)
    for row in singleton_status_rows(sdata):
        if int(row.get('k', args.k)) != int(args.k):
            continue
        if row.get('status') == 'INFEASIBLE':
            rep = int(row['orbit_rep'])
            imgs = all_images([rep], stab_setwise)
            added = add_singleton_images(forbidden_vertex_idx, pt_to_i_all, imgs)
            singleton_sources.append({'rep': rep, 'images': len(imgs), 'new_vertices_removed': added, 'source': str(args.survivor_json)})
    vertices = [p for i, p in enumerate(all_hr) if i not in forbidden_vertex_idx]
    pt_to_i = {p: i for i, p in enumerate(vertices)}
    n = len(vertices)
    adj = [(1 << n) - 1 for _ in range(n)]
    for i in range(n):
        adj[i] &= ~(1 << i)
    proved_hyperedges: set[tuple[int, ...]] = set()
    edge_sources = []
    old_pair_canonicals: set[tuple[int, ...]] = set()

    for cpath in args.constraint_json:
        cdata = load_json(cpath)
        for c in old_pair_constraints(cdata, branch_rep=2, k=args.k):
            pts = [int(x) for x in c['canonical_subset']]
            old_pair_canonicals.add(tuple(canonical_set(pts, stab_setwise)))
            imgs = all_images(pts, stab_setwise)
            if len(pts) == 1:
                added = add_singleton_images(set(), pt_to_i, imgs)  # just count below through hyperedge removal
                hs = hyperedge_images(pts, stab_setwise, pt_to_i)
                proved_hyperedges.update(hs)
                edge_sources.append({'source': str(cpath), 'type': 'singleton', 'k0': int(c['exact_rank1_count']), 'canonical_subset': pts, 'images': len(hs), 'new_vertices_as_hyperedges': added})
            elif len(pts) == 2:
                changed = add_pair_images(adj, pt_to_i, imgs)
                edge_sources.append({'source': str(cpath), 'type': 'pair', 'k0': int(c['exact_rank1_count']), 'canonical_subset': pts, 'images': len(imgs), 'edges_removed': changed})
            else:
                hs = hyperedge_images(pts, stab_setwise, pt_to_i)
                before = len(proved_hyperedges)
                proved_hyperedges.update(hs)
                edge_sources.append({'source': str(cpath), 'type': 'hyperedge', 'k0': int(c['exact_rank1_count']), 'canonical_subset': pts, 'images': len(hs), 'new_hyperedges': len(proved_hyperedges)-before})

    # Apply singleton hyperedges from constraints by isolating vertices if any are present.
    singleton_h = sorted(h[0] for h in proved_hyperedges if len(h) == 1)
    for i in singleton_h:
        for j in range(n):
            if i != j:
                adj[i] &= ~(1 << j)
                adj[j] &= ~(1 << i)
        adj[i] = 0

    print('Building Wang-only and ruling-aware rank1 skeleton oracles...', flush=True)
    base_oracle = GeneralExactKOracle(branch=branch, bases=bases, lbs=lbs, keys=keys, rank_s=20)
    ruling_oracle = RulingExactKOracle(branch=branch, bases=bases, lbs=lbs, keys=keys, rank_s=20, prefix=[1, 2])
    target_high = 20 - args.k
    if target_high != 3:
        print(f'Warning: k={args.k} target_high={target_high}; this script was designed for k=17/top mixed layer.', flush=True)

    initial_degrees = [a.bit_count() for a in adj]
    print(json.dumps({
        'vertices': n, 'edges': sum(initial_degrees)//2, 'target_high': target_high,
        'ruling_meta': ruling_oracle.ruling_meta,
    }, sort_keys=True), flush=True)

    tested_canonicals: set[tuple[int, ...]] = set()
    temporary_skip_hyperedges: set[tuple[int, ...]] = set()
    ruling_new_pairs: set[tuple[int, ...]] = set()
    ruling_strict_pairs: set[tuple[int, ...]] = set()
    iterations = []
    support_candidate_path = None
    closed_by_graph = False
    graph_size_info = None

    for it in range(1, args.iterations + 1):
        active_hyperedges = sorted(proved_hyperedges | temporary_skip_hyperedges)
        clique_idx, search_stats = find_clique_with_hyperedges(
            adj, target_high, active_hyperedges, tested_canonicals, vertices, stab_setwise,
            max_nodes=args.max_search_nodes,
        )
        if clique_idx is None:
            omega, best_idx, exact = max_clique_size(adj, sorted(proved_hyperedges), target_cap=target_high)
            graph_size_info = {'omega_or_cap': omega, 'exact_if_below_target': exact, 'witness': [vertices[i] for i in best_idx]}
            closed_by_graph = bool(exact and omega < target_high)
            iterations.append({'iteration': it, 'event': 'no_target_clique', 'search_stats': search_stats, 'graph_size_info': graph_size_info, 'closed_by_graph': closed_by_graph})
            break

        high = sorted(vertices[i] for i in clique_idx)
        can_high = tuple(canonical_set(high, stab_setwise))
        tested_canonicals.add(can_high)
        print(f'Iteration {it}: high={high} canonical={list(can_high)}', flush=True)
        rq = ruling_oracle.query(high, args.k, time_limit=args.time_limit_full, workers=args.workers, capture_support=True)
        bq = base_oracle.query(high, args.k, time_limit=args.time_limit_compare, workers=args.workers, capture_support=False)
        entry = {
            'iteration': it,
            'event': 'full_high_ruling_query',
            'high': high,
            'canonical_high': list(can_high),
            'orbit_image_count_setwise': orbit_image_count(high, stab_setwise),
            'ruling_status': rq.get('status'),
            'ruling_build_sec': rq.get('build_sec'),
            'ruling_solve_sec': rq.get('solve_sec'),
            'ruling_constraints_added': rq.get('ruling_constraints_added'),
            'wang_only_compare_status': bq.get('status'),
            'wang_only_compare_solve_sec': bq.get('solve_sec'),
            'search_stats': search_stats,
        }
        if rq.get('status') in FEAS:
            support = rq.get('support_all') or []
            entry['support_all'] = support
            entry['support_rank_hist'] = dict(sorted(Counter(matrix_rank_of_mask(p) for p in support).items()))
            entry['ruling_occupancy'] = support_ruling_occupancy(support)
            entry['full_lut_vector_scan'] = scan_support_vectorized(bases, lbs, support)
            cand = {
                'problem': 'rep2 exact-k17 A-support candidate satisfying Wang skeleton plus ruling-line exclusions',
                'field': 'F2',
                'fixed_prefix': [1, 2],
                'exact_rank1_count': args.k,
                'high': high,
                'support': support,
                'rank_hist': entry['support_rank_hist'],
                'ruling_occupancy': entry['ruling_occupancy'],
                'full_lut_vector_scan': entry['full_lut_vector_scan'],
                'meaning': 'A-side occupation/ruling support candidate only; not a tensor decomposition and not B/C-extendability evidence.',
            }
            support_candidate_path = args.out.parent / f'rep2_k17_ruling_support_iter{it}.json'
            support_candidate_path.write_text(json.dumps(cand, indent=2, sort_keys=True) + '\n')
            entry['support_candidate_path'] = str(support_candidate_path)
            iterations.append(entry)
            print(f'  RULING FEASIBLE support candidate saved: {support_candidate_path}', flush=True)
            break

        if rq.get('status') == 'INFEASIBLE':
            shrink_records = []
            reusable = []
            # Query all proper subsets in increasing size; first ruling-infeasible size gives reusable obstructions.
            for r in range(1, len(high) + 1):
                any_inf = False
                for sub in itertools.combinations(high, r):
                    sub = tuple(sorted(int(x) for x in sub))
                    rq_sub = ruling_oracle.query(sub, args.k, time_limit=args.time_limit_shrink, workers=args.workers, capture_support=False)
                    bq_sub = base_oracle.query(sub, args.k, time_limit=args.time_limit_compare, workers=args.workers, capture_support=False)
                    can_sub = tuple(canonical_set(sub, stab_setwise))
                    rec = {
                        'subset': list(sub),
                        'size': r,
                        'canonical_setwise': list(can_sub),
                        'orbit_image_count_setwise': orbit_image_count(sub, stab_setwise),
                        'ruling_status': rq_sub.get('status'),
                        'ruling_solve_sec': rq_sub.get('solve_sec'),
                        'wang_only_status': bq_sub.get('status'),
                        'wang_only_solve_sec': bq_sub.get('solve_sec'),
                        'new_relative_to_imported_old_pairs': (r == 2 and can_sub not in old_pair_canonicals),
                        'ruling_strict_vs_wang_only': (rq_sub.get('status') == 'INFEASIBLE' and bq_sub.get('status') in FEAS),
                    }
                    shrink_records.append(rec)
                    if rq_sub.get('status') == 'INFEASIBLE':
                        any_inf = True
                        reusable.append(sub)
                if any_inf:
                    break
            feedback = []
            for sub in reusable if reusable else [tuple(high)]:
                can_sub = tuple(canonical_set(sub, stab_setwise))
                if len(sub) == 1:
                    hs = hyperedge_images(sub, stab_setwise, pt_to_i)
                    before = len(proved_hyperedges)
                    proved_hyperedges.update(hs)
                    feedback.append({'type': 'ruling_singleton_hyperedge', 'subset': list(sub), 'canonical': list(can_sub), 'new_hyperedges': len(proved_hyperedges)-before})
                elif len(sub) == 2:
                    imgs = all_images(sub, stab_setwise)
                    changed = add_pair_images(adj, pt_to_i, imgs)
                    ruling_new_pairs.add(can_sub)
                    # strictness is determined from shrink records.
                    strict = any(tuple(rec['canonical_setwise']) == can_sub and rec['ruling_strict_vs_wang_only'] for rec in shrink_records)
                    if strict:
                        ruling_strict_pairs.add(can_sub)
                    feedback.append({'type': 'ruling_pair_edge_removal', 'subset': list(sub), 'canonical': list(can_sub), 'images': len(imgs), 'edges_removed': changed, 'strict_vs_wang_only': strict})
                else:
                    hs = hyperedge_images(sub, stab_setwise, pt_to_i)
                    before = len(proved_hyperedges)
                    proved_hyperedges.update(hs)
                    feedback.append({'type': 'ruling_high_hyperedge', 'subset': list(sub), 'canonical': list(can_sub), 'new_hyperedges': len(proved_hyperedges)-before})
            entry['shrink_records'] = shrink_records
            entry['feedback'] = feedback
            iterations.append(entry)
            print(f"  ruling INFEASIBLE; feedback={feedback}", flush=True)
        else:
            # UNKNOWN/nonterminal: skip this exact high orbit only within this exploratory run.
            hs = hyperedge_images(high, stab_setwise, pt_to_i)
            before = len(temporary_skip_hyperedges)
            temporary_skip_hyperedges.update(hs)
            entry['temporary_skip_hyperedges_added'] = len(temporary_skip_hyperedges)-before
            entry['meaning'] = 'temporary skip is not proof evidence'
            iterations.append(entry)
            print('  ruling query unresolved; temporary skip only', flush=True)

    final_degrees = [a.bit_count() for a in adj]
    result = {
        'schema': 'rep2_k17_ruling_guided_v1',
        'problem': 'rep2 adjacent-pair exact-k17 mixed-rank ruling-aware guided clique test',
        'field': 'F2',
        'fixed_prefix': [1, 2],
        'exact_rank1_count': args.k,
        'target_high_rank_points': target_high,
        'old_singleton_sources': singleton_sources,
        'old_constraint_files': [str(p) for p in args.constraint_json],
        'old_constraint_source_count': len(edge_sources),
        'old_constraint_sources_head': edge_sources[:100],
        'pointwise_stabilizer_order': len(branch['stab_pair']),
        'setwise_stabilizer_order': len(stab_setwise),
        'vertices_after_old_singletons': n,
        'vertex_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in vertices).items())),
        'initial_edge_count_after_old_pairs': sum(initial_degrees)//2,
        'initial_degree_hist': dict(sorted(Counter(initial_degrees).items())),
        'ruling_meta': ruling_oracle.ruling_meta,
        'iterations': iterations,
        'ruling_new_pair_canonical_count': len(ruling_new_pairs),
        'ruling_new_pair_canonicals': [list(x) for x in sorted(ruling_new_pairs)],
        'ruling_strict_pair_canonical_count': len(ruling_strict_pairs),
        'ruling_strict_pair_canonicals': [list(x) for x in sorted(ruling_strict_pairs)],
        'final_edge_count_after_feedback': sum(final_degrees)//2,
        'final_degree_hist': dict(sorted(Counter(final_degrees).items())),
        'proved_hyperedges_active': len(proved_hyperedges),
        'temporary_skip_hyperedges_active': len(temporary_skip_hyperedges),
        'closed_by_graph': closed_by_graph,
        'graph_size_info': graph_size_info,
        'support_candidate_path': str(support_candidate_path) if support_candidate_path else None,
        'lut_meta_brief': {'coverage_ok': meta.get('coverage_ok'), 'conflict_count': meta.get('conflict_count'), 'subspace_count': meta.get('subspace_count')},
        'proof_status': 'CP-SAT skeleton execution evidence. Ruling-enabled exclusions need conversion to a proof-producing CNF/provenance object before theorem use; feasible support is only A-side occupation evidence.',
        'elapsed_sec': time.time() - t_all,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True, default=str) + '\n')
    print(json.dumps({
        'status': 'done',
        'iterations': len(iterations),
        'support_candidate_path': result['support_candidate_path'],
        'ruling_new_pairs': result['ruling_new_pair_canonical_count'],
        'ruling_strict_pairs': result['ruling_strict_pair_canonical_count'],
        'closed_by_graph': result['closed_by_graph'],
        'initial_edges': result['initial_edge_count_after_old_pairs'],
        'final_edges': result['final_edge_count_after_feedback'],
        'elapsed_sec': result['elapsed_sec'],
    }, sort_keys=True))


if __name__ == '__main__':
    main()
