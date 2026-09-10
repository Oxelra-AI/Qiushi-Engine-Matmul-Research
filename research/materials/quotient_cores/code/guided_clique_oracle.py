#!/usr/bin/env python3
"""Guided compatibility-graph search for Wang skeleton supports.

For a fixed Wang support branch (E11 plus a second representative) and exact
rank-1 count k, a length-20 A-support has exactly

    20 - k - len(fixed_hr_permanent)

additional higher-rank A-points.  Singleton/pair/higher-subset infeasibility
from the exact-k skeleton oracle gives necessary exclusions.  A full higher-rank
set must therefore be a clique in the conservative graph of surviving pairs and
must avoid all proved forbidden hyperedges.  This script uses that graph to pick
complete high sets, queries the complete fixed-high skeleton oracle, and feeds
infeasible shrinks back as new graph obstructions.

Everything produced here is CP-SAT/skeleton evidence until independently
certified.  The implementation is deliberately conservative: non-INFEASIBLE
statuses remain possible; UNKNOWN full-high queries are only temporary skips and
can never participate in a graph-closure conclusion.
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, Sequence

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from general_singleton_pair_survey import GeneralExactKOracle, build_branch_general  # noqa: E402
from precompute_skeleton_system import compute_stab_e11, pack_bases_numpy  # noqa: E402
from skeleton_oracle_joint_pilot import canonical_set, load_lut, orbit_image_count  # noqa: E402
from wang_capacity_lazy import matrix_rank_of_mask, transform_mask  # noqa: E402

FEASIBLE_STATUSES = {'OPTIMAL', 'FEASIBLE'}


def load_json(path: Path | None) -> dict | None:
    if path is None:
        return None
    if not path.exists() or path.stat().st_size == 0:
        raise FileNotFoundError(f'{path} missing or empty')
    return json.loads(path.read_text())


def _rows_to_survivor_orbits(rows: list[dict]) -> list[int]:
    """Only explicit INFEASIBLE removes an orbit; everything else survives."""
    survivors: list[int] = []
    seen: set[int] = set()
    for r in rows:
        if 'orbit_rep' not in r:
            continue
        rep = int(r['orbit_rep'])
        if rep in seen:
            continue
        seen.add(rep)
        if r.get('status') != 'INFEASIBLE':
            survivors.append(rep)
    return sorted(survivors)


def survivor_orbits_from_json(data: dict, k: int, branch: dict) -> tuple[list[int], dict]:
    """Conservatively parse singleton survivors and return diagnostics.

    Early files sometimes contain stale/empty summary survivor fields.  This
    parser therefore prefers per-orbit solver rows and ignores summary fields
    when rows are available.  A summary is used only as a fallback.
    """
    source = 'unknown'
    rows: list[dict] | None = None
    if 'k_results' in data:
        for entry in data['k_results']:
            if int(entry.get('k')) == int(k):
                if 'singleton_results' in entry:
                    rows = entry.get('singleton_results', [])
                    source = 'k_results.singleton_results'
                else:
                    ph_surv = sorted(set(int(x) for x in entry.get('singleton_feasible_orbs', [])) |
                                     set(int(x) for x in entry.get('singleton_unknown_orbs', [])))
                    rows = None
                    source = 'k_results.summary_fields'
                    out = ph_surv
                    break
        else:
            raise ValueError(f'k={k} not found in survivor JSON')
    elif 'phase1_results' in data:
        rows = data.get('phase1_results', [])
        source = 'phase1_results'
    elif 'singleton_results' in data:
        rows = data.get('singleton_results', [])
        source = 'singleton_results'
    else:
        rows = None

    if rows is not None:
        out = _rows_to_survivor_orbits(rows)
        row_count = len(rows)
    else:
        row_count = 0
        if source == 'unknown':
            if 'phase1_summary' in data:
                ph = data['phase1_summary']
                source = 'phase1_summary_fallback'
                out = sorted(set(int(x) for x in ph.get('feasible_reps', [])) |
                             set(int(x) for x in ph.get('unknown_reps', [])) |
                             set(int(x) for x in ph.get('surviving_reps', [])) |
                             set(int(x) for x in ph.get('survivor_reps', [])))
            elif 'singleton_summary' in data:
                ph = data['singleton_summary']
                source = 'singleton_summary_fallback'
                out = sorted(set(int(x) for x in ph.get('feasible_reps', [])) |
                             set(int(x) for x in ph.get('unknown_reps', [])) |
                             set(int(x) for x in ph.get('survivor_reps', [])))
            else:
                raise ValueError('unrecognized survivor JSON format')

    branch_reps = {int(o['rep']) for o in branch['hr_orbits']}
    bad = [x for x in out if x not in branch_reps]
    if bad:
        raise ValueError(f'survivor orbits not in branch {branch["rep"]}: {bad[:10]}')
    diag = {
        'source': source,
        'row_count': row_count,
        'survivor_orbit_count': len(out),
        'survivor_orbits': out,
        'meaning': 'rebuilt from rows when possible; only INFEASIBLE is eliminated',
    }
    return out, diag


def pair_statuses_from_json(data: dict, k: int | None = None) -> list[dict]:
    if data is None:
        return []
    if 'pair_results' in data:
        return list(data.get('pair_results', []))
    if 'k_results' in data:
        out: list[dict] = []
        for entry in data['k_results']:
            if k is None or int(entry.get('k')) == int(k):
                out.extend(entry.get('pair_results', []))
        return out
    return []


def all_images(points: Sequence[int], group: Sequence[Sequence[int]]) -> list[tuple[int, ...]]:
    return sorted({tuple(sorted(transform_mask(int(p), g) for p in points)) for g in group})


def build_vertices(branch: dict, survivor_orbs: Sequence[int]) -> list[int]:
    survivor_set = set(int(x) for x in survivor_orbs)
    pts: list[int] = []
    for orb in branch['hr_orbits']:
        if int(orb['rep']) in survivor_set:
            pts.extend(int(p) for p in orb['members'])
    return sorted(set(pts))


def remove_edge(adj: list[int], i: int, j: int) -> bool:
    old = bool(adj[i] & (1 << j))
    adj[i] &= ~(1 << j)
    adj[j] &= ~(1 << i)
    return old


def add_forbidden_pair_images(adj: list[int], pt_to_i: dict[int, int], images: Iterable[Sequence[int]]) -> int:
    changed = 0
    for img in images:
        if len(img) != 2:
            continue
        p, q = int(img[0]), int(img[1])
        if p in pt_to_i and q in pt_to_i and p != q:
            if remove_edge(adj, pt_to_i[p], pt_to_i[q]):
                changed += 1
    return changed


def hyperedge_images_to_indices(points: Sequence[int], group, pt_to_i: dict[int, int]) -> list[tuple[int, ...]]:
    idx_sets = []
    for img in all_images(points, group):
        if all(int(p) in pt_to_i for p in img):
            idx_sets.append(tuple(sorted(pt_to_i[int(p)] for p in img)))
    return sorted(set(idx_sets))


def greedy_order_vertices(adj: list[int], active: int) -> list[int]:
    vs: list[int] = []
    x = active
    while x:
        b = x & -x
        i = b.bit_length() - 1
        x ^= b
        vs.append(i)
    return sorted(vs, key=lambda i: (-((adj[i] & active).bit_count()), i))


def find_clique_with_hyperedges(adj: list[int], target: int, forbidden_hyperedges: Sequence[tuple[int, ...]],
                                banned_canonicals: set[tuple[int, ...]], vertices: list[int], group,
                                max_nodes: int = 2_000_000) -> tuple[list[int] | None, dict]:
    """Find one target clique avoiding hyperedges and already tested orbits."""
    hyper_by_v: dict[int, list[tuple[int, ...]]] = defaultdict(list)
    for h in forbidden_hyperedges:
        for v in h:
            hyper_by_v[v].append(h)
    nodes = 0
    prunes = Counter()
    found: list[int] | None = None

    def partial_violates(chosen: list[int], v: int) -> bool:
        s = set(chosen)
        s.add(v)
        for h in hyper_by_v.get(v, []):
            if set(h).issubset(s):
                return True
        return False

    def rec(chosen: list[int], cand: int) -> None:
        nonlocal nodes, found
        nodes += 1
        if found is not None or nodes > max_nodes:
            return
        if len(chosen) == target:
            can = tuple(canonical_set([vertices[i] for i in chosen], group))
            if can in banned_canonicals:
                prunes['tested_canonical'] += 1
                return
            found = chosen.copy()
            return
        if len(chosen) + cand.bit_count() < target:
            prunes['too_few_candidates'] += 1
            return
        for v in greedy_order_vertices(adj, cand):
            b = 1 << v
            if not (cand & b):
                continue
            if partial_violates(chosen, v):
                prunes['hyperedge'] += 1
                cand &= ~b
                continue
            rec(chosen + [v], cand & adj[v])
            cand &= ~b
            if found is not None or nodes > max_nodes:
                return
            if len(chosen) + cand.bit_count() < target:
                prunes['too_few_after_branch'] += 1
                return

    rec([], (1 << len(adj)) - 1)
    return found, {'nodes': nodes, 'prunes': dict(prunes), 'hit_node_limit': nodes > max_nodes}


def max_clique_size(adj: list[int], forbidden_hyperedges: Sequence[tuple[int, ...]], target_cap: int | None = None) -> tuple[int, list[int], bool]:
    """Return clique size reached; exact only if target_cap is None or result < target_cap."""
    best: list[int] = []
    reached_cap = False
    hyper_by_v: dict[int, list[tuple[int, ...]]] = defaultdict(list)
    for h in forbidden_hyperedges:
        for v in h:
            hyper_by_v[v].append(h)

    def partial_violates(chosen: list[int], v: int) -> bool:
        s = set(chosen)
        s.add(v)
        for h in hyper_by_v.get(v, []):
            if set(h).issubset(s):
                return True
        return False

    def rec(chosen: list[int], cand: int) -> None:
        nonlocal best, reached_cap
        if len(chosen) > len(best):
            best = chosen.copy()
            if target_cap is not None and len(best) >= target_cap:
                reached_cap = True
                return
        if reached_cap:
            return
        if len(chosen) + cand.bit_count() <= len(best):
            return
        for v in greedy_order_vertices(adj, cand):
            b = 1 << v
            if not (cand & b):
                continue
            if partial_violates(chosen, v):
                cand &= ~b
                continue
            rec(chosen + [v], cand & adj[v])
            cand &= ~b
            if reached_cap or len(chosen) + cand.bit_count() <= len(best):
                return

    rec([], (1 << len(adj)) - 1)
    exact = not reached_cap
    return len(best), best, exact


def shrink_obstruction(oracle: GeneralExactKOracle, high: Sequence[int], k: int, *, time_limit: float, workers: int) -> dict:
    """Find infeasible subsets of a rejected high set at first detected size."""
    high = sorted(int(x) for x in high)
    infeasible_at_first_size: list[tuple[int, ...]] = []
    queries = []
    for r in range(1, len(high) + 1):
        for sub in itertools.combinations(high, r):
            if any(set(old).issubset(sub) for old in infeasible_at_first_size):
                continue
            res = oracle.query(list(sub), k, time_limit=time_limit, workers=workers, capture_support=False)
            q = {
                'subset': list(sub),
                'canonical': list(canonical_set(sub, oracle.branch['stab_pair'])),
                'orbit_image_count': orbit_image_count(sub, oracle.branch['stab_pair']),
                'size': r,
                'status': res.get('status'),
                'build_sec': res.get('build_sec'),
                'solve_sec': res.get('solve_sec'),
                'constraints_added': res.get('constraints_added'),
                'empty_constraints': res.get('empty_constraints'),
            }
            queries.append(q)
            if res.get('status') == 'INFEASIBLE':
                infeasible_at_first_size.append(tuple(sub))
        if infeasible_at_first_size:
            break
    reusable = [list(x) for x in infeasible_at_first_size] if infeasible_at_first_size else [high]
    return {
        'high': high,
        'infeasible_subsets_at_first_detected_size': [list(x) for x in infeasible_at_first_size],
        'reusable_infeasible_subsets': reusable,
        'queries': queries,
        'meaning': 'Subsets are safe INFEASIBLE feedback. If earlier smaller subsets returned UNKNOWN, they are not necessarily inclusion-minimal.',
    }


def candidate_checks(branch: dict, k: int, additional_high: Sequence[int], support: Sequence[int] | None) -> dict:
    if support is None:
        return {'ok': False, 'reason': 'no_support'}
    s = [int(x) for x in support]
    fixed_rank1 = set(int(x) for x in branch['fixed_rank1'])
    fixed_hr = set(int(x) for x in branch.get('fixed_hr_permanent', []))
    add_high = set(int(x) for x in additional_high)
    rank_hist = Counter(matrix_rank_of_mask(p) for p in s)
    problems = []
    if len(s) != 20:
        problems.append(f'support length {len(s)} != 20')
    if len(set(s)) != len(s):
        problems.append('duplicate support points')
    if any(p < 1 or p > 511 for p in s):
        problems.append('point outside projective mask range')
    if sum(1 for p in s if matrix_rank_of_mask(p) == 1) != int(k):
        problems.append('rank1 count mismatch')
    if sum(1 for p in s if matrix_rank_of_mask(p) > 1) != 20 - int(k):
        problems.append('higher-rank count mismatch')
    if not fixed_rank1.issubset(set(s)):
        problems.append('fixed rank1 points missing')
    if not fixed_hr.issubset(set(s)):
        problems.append('fixed permanent high points missing')
    if not add_high.issubset(set(s)):
        problems.append('queried additional high points missing')
    if set(s) & set(branch['excluded']):
        problems.append('support intersects excluded earlier second-orbit points')
    return {'ok': not problems, 'problems': problems, 'rank_hist': dict(sorted(rank_hist.items()))}


def write_support_candidate(path: Path, *, branch: dict, k: int, high: Sequence[int], query: dict) -> None:
    support = query.get('support_all')
    checks = candidate_checks(branch, k, high, support)
    if not checks['ok']:
        raise ValueError(f'invalid support candidate checks: {checks}')
    payload = {
        'problem': 'full Wang-LUT A-support candidate from guided clique oracle',
        'field': 'F2',
        'rank_s': 20,
        'branch_rep': branch['rep'],
        'rep_rank': branch['rep_rank'],
        'fixed_rank1': branch['fixed_rank1'],
        'fixed_hr_permanent': branch.get('fixed_hr_permanent', []),
        'exact_rank1_count': k,
        'fixed_high_tested': sorted(int(x) for x in high),
        'query_status': query.get('status'),
        'support': support,
        'candidate_checks': checks,
        'meaning': 'Candidate satisfies the compressed full Wang occupation table as implemented; independently scan against the full LUT before using it.',
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rep', type=int, required=True)
    ap.add_argument('--k', type=int, required=True)
    ap.add_argument('--survivor-json', type=Path, required=True)
    ap.add_argument('--forbidden-json', type=Path, default=Path('data/skeleton_joint_pilot/forbidden_high_constraints.json'))
    ap.add_argument('--pair-json', type=Path, action='append', default=[])
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--candidate-out-dir', type=Path, default=None)
    ap.add_argument('--iterations', type=int, default=5)
    ap.add_argument('--time-limit-full', type=float, default=60.0)
    ap.add_argument('--time-limit-shrink', type=float, default=30.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--max-search-nodes', type=int, default=2_000_000)
    args = ap.parse_args()

    t_all = time.time()
    _, stab_e11 = compute_stab_e11()
    branch = build_branch_general(args.rep, stab_e11)
    min_valid_k = len(branch['fixed_rank1'])
    max_valid_k = 20 - len(branch.get('fixed_hr_permanent', []))
    if not (min_valid_k <= int(args.k) <= max_valid_k):
        raise ValueError(f'k={args.k} outside valid range [{min_valid_k},{max_valid_k}] for branch rep {args.rep}')
    target_high = 20 - int(args.k) - len(branch.get('fixed_hr_permanent', []))

    survivor_data = load_json(args.survivor_json)
    survivor_orbs, survivor_parse = survivor_orbits_from_json(survivor_data, args.k, branch)
    vertices = build_vertices(branch, survivor_orbs)
    pt_to_i = {p: i for i, p in enumerate(vertices)}
    n = len(vertices)

    adj = [(1 << n) - 1 for _ in range(n)]
    for i in range(n):
        adj[i] &= ~(1 << i)

    edge_sources = []
    pair_edges_removed = 0
    proved_hyperedges: list[tuple[int, ...]] = []
    temporary_skip_hyperedges: list[tuple[int, ...]] = []

    forb = load_json(args.forbidden_json) if args.forbidden_json and args.forbidden_json.exists() else {'constraints': []}
    for c in forb.get('constraints', []):
        if int(c.get('branch_second_rep')) != int(args.rep):
            continue
        if 'source_full_high_status' in c and c.get('source_full_high_status') != 'INFEASIBLE':
            edge_sources.append({'source': c.get('source'), 'skipped': 'source_full_high_status_not_infeasible', 'constraint': c.get('canonical_subset')})
            continue
        if 'exact_rank1_count' not in c:
            edge_sources.append({'source': c.get('source', 'forbidden_json'), 'skipped': 'missing_exact_rank1_count', 'constraint': c.get('canonical_subset')})
            continue
        k0 = int(c['exact_rank1_count'])
        if k0 < min_valid_k or k0 > int(args.k):
            edge_sources.append({'source': c.get('source', 'forbidden_json'), 'skipped': 'invalid_or_nonmonotone_k0', 'k0': k0, 'constraint': c.get('canonical_subset')})
            continue
        subset = [int(x) for x in c.get('canonical_subset', c.get('source_subset', []))]
        imgs = c.get('orbit_images') or all_images(subset, branch['stab_pair'])
        if len(subset) == 1:
            for img in imgs:
                if len(img) == 1 and int(img[0]) in pt_to_i:
                    proved_hyperedges.append((pt_to_i[int(img[0])],))
            edge_sources.append({'source': c.get('source', 'forbidden_json_singleton'), 'k0': k0, 'type': 'singleton', 'canonical_subset': subset, 'images_used': len(imgs)})
        elif len(subset) == 2:
            changed = add_forbidden_pair_images(adj, pt_to_i, imgs)
            pair_edges_removed += changed
            edge_sources.append({'source': c.get('source', 'forbidden_json_pair'), 'k0': k0, 'type': 'pair', 'canonical_subset': subset, 'images_used': len(imgs), 'edges_removed': changed})
        else:
            hs = hyperedge_images_to_indices(subset, branch['stab_pair'], pt_to_i)
            proved_hyperedges.extend(hs)
            edge_sources.append({'source': c.get('source', 'forbidden_json_hyperedge'), 'k0': k0, 'type': 'hyperedge', 'canonical_subset': subset, 'images_used': len(hs)})

    for ppath in args.pair_json:
        pdata = load_json(ppath)
        if pdata is None:
            continue
        if 'k' in pdata:
            pk = int(pdata['k'])
        elif 'k_results' in pdata:
            pk = int(args.k)
        else:
            raise ValueError(f'pair-json {ppath} has no k or k_results; refusing to infer k0')
        if pk < min_valid_k or pk > int(args.k):
            edge_sources.append({'source': str(ppath), 'skipped': 'invalid_or_nonmonotone_k0', 'k0': pk})
            continue
        for r in pair_statuses_from_json(pdata, args.k):
            if r.get('status') != 'INFEASIBLE':
                continue
            can = [int(x) for x in r.get('canonical', [])]
            if len(can) != 2:
                continue
            imgs = all_images(can, branch['stab_pair'])
            pair_edges_removed += add_forbidden_pair_images(adj, pt_to_i, imgs)
        edge_sources.append({'source': str(ppath), 'k0': pk, 'status_used': 'INFEASIBLE_pairs'})

    singleton_forbidden = sorted(set(h[0] for h in proved_hyperedges if len(h) == 1))
    for i in singleton_forbidden:
        for j in range(n):
            if i != j:
                remove_edge(adj, i, j)
        adj[i] = 0
    proved_hyperedges = sorted(set(tuple(h) for h in proved_hyperedges))

    print('Loading LUT...', flush=True)
    lut, meta = load_lut(args.lut)
    keys = list(lut.keys())
    bases, dims, lbs = pack_bases_numpy(lut)
    oracle = GeneralExactKOracle(branch=branch, bases=bases, lbs=lbs, keys=keys, rank_s=20)

    tested_canonicals: set[tuple[int, ...]] = set()
    iterations = []
    support_candidate_path = None
    closed_by_graph = False
    graph_size_reached = None
    graph_witness = None
    graph_size_exact = None

    for it in range(1, args.iterations + 1):
        active_hyperedges = sorted(set(proved_hyperedges).union(temporary_skip_hyperedges))
        clique_idx, search_stats = find_clique_with_hyperedges(
            adj, target_high, active_hyperedges, tested_canonicals, vertices, branch['stab_pair'],
            max_nodes=args.max_search_nodes,
        )
        if clique_idx is None:
            omega, best_idx, exact = max_clique_size(adj, proved_hyperedges, target_cap=target_high)
            graph_size_reached = omega
            graph_witness = [vertices[i] for i in best_idx]
            graph_size_exact = exact
            closed_by_graph = exact and omega < target_high
            iterations.append({
                'iteration': it,
                'event': 'no_target_clique_found',
                'search_stats_with_temporary_skips': search_stats,
                'clique_size_reached_using_only_proved_exclusions': omega,
                'clique_size_exact': exact,
                'clique_witness_points': graph_witness,
                'closed_by_graph': closed_by_graph,
                'meaning': 'closed_by_graph is true only if the proved-exclusion graph was searched completely and has clique size below target.',
            })
            break

        high = sorted(vertices[i] for i in clique_idx)
        can_high = tuple(canonical_set(high, branch['stab_pair']))
        tested_canonicals.add(can_high)
        print(f'Iteration {it}: testing clique {high} canonical {list(can_high)}', flush=True)
        q = oracle.query(high, args.k, time_limit=args.time_limit_full, workers=args.workers, capture_support=True)
        entry = {
            'iteration': it,
            'event': 'full_high_query',
            'high': high,
            'canonical_high': list(can_high),
            'orbit_image_count': orbit_image_count(high, branch['stab_pair']),
            'query_status': q.get('status'),
            'query_build_sec': q.get('build_sec'),
            'query_solve_sec': q.get('solve_sec'),
            'query_constraints_added': q.get('constraints_added'),
            'query_empty_constraints': q.get('empty_constraints'),
            'search_stats': search_stats,
        }
        if q.get('status') in FEASIBLE_STATUSES:
            checks = candidate_checks(branch, args.k, high, q.get('support_all'))
            entry['support_all'] = q.get('support_all')
            entry['candidate_checks'] = checks
            if checks['ok'] and args.candidate_out_dir is not None:
                support_candidate_path = args.candidate_out_dir / f'rep{args.rep:03d}_k{args.k:02d}_iter{it}_support_candidate.json'
                write_support_candidate(support_candidate_path, branch=branch, k=args.k, high=high, query=q)
                entry['support_candidate_path'] = str(support_candidate_path)
            iterations.append(entry)
            print(f'  FEASIBLE full support candidate: {support_candidate_path}', flush=True)
            break
        if q.get('status') == 'INFEASIBLE':
            shrink = shrink_obstruction(oracle, high, args.k, time_limit=args.time_limit_shrink, workers=args.workers)
            entry['shrink'] = shrink
            feedback = []
            for sub0 in shrink.get('reusable_infeasible_subsets', []):
                sub = sorted(int(x) for x in sub0)
                if len(sub) == 1:
                    imgs = all_images(sub, branch['stab_pair'])
                    affected = 0
                    for img in imgs:
                        if len(img) == 1 and int(img[0]) in pt_to_i:
                            vi = pt_to_i[int(img[0])]
                            proved_hyperedges.append((vi,))
                            for j in range(n):
                                if vi != j and remove_edge(adj, vi, j):
                                    affected += 1
                            adj[vi] = 0
                    proved_hyperedges = sorted(set(proved_hyperedges))
                    feedback.append({'type': 'singleton_vertex_removal', 'subset': sub, 'images': len(imgs), 'edges_removed': affected})
                elif len(sub) == 2:
                    imgs = all_images(sub, branch['stab_pair'])
                    changed = add_forbidden_pair_images(adj, pt_to_i, imgs)
                    pair_edges_removed += changed
                    feedback.append({'type': 'pair_edge_removal', 'subset': sub, 'canonical': list(canonical_set(sub, branch['stab_pair'])), 'images': len(imgs), 'edges_removed': changed})
                else:
                    hs = hyperedge_images_to_indices(sub, branch['stab_pair'], pt_to_i)
                    before = len(proved_hyperedges)
                    proved_hyperedges = sorted(set(proved_hyperedges).union(hs))
                    feedback.append({'type': 'higher_order_hyperedge', 'subset': sub, 'canonical': list(canonical_set(sub, branch['stab_pair'])), 'images': len(hs), 'new_hyperedges': len(proved_hyperedges) - before})
            entry['feedback'] = feedback
            iterations.append(entry)
            print(f'  INFEASIBLE; feedback {feedback}', flush=True)
        else:
            imgs = hyperedge_images_to_indices(high, branch['stab_pair'], pt_to_i)
            before = len(temporary_skip_hyperedges)
            temporary_skip_hyperedges = sorted(set(temporary_skip_hyperedges).union(imgs))
            entry['unknown_handling'] = 'Full high-set status remains unresolved; this orbit is only temporarily skipped for this run and never used for final closure.'
            entry['temporary_hyperedges_added'] = len(temporary_skip_hyperedges) - before
            iterations.append(entry)
            print('  unresolved full query; temporarily skipping its orbit', flush=True)

    degrees = [a.bit_count() for a in adj]
    payload = {
        'problem': 'guided compatibility graph to full skeleton oracle',
        'field': 'F2',
        'rank_s': 20,
        'branch_rep': args.rep,
        'rep_rank': branch['rep_rank'],
        'k': args.k,
        'fixed_rank1': branch['fixed_rank1'],
        'fixed_hr_permanent': branch.get('fixed_hr_permanent', []),
        'target_additional_high_rank_points': target_high,
        'survivor_parse': survivor_parse,
        'survivor_orbits': survivor_orbs,
        'vertex_count_initial': n,
        'vertex_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in vertices).items())),
        'known_pair_edges_removed': pair_edges_removed,
        'edge_sources': edge_sources[:500],
        'proved_hyperedges_active': len(proved_hyperedges),
        'temporary_skip_hyperedges_active': len(temporary_skip_hyperedges),
        'degree_hist_after_feedback': dict(sorted(Counter(degrees).items())),
        'edge_count_after_feedback': sum(degrees) // 2,
        'closed_by_graph': closed_by_graph,
        'clique_size_reached_using_only_proved_exclusions': graph_size_reached,
        'clique_size_exact_if_below_target': graph_size_exact,
        'clique_witness_if_computed': graph_witness,
        'support_candidate_path': str(support_candidate_path) if support_candidate_path else None,
        'iterations': iterations,
        'proof_status': 'CP-SAT skeleton evidence only. Any exclusion needs certified singleton/pair/hyperedge implications or a checked original-variable proof; any support candidate needs independent full-LUT scan and then B/C/decomposition work.',
        'lut_meta_brief': {'coverage_ok': meta.get('coverage_ok'), 'conflict_count': meta.get('conflict_count'), 'subspace_count': meta.get('subspace_count')},
        'elapsed_sec': time.time() - t_all,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True, default=str) + '\n')
    print(json.dumps({
        'branch_rep': payload['branch_rep'],
        'k': payload['k'],
        'target_high': target_high,
        'vertex_count': n,
        'support_candidate_path': payload['support_candidate_path'],
        'closed_by_graph': payload['closed_by_graph'],
        'iterations': len(iterations),
        'edge_count_after_feedback': payload['edge_count_after_feedback'],
        'proved_hyperedges_active': payload['proved_hyperedges_active'],
        'temporary_skip_hyperedges_active': payload['temporary_skip_hyperedges_active'],
        'elapsed_sec': payload['elapsed_sec'],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
