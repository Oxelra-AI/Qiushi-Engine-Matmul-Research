#!/usr/bin/env python3
"""Conservative clique test from singleton/pair Wang skeleton evidence.

For a fixed branch and exact rank-1 count k, singleton exclusions remove HR
vertices.  Pair tests remove edges.  Any full support with the required number
of additional HR points must form a clique in the remaining graph: every pair
inside the selected HR set must have survived the pair relaxation.  If the
conservative graph (keeping FEASIBLE/OPTIMAL/UNKNOWN/missing pair classes as
edges) has clique number smaller than the required additional-HR count, the
k-level is closed at the same CP-SAT evidence level as the pair tests.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from general_singleton_pair_survey import build_branch_general  # noqa: E402
from precompute_skeleton_system import compute_stab_e11  # noqa: E402
from skeleton_oracle_joint_pilot import canonical_set  # noqa: E402


def max_clique_bitset(adj: list[int]):
    """Return (size, vertices) using branch and bound with greedy coloring."""
    n = len(adj)
    best: list[int] = []

    def color_sort(P: int):
        order = []
        colors = []
        U = P
        color = 0
        while U:
            color += 1
            Q = U
            while Q:
                v_bit = Q & -Q
                v = v_bit.bit_length() - 1
                Q ^= v_bit
                U ^= v_bit
                Q &= ~adj[v]
                order.append(v)
                colors.append(color)
        return order, colors

    def expand(R: list[int], P: int):
        nonlocal best
        if not P:
            if len(R) > len(best):
                best = R.copy()
            return
        order, colors = color_sort(P)
        for i in range(len(order) - 1, -1, -1):
            v = order[i]
            if len(R) + colors[i] <= len(best):
                return
            bit = 1 << v
            if not (P & bit):
                continue
            expand(R + [v], P & adj[v])
            P &= ~bit
            if len(R) + P.bit_count() <= len(best):
                return

    expand([], (1 << n) - 1)
    return len(best), best


def find_k_clique(adj: list[int], target: int):
    n = len(adj)
    found: list[int] | None = None

    def rec(chosen: list[int], cand: int):
        nonlocal found
        if found is not None:
            return
        if len(chosen) == target:
            found = chosen.copy()
            return
        if len(chosen) + cand.bit_count() < target:
            return
        # choose vertices in increasing order; intersect candidates with neighbors
        while cand and found is None:
            b = cand & -cand
            v = b.bit_length() - 1
            cand ^= b
            rec(chosen + [v], cand & adj[v])

    rec([], (1 << n) - 1)
    return found


def load_k_entry(path: Path, k: int):
    d = json.loads(path.read_text())
    for e in d.get('k_results', []):
        if int(e.get('k')) == int(k):
            return d, e
    raise ValueError(f'k={k} not found in {path}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--descent-json', type=Path, required=True)
    ap.add_argument('--k', type=int, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--rank-s', type=int, default=20)
    args = ap.parse_args()

    t0 = time.time()
    descent, entry = load_k_entry(args.descent_json, args.k)
    rep = int(descent['branch_rep'])
    _, stab_e11 = compute_stab_e11()
    branch = build_branch_general(rep, stab_e11)
    survivor_orbs = sorted(set(int(x) for x in entry.get('singleton_feasible_orbs', [])) |
                           set(int(x) for x in entry.get('singleton_unknown_orbs', [])))
    surviving_pts = []
    for orb in branch['hr_orbits']:
        if int(orb['rep']) in survivor_orbs:
            surviving_pts.extend(int(p) for p in orb['members'])
    surviving_pts = sorted(surviving_pts)
    n = len(surviving_pts)
    pt_to_i = {p: i for i, p in enumerate(surviving_pts)}
    pair_status = {}
    status_hist = Counter()
    for r in entry.get('pair_results', []):
        can = tuple(int(x) for x in r.get('canonical', []))
        st = r.get('status', 'MISSING')
        if len(can) == 2:
            pair_status[can] = st
            status_hist[st] += 1
    allowed_status = {'OPTIMAL', 'FEASIBLE', 'UNKNOWN', 'MODEL_INVALID', 'ERROR'}
    adj = [0] * n
    pair_class_hist = Counter()
    missing_class_count = 0
    checked_pairs = 0
    for a in range(n):
        p = surviving_pts[a]
        for b in range(a + 1, n):
            q = surviving_pts[b]
            can = canonical_set([p, q], branch['stab_pair'])
            st = pair_status.get(can)
            if st is None:
                missing_class_count += 1
                allow = True  # conservative: missing pair class is unresolved
                label = 'MISSING'
            else:
                allow = st in allowed_status
                label = st
            pair_class_hist[label] += 1
            checked_pairs += 1
            if allow:
                adj[a] |= 1 << b
                adj[b] |= 1 << a
    degrees = [x.bit_count() for x in adj]
    fixed_hr_perm = list(branch.get('fixed_hr_permanent', []))
    required_additional_hr = args.rank_s - args.k - len(fixed_hr_perm)
    witness = find_k_clique(adj, required_additional_hr) if required_additional_hr > 0 else []
    if witness is None:
        omega, best_idx = max_clique_bitset(adj)
    else:
        omega, best_idx = len(witness), witness
    best_pts = [surviving_pts[i] for i in best_idx]
    payload = {
        'problem': 'conservative HR pair-survivor clique test',
        'field': 'F2',
        'rank_s': args.rank_s,
        'branch_rep': rep,
        'rep_rank': branch['rep_rank'],
        'k': args.k,
        'fixed_rank1': branch['fixed_rank1'],
        'fixed_hr_permanent': fixed_hr_perm,
        'required_total_hr': args.rank_s - args.k,
        'required_additional_hr': required_additional_hr,
        'survivor_orbits': survivor_orbs,
        'surviving_hr_points': n,
        'pair_class_status_hist': dict(sorted(status_hist.items())),
        'actual_pair_status_hist': dict(sorted(pair_class_hist.items())),
        'missing_pair_class_count_over_actual_pairs': missing_class_count,
        'actual_pairs_checked': checked_pairs,
        'edge_count': sum(degrees) // 2,
        'degree_hist': dict(sorted(Counter(degrees).items())),
        'max_degree': max(degrees, default=0),
        'clique_size_lower_or_exact': omega,
        'clique_witness_points': best_pts,
        'target_clique_found': witness is not None,
        'closed_by_pair_graph': witness is None and omega < required_additional_hr,
        'closure_meaning': 'If closed_by_pair_graph is true, every required high-rank set contains a CP-SAT-infeasible pair class; formal use still requires certificates for the pair exclusions and singleton eliminations used.',
        'elapsed_sec': time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: payload[k] for k in ['branch_rep','k','required_additional_hr','surviving_hr_points','edge_count','max_degree','clique_size_lower_or_exact','target_clique_found','closed_by_pair_graph','elapsed_sec']}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
