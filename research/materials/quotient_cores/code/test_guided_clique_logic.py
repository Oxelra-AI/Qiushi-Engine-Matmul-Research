#!/usr/bin/env python3
"""Randomized brute-force tests for analysis guided clique helpers."""
from __future__ import annotations

import itertools
import random
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from guided_clique_oracle import find_clique_with_hyperedges, max_clique_size  # noqa: E402


def brute(adj, hyperedges, target=None):
    n = len(adj)
    best = []
    target_hit = None
    hypers = [set(h) for h in hyperedges]
    for r in range(n + 1):
        for comb in itertools.combinations(range(n), r):
            ok = True
            s = set(comb)
            for i, j in itertools.combinations(comb, 2):
                if not (adj[i] >> j) & 1:
                    ok = False
                    break
            if ok:
                for h in hypers:
                    if h.issubset(s):
                        ok = False
                        break
            if not ok:
                continue
            if r > len(best):
                best = list(comb)
            if target is not None and r == target and target_hit is None:
                target_hit = list(comb)
    return best, target_hit


def random_graph(n, p):
    adj = [0] * n
    for i in range(n):
        for j in range(i + 1, n):
            if random.random() < p:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
    return adj


def main():
    random.seed(260026)
    tested = 0
    for n in range(2, 10):
        for trial in range(200):
            p = random.random()
            adj = random_graph(n, p)
            hyperedges = []
            for r in (1, 2, 3):
                for comb in itertools.combinations(range(n), r):
                    if random.random() < 0.03:
                        hyperedges.append(tuple(comb))
            best, _ = brute(adj, hyperedges)
            got_size, got, exact = max_clique_size(adj, hyperedges, target_cap=None)
            if got_size != len(best) or not exact:
                raise AssertionError((n, trial, 'max', len(best), best, got_size, got, exact, hyperedges))
            for target in range(0, min(n, 5) + 1):
                _, hit = brute(adj, hyperedges, target=target)
                # Use identity-like dummy vertices/group; no banned canonicals.
                clique, stats = find_clique_with_hyperedges(
                    adj, target, hyperedges, set(), list(range(n)), [list(range(9))], max_nodes=1_000_000
                )
                if (hit is None) != (clique is None):
                    raise AssertionError((n, trial, 'target', target, hit, clique, stats, hyperedges, adj))
                if clique is not None and len(clique) != target:
                    raise AssertionError((n, trial, 'bad_size', target, clique))
            tested += 1
    print({'status': 'ok', 'random_graphs_tested': tested})


if __name__ == '__main__':
    main()
