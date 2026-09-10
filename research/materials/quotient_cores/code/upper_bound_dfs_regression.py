#!/usr/bin/env python3
"""analysis: regression tests for sound Wang-row domain propagation.

The mathematical constraint is only an upper bound |S∩R| <= cap for each row R.
Sound propagation may remove future points from a row once the row is saturated
(count == cap), and may reject only when a selected point would exceed a cap or
when too few selectable points remain globally. It must NOT reject merely because
there are too few remaining points to fill a row's unused capacity.

This script gives small brute-force-comparable examples exercising saturation,
branching and undo. It also demonstrates the exact false inference present in the
peer e11_domain_dfs.cpp implementation.
"""
from __future__ import annotations
import itertools, json, random
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

OUT = Path("data/domain_dfs_soundness")

@dataclass(frozen=True)
class Row:
    pts: Tuple[int, ...]
    cap: int


def feasible(S: Sequence[int], rows: Sequence[Row]) -> bool:
    st = set(S)
    return all(sum(1 for p in r.pts if p in st) <= r.cap for r in rows)


def brute(n: int, target: int, rows: Sequence[Row]) -> List[Tuple[int, ...]]:
    return [c for c in itertools.combinations(range(1, n + 1), target) if feasible(c, rows)]


def sound_dfs(n: int, target: int, rows: Sequence[Row]):
    """Small transparent DFS with trailed state and only upper-bound semantics."""
    pt_rows = [[] for _ in range(n + 1)]
    for i, r in enumerate(rows):
        for p in r.pts:
            pt_rows[p].append(i)
    domain = [False] + [True] * n
    counts = [0] * len(rows)
    selected: List[int] = []
    sols: List[Tuple[int, ...]] = []
    prune = {"over_cap": 0, "global_shortage": 0, "saturation_removals": 0, "calls": 0}

    def remove_point(q: int, removed: List[int]):
        if domain[q]:
            domain[q] = False
            removed.append(q)

    def rec(min_p: int):
        prune["calls"] += 1
        depth = len(selected)
        if depth == target:
            sols.append(tuple(selected))
            return
        need = target - depth
        avail = [p for p in range(min_p, n + 1) if domain[p]]
        if len(avail) < need:
            prune["global_shortage"] += 1
            return
        for p in avail:
            # After p, enough later selectable points must remain.
            if sum(1 for q in range(p + 1, n + 1) if domain[q]) < need - 1:
                break
            touched = []
            ok = True
            for ri in pt_rows[p]:
                if counts[ri] + 1 > rows[ri].cap:
                    ok = False
                    prune["over_cap"] += 1
                    break
                touched.append(ri)
            if not ok:
                continue
            removed: List[int] = []
            remove_point(p, removed)
            selected.append(p)
            for ri in touched:
                counts[ri] += 1
            # Saturated rows impose future exclusions only.
            for ri in touched:
                if counts[ri] == rows[ri].cap:
                    for q in rows[ri].pts:
                        if q != p and domain[q]:
                            prune["saturation_removals"] += 1
                            remove_point(q, removed)
            rec(p + 1)
            for ri in reversed(touched):
                counts[ri] -= 1
            selected.pop()
            for q in reversed(removed):
                domain[q] = True
    rec(1)
    return sols, prune


def flawed_rejects_toy_after_selecting_1():
    """Replicate only the peer's invalid small_remain < cap-count test on the toy."""
    # rows: R0={1,2}, cap1; R1={2,3}, cap2. Select 1 saturates R0 and removes 2.
    rows = [Row((1, 2), 1), Row((2, 3), 2)]
    small_count = [0, 0]
    small_remain = [2, 2]
    # select 1 increments row0 to cap, then removing point 2 decrements remains
    small_count[0] += 1
    removed_point = 2
    touched_by_2 = [0, 1]
    events = []
    rejected = False
    for ri in touched_by_2:
        small_remain[ri] -= 1
        bad = small_remain[ri] < rows[ri].cap - small_count[ri]
        events.append({
            "row": ri,
            "pts": rows[ri].pts,
            "cap": rows[ri].cap,
            "count": small_count[ri],
            "remain_after_removing_2": small_remain[ri],
            "invalid_test_rhs_cap_minus_count": rows[ri].cap - small_count[ri],
            "flawed_rejects_here": bad,
        })
        if bad:
            rejected = True
            break
    return {"rejected": rejected, "events": events}


def random_instances(seed=130917, trials=200, n=9, max_rows=8):
    rng = random.Random(seed)
    mismatches = []
    aggregate = {"trials": trials, "with_solutions": 0, "total_bruteforce_solutions": 0, "total_sound_solutions": 0}
    examples = []
    for t in range(trials):
        target = rng.randint(0, min(5, n))
        rows = []
        for _ in range(rng.randint(0, max_rows)):
            size = rng.randint(0, n)
            pts = tuple(sorted(rng.sample(range(1, n + 1), size)))
            cap = rng.randint(0, size) if size else 0
            rows.append(Row(pts, cap))
        b = brute(n, target, rows)
        s, stats = sound_dfs(n, target, rows)
        aggregate["total_bruteforce_solutions"] += len(b)
        aggregate["total_sound_solutions"] += len(s)
        if b:
            aggregate["with_solutions"] += 1
        if b != s:
            mismatches.append({"trial": t, "target": target, "rows": [r.__dict__ for r in rows], "brute": b[:20], "sound": s[:20], "stats": stats})
            break
        if len(examples) < 5 and stats["saturation_removals"] and stats["calls"] > 1:
            examples.append({"trial": t, "n": n, "target": target, "rows": [r.__dict__ for r in rows], "solutions": b[:10], "solution_count": len(b), "stats": stats})
    return aggregate | {"mismatches": mismatches, "examples_exercising_saturation_and_undo": examples}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    toy_rows = [Row((1, 2), 1), Row((2, 3), 2)]
    toy_brute = brute(3, 2, toy_rows)
    toy_sound, toy_stats = sound_dfs(3, 2, toy_rows)
    result = {
        "schema": "s0908_domain_dfs_soundness_v1",
        "semantics": "Rows are upper bounds |S∩R|<=cap. Saturated rows remove future points in R; unused capacity creates no obligation.",
        "toy": {
            "n": 3,
            "target": 2,
            "rows": [r.__dict__ for r in toy_rows],
            "bruteforce_solutions": toy_brute,
            "sound_dfs_solutions": toy_sound,
            "sound_stats": toy_stats,
            "peer_small_remain_test_simulation": flawed_rejects_toy_after_selecting_1(),
            "interpretation": "The feasible support (1,3) is lost if one rejects on small_remain < cap-count after saturation removes point 2.",
        },
        "random_bruteforce_comparison": random_instances(),
    }
    out = OUT / "upper_bound_dfs_regression.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
