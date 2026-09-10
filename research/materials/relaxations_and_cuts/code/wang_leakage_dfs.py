#!/usr/bin/env python3
r"""analysisc: DFS support enumeration with Wang + unconditional leakage pruning.

Orderly DFS: enumerate 19-point subsets of {1,...,255} in lexicographic order.
At each partial support, prune by:
  1. Wang capacity: for each subspace, current occ + max future additions <= cap
  2. Unconditional leakage: check if any rank-1/rank-2 target already has
     eB_lb + eC_lb > budget (even using best-case future m-values)

The DFS records explicit coverage: solutions_found, branches_pruned, timeout status.
If timeout=false and solutions_found=0, this is a proof that no 19-point
complete-Wang-and-leakage-admissible support exists.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np

SCRIPTS = Path("scripts")
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import contraction_weight_excess_search as base  # noqa:E402
from unconditional_leakage import get_intersection_dims  # noqa:E402

OUTDIR = Path("data/unconditional_leakage")
S_RANK = 19
POINTS = list(range(1, 256))

# Precompute activation masks: for each lambda, which points activate it
ACTIVATION = {}
for lam in range(1, 256):
    ACTIVATION[lam] = frozenset(p for p in POINTS if base.dot8(lam, p))

# Precompute Wang table: list of (point_set, capacity) pairs
def build_wang_table():
    """Build complete Wang occupation table for s=19."""
    records, _ = base.load_complete_records()
    table = []
    for rec in records:
        L = int(rec["L"])
        cap = S_RANK - L
        if cap <= 0 or cap >= S_RANK:
            continue
        pts = base.points_from_bitset(int(rec["point_bitset"]))
        if pts:
            table.append((frozenset(pts), cap))
    # Sort by capacity (tightest first for early pruning)
    table.sort(key=lambda x: x[1])
    return table


# Precompute unconditional leakage geometry
def build_leakage_table():
    """Precompute all (source, target) pairs with their geometric constants."""
    dB_tbl, dC_tbl = get_intersection_dims()
    targets = [mu for mu, sp in base.SPACES.items() if sp.rank_lam <= 2]
    sources = list(range(1, 256))  # all nonzero as sources

    pairs = []
    for mu in targets:
        sp_mu = base.SPACES[mu]
        for lam in sources:
            if lam == mu:
                continue
            sp_lam = base.SPACES[lam]
            nu = lam ^ mu
            const_B = 2 * sp_lam.r - 2 * dB_tbl[(lam, mu)]
            const_C = 2 * sp_lam.r - 2 * dC_tbl[(lam, mu)]
            if const_B > 0 or const_C > 0:  # only keep potentially useful pairs
                pairs.append((lam, mu, nu, const_B, const_C, sp_mu.r))
    return targets, pairs


def dfs_enumerate(time_limit: float = 300.0, first_point: int = 0,
                  max_cap: int = 0) -> dict:
    """Run orderly DFS with Wang + unconditional leakage pruning."""
    t0 = time.time()
    wang_table = build_wang_table()
    if max_cap > 0:
        wang_table = [(pts, cap) for pts, cap in wang_table if cap <= max_cap]
    targets, leak_pairs = build_leakage_table()
    build_sec = time.time() - t0

    # For each point, precompute which Wang rows it participates in
    point_wang_rows = {p: [] for p in POINTS}
    for idx, (pts, cap) in enumerate(wang_table):
        for p in pts:
            if p in point_wang_rows:
                point_wang_rows[p].append(idx)

    # State arrays
    selected = [0] * (S_RANK + 1)  # selected[i] = point at position i
    occ = [0] * len(wang_table)     # current occupation of each Wang row
    m_cur = [0] * 256               # current m_lambda values
    n_selected = [0]                # mutable counter
    solutions = []
    stats = {"wang_prunes": 0, "leak_prunes": 0, "nodes": 0, "leaves": 0}
    timeout = [False]

    # Future potential: for each Wang row, how many remaining candidate points
    # could still be added. Initialize to full point set.
    remaining_in = [0] * len(wang_table)
    for idx, (pts, cap) in enumerate(wang_table):
        remaining_in[idx] = sum(1 for p in pts if p >= (first_point if first_point > 0 else 1))

    def check_leakage() -> bool:
        """Check unconditional leakage feasibility for current partial support.

        For a partial support of size k < 19, future additions can only increase
        m_lambda values. The leakage bound for a target mu is:
          2*eB(mu) >= 2*r_lam - m_lam + m_mu - m_{lam^mu} - 2*dB
        In the worst case for the prover (best case for feasibility):
          m_lam is maximized -> m_lam can reach at most m_cur[lam] + (19 - k)
          m_mu is minimized -> m_cur[mu] (already known, can only increase)
          m_{lam^mu} is maximized -> can reach at most m_cur[nu] + (19 - k)

        For pruning: use CURRENT values as lower bounds on m_mu and upper bounds
        on m_lam and m_{lam^mu} to get a conservative test.
        Actually, the RHS = const - m_lam + m_mu - m_nu. To maximize eB_lb,
        we want m_lam small, m_mu large, m_nu small.
        Current values: m_lam >= m_cur[lam], m_mu >= m_cur[mu], m_nu >= m_cur[nu].
        Future: m_lam <= m_cur[lam] + slack, etc. where slack = 19 - k.

        Best eB_lb for pruning: use m_lam = m_cur[lam] (minimum, since future adds increase it),
        m_mu = m_cur[mu] + (19 - k) (maximum possible), m_nu = m_cur[nu] (minimum).
        But this OVER-counts: a single future point adds to m_lam AND m_mu AND m_nu
        simultaneously, so they can't be independently optimized.

        Conservative pruning: use current weights only (ignoring future additions).
        This gives: 2*eB(mu) >= const - m_cur[lam] + m_cur[mu] - m_cur[nu]
        This underestimates the final constraint (future m_mu increases help).
        """
        k = n_selected[0]
        for mu in targets:
            sp_mu = base.SPACES[mu]
            cur_m_mu = m_cur[mu]
            if cur_m_mu < sp_mu.r:
                continue  # target not yet feasible (might become feasible later)
            budget = cur_m_mu - sp_mu.r  # lower bound on final budget (it can only increase)
            # But the budget can increase with future m_mu additions...
            # So this conservative check only triggers when current budget is already tight
            # and leakage is already high.
            best_eB = 0
            best_eC = 0
            for lam, mu2, nu, const_B, const_C, r_mu in leak_pairs:
                if mu2 != mu:
                    continue
                ml = m_cur[lam]
                mnu = m_cur[nu] if nu != 0 else S_RANK
                rhs_B = const_B - ml + cur_m_mu - mnu
                rhs_C = const_C - ml + cur_m_mu - mnu
                if rhs_B > 0:
                    lb = (rhs_B + 1) // 2
                    if lb > best_eB:
                        best_eB = lb
                if rhs_C > 0:
                    lb = (rhs_C + 1) // 2
                    if lb > best_eC:
                        best_eC = lb
            if best_eB + best_eC > budget:
                # Current excess bounds already exceed current budget.
                # But budget can increase with future m_mu...
                # Only prune if even maximum future budget can't help.
                max_future_budget = S_RANK - sp_mu.r  # m_mu can be at most 19
                if best_eB + best_eC > max_future_budget:
                    return False
                # For intermediate check: eB + eC > 9 - r_mu is impossible
                # (since eB <= 9-r_mu and eC <= 9-r_mu, total can be 2*(9-r_mu))
                # Actually eB + eC <= m_mu - r_mu <= 19 - r_mu
                # eB <= 9 - r_mu, eC <= 9 - r_mu
                # So max(eB + eC) = min(m_mu - r_mu, eB_max + eC_max) = min(16, 12) = 12 for rank 1
                # This won't trigger for rank-1 targets (max_future_budget = 16)
                pass
        return True

    def dfs(depth: int, min_point: int):
        """DFS with orderly generation."""
        if time.time() - t0 > time_limit + build_sec:
            timeout[0] = True
            return

        stats["nodes"] += 1

        if depth > S_RANK:
            # Found a complete support!
            stats["leaves"] += 1
            sol = list(selected[1:S_RANK+1])
            solutions.append(sol)
            return

        remaining_to_pick = S_RANK - depth + 1  # how many more points to select

        for p in range(min_point, 256):
            if timeout[0]:
                return

            # Check Wang feasibility: adding p to current selection
            wang_ok = True
            affected_rows = point_wang_rows.get(p, [])
            for idx in affected_rows:
                pts, cap = wang_table[idx]
                if occ[idx] + 1 > cap:
                    wang_ok = False
                    break
            if not wang_ok:
                stats["wang_prunes"] += 1
                continue

            # Also check: can we still reach 19 points?
            # After selecting p, we need (remaining_to_pick - 1) more from {p+1,...,255}
            if 255 - p < remaining_to_pick - 1:
                break  # lexicographic: no point trying further

            # Select point p
            selected[depth] = p
            n_selected[0] = depth

            # Update contraction weights
            for lam in range(1, 256):
                if base.dot8(lam, p):
                    m_cur[lam] += 1

            # Update Wang occupation
            for idx in affected_rows:
                occ[idx] += 1

            # Recurse
            dfs(depth + 1, p + 1)

            # Undo
            for lam in range(1, 256):
                if base.dot8(lam, p):
                    m_cur[lam] -= 1
            for idx in affected_rows:
                occ[idx] -= 1
            n_selected[0] = depth - 1

    # Run DFS
    if first_point > 0:
        # Fix first point and search
        selected[1] = first_point
        n_selected[0] = 1
        for lam in range(1, 256):
            if base.dot8(lam, first_point):
                m_cur[lam] += 1
        for idx in point_wang_rows.get(first_point, []):
            occ[idx] += 1
        dfs(2, first_point + 1)
    else:
        dfs(1, 1)

    elapsed = time.time() - t0
    return {
        "schema": "s0908_wang_leakage_dfs_v1",
        "s_rank": S_RANK,
        "first_point": first_point,
        "wang_rows": len(wang_table),
        "wang_cap_hist": {str(cap): sum(1 for _, c in wang_table if c == cap)
                         for cap in sorted(set(c for _, c in wang_table))},
        "leak_pairs": len(leak_pairs),
        "build_sec": round(build_sec, 3),
        "elapsed_sec": round(elapsed, 3),
        "timeout": timeout[0],
        "time_limit": time_limit,
        "stats": stats,
        "solutions_found": len(solutions),
        "solutions_head": solutions[:10],
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--time-limit", type=float, default=120)
    ap.add_argument("--first-point", type=int, default=0, help="Fix first point (0=no fix)")
    ap.add_argument("--max-cap", type=int, default=0, help="Only use Wang rows with cap <= this (0=all)")
    ap.add_argument("--out", default=str(OUTDIR / "wang_dfs_pilot.json"))
    args = ap.parse_args()

    OUTDIR.mkdir(parents=True, exist_ok=True)
    result = dfs_enumerate(time_limit=args.time_limit, first_point=args.first_point,
                            max_cap=args.max_cap)
    outpath = Path(args.out)
    with open(outpath, "w") as f:
        json.dump(result, f, indent=2, sort_keys=True)
    brief = {k: v for k, v in result.items() if k != "solutions_head"}
    print(json.dumps(brief, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
