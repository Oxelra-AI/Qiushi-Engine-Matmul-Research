#!/usr/bin/env python3
"""CP-SAT probe for the global nonadjacent rank-1 matching branch.

After fixing one selected rank-1 A-factor to E11, the alternative to an
adjacent rank-1 pair is that all selected rank-1 points form a matching in the
7x7 Segre grid of rank-1 matrices u v^T over F2.  This script keeps the full
A-side projective variable universe (no second-orbit branch exclusions), fixes
E11, imposes exact rank-1 count k and matching constraints, and adds selected
Wang occupation rows.

The output is computational evidence only.  INFEASIBLE requires a checked
CNF/PB proof before theorem use; SAT/FEASIBLE is only a row-family candidate and
must be scanned against the full expanded Wang LUT.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Sequence, Set

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rank1_capacity_profile import load_or_build as load_or_build_rank1_projection  # noqa: E402
from wang_capacity_cnf_e11_fixed import E11, parse_dims  # noqa: E402
from wang_capacity_lazy import in_rowspace, matrix_rank_of_mask, subspace_points_from_basis, unpack_basis  # noqa: E402


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def outer_mask(u: int, v: int) -> int:
    mask = 0
    for i in range(3):
        if (u >> i) & 1:
            mask |= int(v) << (3 * i)
    return mask


def rank1_uv_map() -> dict[int, tuple[int, int]]:
    out: dict[int, tuple[int, int]] = {}
    for u in range(1, 8):
        for v in range(1, 8):
            out[outer_mask(u, v)] = (u, v)
    rank1 = [p for p in range(1, 512) if matrix_rank_of_mask(p) == 1]
    if set(rank1) != set(out) or len(out) != 49:
        raise RuntimeError('rank1 uv map mismatch')
    return out


def row_contains(point: int, basis: Sequence[int]) -> bool:
    return in_rowspace(int(point), basis, n=9)


def parse_groups(spec: str) -> set[tuple[int, int]] | None:
    spec = spec.strip()
    if not spec:
        return None
    out: set[tuple[int, int]] = set()
    for part in spec.replace(';', ',').split(','):
        part = part.strip()
        if not part:
            continue
        if ':' in part:
            a, b = part.split(':', 1)
        elif '/' in part:
            a, b = part.split('/', 1)
        else:
            raise ValueError(f'bad group spec {part!r}')
        out.add((int(a), int(b)))
    return out


def collect_keys_from_json(path: Path) -> set[int]:
    """Collect Wang row keys from scan/core JSONs with nested key fields."""
    data = json.loads(path.read_text())
    out: set[int] = set()

    def visit(obj):
        if isinstance(obj, dict):
            if 'key' in obj and ('lb' in obj or 'dim' in obj or 'occupancy' in obj):
                try:
                    out.add(int(obj['key']))
                except Exception:
                    pass
            for v in obj.values():
                visit(v)
        elif isinstance(obj, list):
            for v in obj:
                visit(v)
    visit(data)
    return out


def add_rank1_projection(model, x: dict[int, object], rank1_cache: Path, lut_path: Path, rank_s: int,
                         max_intersection_size: int | None, include_groups: set[tuple[int, int]] | None):
    pts_r1, cons, cmeta, lmeta = load_or_build_rank1_projection(rank1_cache, lut_path, rank_s, False)
    rows_added = skipped = empty = 0
    row_hist = Counter(); cap_hist = Counter(); row_var_hist = Counter(); group_selected = Counter()
    for mask0, cap0, key in cons:
        mask = int(mask0); cap = int(cap0); size = mask.bit_count()
        if include_groups is not None and (size, cap) not in include_groups:
            continue
        if include_groups is None and max_intersection_size is not None and size > max_intersection_size:
            continue
        vars_in = []
        y = mask
        while y:
            lb = y & -y
            i = lb.bit_length() - 1
            y ^= lb
            p = int(pts_r1[i])
            vars_in.append(x[p])
        row_hist[(size, cap)] += 1; cap_hist[cap] += 1; row_var_hist[len(vars_in)] += 1; group_selected[(size, cap)] += 1
        if cap < 0:
            model.AddBoolOr([]); rows_added += 1; empty += 1
        elif len(vars_in) <= cap:
            skipped += 1
        else:
            model.Add(sum(vars_in) <= cap); rows_added += 1
    return {
        'rank1_projection_rows_added': rows_added,
        'rank1_projection_skipped_vacuous': skipped,
        'rank1_projection_empty': empty,
        'rank1_projection_hist': {f'{a},{b}': c for (a, b), c in sorted(row_hist.items())},
        'rank1_projection_cap_hist': dict(sorted(cap_hist.items())),
        'rank1_projection_row_var_hist': dict(sorted(row_var_hist.items())),
        'rank1_projection_filter': {
            'max_intersection_size': max_intersection_size,
            'include_groups': None if include_groups is None else sorted([list(g) for g in include_groups]),
        },
        'rank1_projection_cache_meta_brief': {
            'compressed_intersections': cmeta.get('compressed_intersections'),
            'nonvacuous_constraints': cmeta.get('nonvacuous_constraints'),
            'lut_coverage_ok': lmeta.get('coverage_ok'),
            'lut_conflict_count': lmeta.get('conflict_count'),
        },
    }


def solve_one(lut: dict[int, int], lmeta: dict, *, lut_path: Path, rank_s: int, exact_k: int,
              include_dims: Set[int], through_e11_dims: Set[int], seed_keys: set[int],
              rank1_cache: Path, use_rank1_projection: bool, rank1_max_intersection_size: int | None,
              rank1_include_groups: set[tuple[int, int]] | None,
              time_limit: float, workers: int, out: Path) -> dict:
    from ortools.sat.python import cp_model

    t0 = time.time()
    uv = rank1_uv_map()
    rank1_pts = sorted(uv)
    if exact_k < 1 or exact_k > 7:
        raise ValueError('matching branch after E11 requires 1 <= exact_k <= 7')
    model = cp_model.CpModel()
    pts = list(range(1, 512))
    x = {p: model.NewBoolVar(f'x_{p}') for p in pts}
    model.Add(sum(x.values()) == rank_s)
    model.Add(x[E11] == 1)
    model.Add(sum(x[p] for p in rank1_pts) == exact_k)

    # Matching in the rank-1 Segre grid. Since x[E11]=1 and E11=(1,1),
    # this also forbids all other rank-1 points sharing its left or right vector.
    left_constraints = 0
    right_constraints = 0
    for u in range(1, 8):
        model.Add(sum(x[outer_mask(u, v)] for v in range(1, 8)) <= 1)
        left_constraints += 1
    for v in range(1, 8):
        model.Add(sum(x[outer_mask(u, v)] for u in range(1, 8)) <= 1)
        right_constraints += 1

    rows_added = skipped = empty = 0
    rows_by_dim = Counter(); rows_by_lb = Counter(); source_by_dim = Counter(); row_var_hist = Counter(); cap_hist = Counter(); e11_in_hist = Counter()
    for i, (key, lb0) in enumerate(lut.items(), 1):
        d = int(key) & 0xF
        source = None
        basis = None
        if d in include_dims:
            source = 'include_dim'
        elif d in through_e11_dims:
            basis = unpack_basis(key)
            if row_contains(E11, basis):
                source = 'through_E11'
        if source is None and int(key) in seed_keys:
            source = 'seed'
        if source is None:
            continue
        if basis is None:
            basis = unpack_basis(key)
        row_pts = subspace_points_from_basis(basis)
        cap = rank_s - int(lb0)
        vars_in = [x[p] for p in row_pts]
        rows_by_dim[d] += 1; rows_by_lb[int(lb0)] += 1; source_by_dim[(source, d)] += 1; row_var_hist[len(vars_in)] += 1; cap_hist[cap] += 1
        e11_in_hist[1 if E11 in row_pts else 0] += 1
        if cap < 0:
            model.AddBoolOr([]); rows_added += 1; empty += 1
        elif len(vars_in) <= cap:
            skipped += 1
        else:
            model.Add(sum(vars_in) <= cap); rows_added += 1
        if i % 1_000_000 == 0:
            print(f'  scanned {i:,}/{len(lut):,}; added={rows_added:,}; elapsed={time.time()-t0:.1f}s', flush=True)

    r1_stats = {
        'rank1_projection_rows_added': 0,
        'rank1_projection_skipped_vacuous': 0,
        'rank1_projection_empty': 0,
        'rank1_projection_filter': None,
    }
    if use_rank1_projection:
        r1_stats = add_rank1_projection(model, x, rank1_cache, lut_path, rank_s,
                                        rank1_max_intersection_size, rank1_include_groups)

    build_elapsed = time.time() - t0
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_search_workers = workers
    t1 = time.time(); st = solver.Solve(model); solve_elapsed = time.time() - t1
    names = {cp_model.OPTIMAL: 'OPTIMAL', cp_model.FEASIBLE: 'FEASIBLE', cp_model.INFEASIBLE: 'INFEASIBLE', cp_model.UNKNOWN: 'UNKNOWN', cp_model.MODEL_INVALID: 'MODEL_INVALID'}
    status = names.get(st, str(st))
    support = None
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        support = [p for p in pts if solver.Value(x[p])]
    matching_rank1 = None
    if support is not None:
        matching_rank1 = [{'point': p, 'u': uv[p][0], 'v': uv[p][1]} for p in support if p in uv]
    payload = {
        'problem': 'global nonadjacent rank-1 matching branch Wang support CP-SAT',
        'field': 'F2',
        'rank_s': rank_s,
        'fixed_rank1_anchor': E11,
        'exact_rank1_count': exact_k,
        'include_dims': sorted(include_dims),
        'through_e11_dims': sorted(through_e11_dims),
        'seed_key_count': len(seed_keys),
        'matching_constraints': {
            'left_vector_at_most_one': left_constraints,
            'right_vector_at_most_one': right_constraints,
            'meaning': 'Selected rank-1 points form a matching in the 7x7 Segre grid; E11 fixed.',
        },
        'wang_rows_added': rows_added,
        'wang_rows_by_dim': dict(sorted(rows_by_dim.items())),
        'wang_rows_by_lb': dict(sorted(rows_by_lb.items())),
        'wang_source_by_dim': {f'{s},{d}': c for (s, d), c in sorted(source_by_dim.items())},
        'wang_row_var_hist': dict(sorted(row_var_hist.items())),
        'wang_cap_hist': dict(sorted(cap_hist.items())),
        'wang_e11_in_row_hist': dict(sorted(e11_in_hist.items())),
        'wang_skipped_vacuous': skipped,
        'wang_empty': empty,
        **r1_stats,
        'solver_status': status,
        'solver_status_code': int(st),
        'solver_walltime': float(solver.WallTime()),
        'solver_num_conflicts': int(solver.NumConflicts()),
        'solver_num_branches': int(solver.NumBranches()),
        'build_elapsed_sec': build_elapsed,
        'solve_elapsed_sec': solve_elapsed,
        'support': support,
        'support_size': None if support is None else len(support),
        'support_rank_hist': None if support is None else dict(sorted(Counter(matrix_rank_of_mask(p) for p in support).items())),
        'support_rank1_count': None if support is None else sum(1 for p in support if matrix_rank_of_mask(p) == 1),
        'support_rank1_uv': matching_rank1,
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'meaning': 'If all exact k=1..7 matching branches are infeasible with checked proofs, then nonadjacent rank-1 supports are excluded. Feasible supports require full expanded LUT scanning.',
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'k': exact_k,
        'solver_status': status,
        'support_size': payload['support_size'],
        'support_rank_hist': payload['support_rank_hist'],
        'wang_rows_added': rows_added,
        'rank1_projection_rows_added': r1_stats.get('rank1_projection_rows_added'),
        'build_elapsed_sec': build_elapsed,
        'solve_elapsed_sec': solve_elapsed,
        'out': str(out),
    }, indent=2, sort_keys=True), flush=True)
    return payload


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--k', type=int, action='append', default=None, help='exact k values; repeatable. Default 1..7')
    ap.add_argument('--include-dims', default='1')
    ap.add_argument('--through-e11-dims', default='4,6')
    ap.add_argument('--seed-json', type=Path, action='append', default=[], help='JSON files containing Wang row key fields to include as seed cuts')
    ap.add_argument('--rank1-projection', action='store_true')
    ap.add_argument('--rank1-cache', type=Path, default=Path('data/wang_capacity_rank1_profile/rank1_intersection_cache.pkl'))
    ap.add_argument('--rank1-max-intersection-size', type=int, default=None)
    ap.add_argument('--rank1-include-groups', default='')
    ap.add_argument('--time-limit', type=float, default=120.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--outdir', type=Path, required=True)
    ap.add_argument('--summary', type=Path, required=True)
    args = ap.parse_args()

    ks = args.k if args.k is not None else list(range(1, 8))
    lut, lmeta = load_lut(args.lut)
    seed_keys: set[int] = set()
    for sp in args.seed_json:
        got = collect_keys_from_json(sp)
        print(f'seed {sp}: {len(got)} keys', flush=True)
        seed_keys.update(got)
    print(f'loaded LUT {len(lut):,} coverage={lmeta.get("coverage_ok")} conflicts={lmeta.get("conflict_count")} seed_keys={len(seed_keys)}', flush=True)
    records = []
    t0 = time.time()
    args.outdir.mkdir(parents=True, exist_ok=True)
    for k in ks:
        out = args.outdir / f'matching_exact_k{k:02d}_dims{args.include_dims.replace(",","")}_through{args.through_e11_dims.replace(",","")}.json'
        rec = solve_one(
            lut, lmeta, lut_path=args.lut, rank_s=args.rank, exact_k=int(k),
            include_dims=parse_dims(args.include_dims), through_e11_dims=parse_dims(args.through_e11_dims),
            seed_keys=seed_keys, rank1_cache=args.rank1_cache, use_rank1_projection=args.rank1_projection,
            rank1_max_intersection_size=args.rank1_max_intersection_size,
            rank1_include_groups=parse_groups(args.rank1_include_groups),
            time_limit=args.time_limit, workers=args.workers, out=out,
        )
        records.append({
            'k': int(k), 'path': str(out), 'solver_status': rec['solver_status'],
            'support_size': rec.get('support_size'), 'support_rank_hist': rec.get('support_rank_hist'),
            'support_rank1_count': rec.get('support_rank1_count'),
            'build_elapsed_sec': rec.get('build_elapsed_sec'), 'solve_elapsed_sec': rec.get('solve_elapsed_sec'),
            'wang_rows_added': rec.get('wang_rows_added'),
            'rank1_projection_rows_added': rec.get('rank1_projection_rows_added'),
        })
        summary = {
            'problem': 'global nonadjacent rank-1 matching branch exact-k scan',
            'field': 'F2',
            'rank_s': args.rank,
            'fixed_rank1_anchor': E11,
            'k_values_requested': [int(x) for x in ks],
            'include_dims': sorted(parse_dims(args.include_dims)),
            'through_e11_dims': sorted(parse_dims(args.through_e11_dims)),
            'seed_key_count': len(seed_keys),
            'seed_json': [str(p) for p in args.seed_json],
            'rank1_projection': bool(args.rank1_projection),
            'records': records,
            'status_hist_so_far': dict(sorted(Counter(r['solver_status'] for r in records).items())),
            'elapsed_sec': time.time() - t0,
            'meaning': 'CP-SAT evidence for the matching alternative in the analysis global rank-1 cover; proof objects still required for lower-bound use.',
        }
        args.summary.parent.mkdir(parents=True, exist_ok=True)
        args.summary.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
