#!/usr/bin/env python3
"""Classify and probe anchored nonadjacent rank-1 matching strata.

In the nonadjacent half of the analysis cover, fix E11 as one selected
rank-1 A-point.  The remaining selected rank-1 points form a matching on the
6x6 Segre grid of rank-1 points not sharing E11's left or right vector.
There are sum_j C(6,j)^2 j! = 13327 anchored matchings before symmetry.

This script classifies actual whole matching sets under Stab(E11).  It can
also run conditioned higher-rank completion CP-SAT probes for selected strata:
for a fixed rank-1 matching M, all rank-1 choices are fixed and the solver
selects exactly rank_s-|M| higher-rank projective A-points subject to selected
Wang occupation rows with residual capacities rank_s-L(Phi)-|M cap Phi|.

The CP-SAT output is execution evidence only, not a mathematical certificate.
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
from typing import Iterable, Sequence

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from precompute_skeleton_system import compute_stab_e11  # noqa: E402
from skeleton_oracle_joint_pilot import canonical_set  # noqa: E402
from wang_capacity_cnf_e11_fixed import E11, parse_dims  # noqa: E402
from wang_capacity_lazy import in_rowspace, matrix_rank_of_mask, subspace_points_from_basis, transform_mask, unpack_basis  # noqa: E402


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
    if set(rank1) != set(out) or len(out) != 49 or out[E11] != (1, 1):
        raise RuntimeError({'rank1_count': len(rank1), 'uv_count': len(out), 'E11_uv': out.get(E11)})
    return out


def anchored_matchings() -> list[tuple[int, ...]]:
    """All selected rank-1 sets in the matching branch, including E11."""
    out: list[tuple[int, ...]] = []
    us = list(range(2, 8))
    vs = list(range(2, 8))
    for j in range(0, 7):
        for U in itertools.combinations(us, j):
            for V in itertools.combinations(vs, j):
                for perm in itertools.permutations(V):
                    pts = [E11]
                    pts.extend(outer_mask(u, v) for u, v in zip(U, perm))
                    out.append(tuple(sorted(pts)))
    return out


def all_images(points: Sequence[int], group: Sequence[Sequence[int]]) -> set[tuple[int, ...]]:
    return {tuple(sorted(transform_mask(int(p), g) for p in points)) for g in group}


def matching_ok(points: Sequence[int], uv: dict[int, tuple[int, int]]) -> bool:
    us: set[int] = set()
    vs: set[int] = set()
    for p in points:
        u, v = uv[int(p)]
        if u in us or v in vs:
            return False
        us.add(u); vs.add(v)
    return True


def classify_matchings() -> dict:
    uv = rank1_uv_map()
    _, stab_e11 = compute_stab_e11()
    matchings = anchored_matchings()
    count_formula = sum(__import__('math').comb(6, j) ** 2 * __import__('math').factorial(j) for j in range(7))
    if len(matchings) != count_formula:
        raise RuntimeError({'enumerated': len(matchings), 'formula': count_formula})
    if any(E11 not in m or not matching_ok(m, uv) for m in matchings):
        raise RuntimeError('bad anchored matching enumeration')

    classes: dict[tuple[int, ...], dict] = {}
    for m in matchings:
        can = tuple(canonical_set(m, stab_e11))
        rec = classes.get(can)
        if rec is None:
            imgs = all_images(can, stab_e11)
            # Restrict to anchored matchings; the full stabilizer should preserve this set.
            anchored_imgs = [img for img in imgs if E11 in img and all(p in uv for p in img) and matching_ok(img, uv)]
            rec = {
                'canonical': list(can),
                'k': len(can),
                'other_points_uv': [{'point': p, 'u': uv[p][0], 'v': uv[p][1]} for p in can if p != E11],
                'orbit_image_count': len(imgs),
                'anchored_matching_image_count': len(anchored_imgs),
                'stabilizer_size_in_StabE11': len(stab_e11) // len(imgs),
                'enumerated_members': 0,
            }
            classes[can] = rec
        rec['enumerated_members'] += 1

    by_k = Counter(len(m) for m in matchings)
    class_by_k = Counter(rec['k'] for rec in classes.values())
    member_sum_by_k = defaultdict(int)
    orbit_sum_by_k = defaultdict(int)
    mismatch = []
    for rec in classes.values():
        member_sum_by_k[rec['k']] += rec['enumerated_members']
        orbit_sum_by_k[rec['k']] += rec['anchored_matching_image_count']
        if rec['enumerated_members'] != rec['anchored_matching_image_count']:
            mismatch.append({'canonical': rec['canonical'], 'enumerated_members': rec['enumerated_members'], 'anchored_matching_image_count': rec['anchored_matching_image_count']})

    reps_by_k = defaultdict(list)
    for can in sorted(classes):
        reps_by_k[len(can)].append(classes[can])

    return {
        'problem': 'anchored nonadjacent rank-1 matching strata under Stab(E11)',
        'field': 'F2',
        'fixed_anchor': E11,
        'stab_E11_order': len(stab_e11),
        'anchored_matching_count': len(matchings),
        'formula_count': count_formula,
        'count_by_total_rank1_k': dict(sorted(by_k.items())),
        'strata_count_total': len(classes),
        'strata_count_by_total_rank1_k': dict(sorted(class_by_k.items())),
        'strata_member_sum_by_k': dict(sorted(member_sum_by_k.items())),
        'strata_orbit_image_sum_by_k': dict(sorted(orbit_sum_by_k.items())),
        'orbit_member_mismatch_count': len(mismatch),
        'orbit_member_mismatch_head': mismatch[:10],
        'representatives_by_k': {str(k): reps_by_k[k] for k in sorted(reps_by_k)},
        'meaning': 'For each representative M, all rank-1 support variables are fixed to exactly M; choose 20-|M| higher-rank points subject to residual Wang capacities.',
    }


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def row_contains(point: int, basis: Sequence[int]) -> bool:
    return in_rowspace(int(point), basis, n=9)


def solve_fixed_matching(lut: dict[int, int], lmeta: dict, matching: Sequence[int], *, rank_s: int,
                         include_dims: set[int], through_e11_dims: set[int], seed_keys: set[int],
                         time_limit: float, workers: int, out: Path) -> dict:
    from ortools.sat.python import cp_model

    t0 = time.time()
    uv = rank1_uv_map()
    matching = tuple(sorted(int(p) for p in matching))
    if E11 not in matching or any(p not in uv for p in matching) or not matching_ok(matching, uv):
        raise ValueError(f'not an anchored rank-1 matching: {matching}')
    rank1_selected = set(matching)
    rank1_all = set(uv)
    hr_pts = [p for p in range(1, 512) if p not in rank1_all]
    target_hr = rank_s - len(matching)
    if target_hr < 0 or target_hr > len(hr_pts):
        raise ValueError('bad target_hr')

    model = cp_model.CpModel()
    y = {p: model.NewBoolVar(f'y_{p}') for p in hr_pts}
    model.Add(sum(y.values()) == target_hr)

    rows_added = skipped = empty = 0
    rows_by_dim = Counter(); rows_by_lb = Counter(); source_by_dim = Counter(); row_var_hist = Counter(); cap_hist = Counter(); selected_r1_occ_hist = Counter()
    witness_head = []
    for i, (key0, lb0) in enumerate(lut.items(), 1):
        key = int(key0); lb = int(lb0); d = key & 0xF
        source = None
        basis = None
        if d in include_dims:
            source = 'include_dim'
        elif d in through_e11_dims:
            basis = unpack_basis(key)
            if row_contains(E11, basis):
                source = 'through_E11'
        if source is None and key in seed_keys:
            source = 'seed'
        if source is None:
            continue
        if basis is None:
            basis = unpack_basis(key)
        pts = subspace_points_from_basis(basis)
        selected_r1_occ = sum(1 for p in matching if p in pts)
        cap = rank_s - lb - selected_r1_occ
        vars_in = [y[p] for p in pts if p in y]
        rows_by_dim[d] += 1; rows_by_lb[lb] += 1; source_by_dim[(source, d)] += 1; row_var_hist[len(vars_in)] += 1; cap_hist[cap] += 1; selected_r1_occ_hist[selected_r1_occ] += 1
        if len(witness_head) < 60 and (cap < 0 or len(vars_in) > cap):
            witness_head.append({'key': key, 'dim': d, 'lb': lb, 'selected_rank1_in_row': selected_r1_occ, 'hr_vars_in_row': len(vars_in), 'cap': cap, 'source': source, 'basis': list(basis)})
        if cap < 0:
            model.AddBoolOr([]); rows_added += 1; empty += 1
        elif len(vars_in) <= cap:
            skipped += 1
        else:
            model.Add(sum(vars_in) <= cap); rows_added += 1
        if i % 1_000_000 == 0:
            print(f'  scanned {i:,}/{len(lut):,}; added={rows_added:,}; elapsed={time.time()-t0:.1f}s', flush=True)

    build_elapsed = time.time() - t0
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(time_limit)
    solver.parameters.num_search_workers = int(workers)
    t1 = time.time(); st = solver.Solve(model); solve_elapsed = time.time() - t1
    status = solver.StatusName(st)
    support_hr = None
    support = None
    if status in ('OPTIMAL', 'FEASIBLE'):
        support_hr = [p for p in hr_pts if solver.Value(y[p])]
        support = sorted(list(matching) + support_hr)
    payload = {
        'problem': 'conditioned matching-stratum higher-rank completion',
        'field': 'F2',
        'rank_s': rank_s,
        'fixed_rank1_matching': list(matching),
        'fixed_rank1_matching_uv': [{'point': p, 'u': uv[p][0], 'v': uv[p][1]} for p in matching],
        'total_rank1_k': len(matching),
        'target_higher_rank_count': target_hr,
        'include_dims': sorted(include_dims),
        'through_e11_dims': sorted(through_e11_dims),
        'seed_key_count': len(seed_keys),
        'wang_rows_added': rows_added,
        'wang_rows_by_dim': dict(sorted(rows_by_dim.items())),
        'wang_rows_by_lb': dict(sorted(rows_by_lb.items())),
        'wang_source_by_dim': {f'{s},{d}': c for (s, d), c in sorted(source_by_dim.items())},
        'wang_row_var_hist': dict(sorted(row_var_hist.items())),
        'wang_cap_hist': dict(sorted(cap_hist.items())),
        'selected_rank1_occ_hist': dict(sorted(selected_r1_occ_hist.items())),
        'wang_skipped_vacuous': skipped,
        'wang_empty': empty,
        'witness_head': witness_head,
        'solver_status': status,
        'solver_status_code': int(st),
        'solver_walltime': float(solver.WallTime()),
        'solver_num_conflicts': int(solver.NumConflicts()),
        'solver_num_branches': int(solver.NumBranches()),
        'build_elapsed_sec': build_elapsed,
        'solve_elapsed_sec': solve_elapsed,
        'support_higher_rank': support_hr,
        'support': support,
        'support_size': None if support is None else len(support),
        'support_rank_hist': None if support is None else dict(sorted(Counter(matrix_rank_of_mask(p) for p in support).items())),
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'meaning': 'Conditioned on this exact rank-1 matching stratum. Feasible support must be scanned against the full expanded LUT before being treated as a complete Wang-admissible A-support.',
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'matching': list(matching),
        'k': len(matching),
        'target_hr': target_hr,
        'solver_status': status,
        'support_size': payload['support_size'],
        'support_rank_hist': payload['support_rank_hist'],
        'wang_rows_added': rows_added,
        'build_elapsed_sec': build_elapsed,
        'solve_elapsed_sec': solve_elapsed,
        'out': str(out),
    }, indent=2, sort_keys=True), flush=True)
    return payload


def collect_keys_from_json(path: Path) -> set[int]:
    data = json.loads(path.read_text())
    out: set[int] = set()
    def visit(obj):
        if isinstance(obj, dict):
            if 'key' in obj and ('lb' in obj or 'dim' in obj or 'occupancy' in obj or 'cap' in obj):
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


def choose_probe_reps(class_payload: dict, ks: Sequence[int] | None, max_per_k: int) -> list[dict]:
    reps = []
    rbk = class_payload['representatives_by_k']
    use_ks = [int(k) for k in (ks if ks is not None else sorted(int(x) for x in rbk))]
    for k in use_ks:
        arr = list(rbk.get(str(k), []))
        # Prefer largest orbit strata first; tie by canonical set.
        arr.sort(key=lambda r: (-int(r['enumerated_members']), tuple(r['canonical'])))
        reps.extend(arr[:max_per_k])
    return reps


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', type=Path, required=True, help='classification JSON path')
    ap.add_argument('--probe-outdir', type=Path, default=None)
    ap.add_argument('--probe-summary', type=Path, default=None)
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--probe-k', type=int, action='append', default=None, help='total rank-1 k values to probe; repeatable')
    ap.add_argument('--max-probe-per-k', type=int, default=0)
    ap.add_argument('--include-dims', default='1')
    ap.add_argument('--through-e11-dims', default='4,6')
    ap.add_argument('--seed-json', type=Path, action='append', default=[])
    ap.add_argument('--time-limit', type=float, default=60.0)
    ap.add_argument('--workers', type=int, default=8)
    args = ap.parse_args()

    t0 = time.time()
    payload = classify_matchings()
    payload['elapsed_sec'] = time.time() - t0
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'anchored_matching_count': payload['anchored_matching_count'],
        'strata_count_total': payload['strata_count_total'],
        'strata_count_by_k': payload['strata_count_by_total_rank1_k'],
        'orbit_member_mismatch_count': payload['orbit_member_mismatch_count'],
        'out': str(args.out),
    }, indent=2, sort_keys=True), flush=True)

    if args.max_probe_per_k <= 0:
        return
    if args.probe_outdir is None or args.probe_summary is None:
        raise ValueError('--probe-outdir and --probe-summary required when probing')
    seed_keys: set[int] = set()
    for sp in args.seed_json:
        got = collect_keys_from_json(sp)
        print(f'seed {sp}: {len(got)} keys', flush=True)
        seed_keys.update(got)
    lut, lmeta = load_lut(args.lut)
    reps = choose_probe_reps(payload, args.probe_k, args.max_probe_per_k)
    args.probe_outdir.mkdir(parents=True, exist_ok=True)
    records = []
    for idx, rec in enumerate(reps):
        k = int(rec['k'])
        can = [int(p) for p in rec['canonical']]
        out = args.probe_outdir / f'matching_stratum_k{k:02d}_idx{idx:04d}_can_{"_".join(map(str, can))}.json'
        q = solve_fixed_matching(
            lut, lmeta, can, rank_s=args.rank,
            include_dims=parse_dims(args.include_dims), through_e11_dims=parse_dims(args.through_e11_dims), seed_keys=seed_keys,
            time_limit=args.time_limit, workers=args.workers, out=out,
        )
        records.append({
            'idx': idx,
            'k': k,
            'canonical': can,
            'enumerated_members': rec['enumerated_members'],
            'orbit_image_count': rec['orbit_image_count'],
            'path': str(out),
            'solver_status': q['solver_status'],
            'support_size': q.get('support_size'),
            'support_rank_hist': q.get('support_rank_hist'),
            'target_higher_rank_count': q.get('target_higher_rank_count'),
            'wang_rows_added': q.get('wang_rows_added'),
            'solve_elapsed_sec': q.get('solve_elapsed_sec'),
        })
        summary = {
            'problem': 'matching stratum conditioned HR completion probe summary',
            'classification_path': str(args.out),
            'probe_k': args.probe_k,
            'max_probe_per_k': args.max_probe_per_k,
            'include_dims': sorted(parse_dims(args.include_dims)),
            'through_e11_dims': sorted(parse_dims(args.through_e11_dims)),
            'seed_key_count': len(seed_keys),
            'records': records,
            'status_hist_so_far': dict(sorted(Counter(r['solver_status'] for r in records).items())),
            'elapsed_sec': time.time() - t0,
        }
        args.probe_summary.parent.mkdir(parents=True, exist_ok=True)
        args.probe_summary.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(json.dumps(summary, indent=2, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
