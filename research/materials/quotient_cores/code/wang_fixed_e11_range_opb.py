#!/usr/bin/env python3
"""Generate a native pseudo-Boolean OPB instance for fixed-E11 Wang support branches.

This is a clean OPB counterpart of ``wang_fixed_e11_range_cpsat.py``.  It is
written after the analysis sequential-counter bug so that native PB solvers can
reason over the Wang cardinality inequalities without auxiliary CNF counters.

Semantics:
  * Universe: projective A-points of F2^9, omitting earlier Stab(E11) second
    orbits when requested by the branch partition.
  * Variables: dense x1..xN variables mapped to remaining projective points;
    fixed points are variables constrained to be 1, not silently removed.
  * Total support: two inequalities enforcing sum x_p = rank_s.
  * Wang rows: selected dimension rows and rows through the fixed prefix encode
    sum_{p in Phi and p present} x_p <= rank_s - L(Phi).
  * Rank-1 projected rows: compressed full-Wang projection onto the 49 rank-1
    points, restricted to present variables, with the same capacities.

UNSAT plus a separately verified PB proof is a valid proof component for the
encoded necessary-condition branch.  SAT only gives an A-support candidate and
must be scanned against the full 8,283,458-row Wang LUT.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, Sequence, Set

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rank1_capacity_profile import load_or_build as load_or_build_rank1_projection  # noqa: E402
from wang_capacity_cnf_e11_fixed import E11, collect_violation_keys, parse_dims, stab_e11_orbits  # noqa: E402
from wang_capacity_lazy import in_rowspace, matrix_rank_of_mask, unpack_basis, subspace_points_from_basis  # noqa: E402

DEFAULT_LUT = Path('data/wang_f2_lb20/wang_subspace_lut.pkl')
DEFAULT_R1_CACHE = Path('data/wang_capacity_rank1_profile/rank1_intersection_cache.pkl')
DEFAULT_ROUNDINGSAT = Path('research/research_record/staging/processing/pbtools/roundingsat-master/build_qiushi/roundingsat')


def sha256(path: Path) -> str | None:
    if not path.exists() or not path.is_file():
        return None
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(4 * 1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return payload['lut'], payload.get('meta', {})


def parse_ints(spec: str) -> list[int]:
    if not spec.strip():
        return []
    return [int(x) for x in spec.replace(';', ',').split(',') if x.strip()]


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
            raise ValueError(f'bad rank1 group {part!r}')
        out.add((int(a), int(b)))
    return out


def branch_points(fixed_extra: Sequence[int], exclude_second_orbits_before: bool):
    fixed = [E11] + [int(p) for p in fixed_extra if int(p) != E11]
    if len(set(fixed)) != len(fixed):
        raise ValueError(f'duplicate fixed point in {fixed}')
    excluded: Set[int] = set()
    if exclude_second_orbits_before:
        if len(fixed_extra) != 1:
            raise ValueError('exclude_second_orbits_before requires exactly one fixed extra point')
        second_rep = int(fixed_extra[0])
        found = False
        for orb in stab_e11_orbits():
            if orb['rep'] == second_rep:
                found = True
                break
            excluded.update(int(p) for p in orb['members'])
        if not found:
            raise ValueError(f'{second_rep} is not a Stab(E11) representative')
        for p in fixed:
            excluded.discard(p)
    pts = [p for p in range(1, 512) if p not in excluded]
    p_to_var = {p: i + 1 for i, p in enumerate(pts)}
    for p in fixed:
        if p not in p_to_var:
            raise ValueError(f'fixed point {p} excluded from branch')
    return fixed, excluded, pts, p_to_var


def row_contains_all(points: Sequence[int], basis: Sequence[int]) -> bool:
    return all(in_rowspace(int(p), basis, n=9) for p in points)


def le_constraint(var_ids: Sequence[int], bound: int) -> str:
    # OPB parser accepts <= and positive integer coefficients.  For an empty
    # lhs, use a contradiction involving x1; every branch here has variables.
    if not var_ids:
        return '+1 x1 >= 2 ;'
    lhs = ' '.join(f'+1 x{v}' for v in var_ids)
    return f'{lhs} <= {bound} ;'


def ge_constraint(var_ids: Sequence[int], bound: int) -> str:
    if not var_ids:
        return '+1 x1 >= 2 ;' if bound > 0 else '+1 x1 >= 0 ;'
    lhs = ' '.join(f'+1 x{v}' for v in var_ids)
    return f'{lhs} >= {bound} ;'


def unit_constraint(var_id: int) -> str:
    return f'+1 x{var_id} >= 1 ;'


def read_support(path: Path) -> list[int]:
    payload = json.loads(path.read_text())
    for key in ('support', 'solution', 'nonzero_solution'):
        if key in payload and payload[key] is not None:
            return [int(x) for x in payload[key]]
    # Some support scans place the support under result.solution.
    if isinstance(payload.get('result'), dict) and payload['result'].get('solution') is not None:
        return [int(x) for x in payload['result']['solution']]
    raise ValueError(f'No support-like field found in {path}')


def add_or_check_violation(count: int, bound: int) -> int:
    return max(0, count - bound)


def generate_or_check(lut: Dict[int, int], lut_meta: dict, *, lut_path: Path, rank_s: int,
                      fixed_extra: Sequence[int], exclude_second_orbits_before: bool,
                      min_rank1_count: int | None, max_rank1_count: int | None,
                      include_dims: Set[int], through_fixed_dims: Set[int],
                      seed_keys: Set[int], seed_dims: Set[int], rank1_cache: Path,
                      rank1_max_intersection_size: int | None,
                      rank1_include_groups: set[tuple[int, int]] | None,
                      opb: Path | None, meta_path: Path, support_json: Path | None) -> dict:
    t0 = time.time()
    fixed, excluded, pts, p_to_var = branch_points(fixed_extra, exclude_second_orbits_before)
    pt_set = set(pts)
    fixed_set = set(fixed)
    all_lits = [p_to_var[p] for p in pts]
    rank1_pts_present = [p for p in pts if matrix_rank_of_mask(p) == 1]
    rank1_lits = [p_to_var[p] for p in rank1_pts_present]

    constraints: list[str] = []
    equality_as_two_ineq = 0
    fixed_unit_count = 0
    if opb is not None:
        constraints.append(ge_constraint(all_lits, rank_s)); equality_as_two_ineq += 1
        constraints.append(le_constraint(all_lits, rank_s)); equality_as_two_ineq += 1
        for p in fixed:
            constraints.append(unit_constraint(p_to_var[p])); fixed_unit_count += 1
        if min_rank1_count is not None:
            constraints.append(ge_constraint(rank1_lits, min_rank1_count))
        if max_rank1_count is not None:
            constraints.append(le_constraint(rank1_lits, max_rank1_count))

    support: set[int] | None = None
    support_errors: list[str] = []
    support_rank1_count = None
    if support_json is not None:
        support_list = read_support(support_json)
        support = set(support_list)
        if len(support) != len(support_list):
            support_errors.append('support has repeated projective points')
        if any(p not in pt_set for p in support):
            support_errors.append('support uses a point outside the branch universe')
        if not fixed_set.issubset(support):
            support_errors.append('support omits at least one fixed point')
        if len(support) != rank_s:
            support_errors.append(f'support size {len(support)} != rank_s {rank_s}')
        support_rank1_count = sum(1 for p in support if matrix_rank_of_mask(p) == 1)
        if min_rank1_count is not None and support_rank1_count < min_rank1_count:
            support_errors.append('support violates min_rank1_count')
        if max_rank1_count is not None and support_rank1_count > max_rank1_count:
            support_errors.append('support violates max_rank1_count')

    wang_rows_by_dim = Counter(); wang_rows_by_lb = Counter(); wang_source_by_dim = Counter(); wang_row_var_hist = Counter(); wang_cap_hist = Counter(); wang_fixed_in_hist = Counter()
    wang_added = 0; wang_skipped = 0; wang_empty = 0; wang_violations = 0; wang_max_excess = 0; wang_violation_head = []
    for scan_i, (key, lb0) in enumerate(lut.items(), 1):
        d = int(key) & 0xF
        basis = None
        source = None
        if d in include_dims:
            source = 'include_dim'
        elif d in through_fixed_dims:
            basis = unpack_basis(key)
            if row_contains_all(fixed, basis):
                source = 'through_fixed'
        if source is None and key in seed_keys and d in seed_dims:
            source = 'seed'
        if source is None:
            continue
        if basis is None:
            basis = unpack_basis(key)
        pts_in = subspace_points_from_basis(basis)
        cap = rank_s - int(lb0)
        present_pts = [p for p in pts_in if p in pt_set]
        lits = [p_to_var[p] for p in present_pts]
        fixed_in = sum(1 for p in fixed if p in pts_in)
        wang_rows_by_dim[d] += 1; wang_rows_by_lb[int(lb0)] += 1; wang_source_by_dim[(source, d)] += 1; wang_row_var_hist[len(lits)] += 1; wang_cap_hist[cap] += 1; wang_fixed_in_hist[fixed_in] += 1
        if opb is not None:
            if cap < 0:
                constraints.append('+1 x1 >= 2 ;'); wang_added += 1; wang_empty += 1
            elif len(lits) <= cap:
                wang_skipped += 1
            else:
                constraints.append(le_constraint(lits, cap)); wang_added += 1
        if support is not None:
            occ = sum(1 for p in present_pts if p in support)
            excess = add_or_check_violation(occ, cap)
            if excess:
                wang_violations += 1; wang_max_excess = max(wang_max_excess, excess)
                if len(wang_violation_head) < 20:
                    wang_violation_head.append({'key': int(key), 'dim': d, 'lb': int(lb0), 'cap': cap, 'occ': occ, 'excess': excess})
        if scan_i % 1_000_000 == 0:
            print(f'scanned {scan_i:,}/{len(lut):,}; wang_rows={sum(wang_rows_by_dim.values()):,}; elapsed={time.time()-t0:.1f}s', flush=True)

    r1_pts, r1_cons, r1_meta, r1_lmeta = load_or_build_rank1_projection(rank1_cache, lut_path, rank_s, False)
    r1_groups_hist = Counter(); r1_row_var_hist = Counter(); r1_cap_hist = Counter()
    r1_added = 0; r1_skipped = 0; r1_empty = 0; r1_violations = 0; r1_max_excess = 0; r1_violation_head = []
    for mask0, cap0, rkey in r1_cons:
        mask = int(mask0); cap = int(cap0); size = mask.bit_count()
        if rank1_include_groups is not None and (size, cap) not in rank1_include_groups:
            continue
        if rank1_include_groups is None and rank1_max_intersection_size is not None and size > rank1_max_intersection_size:
            continue
        present_r1_pts = []
        y = mask
        while y:
            lb = y & -y
            j = lb.bit_length() - 1
            y ^= lb
            p = int(r1_pts[j])
            if p in pt_set:
                present_r1_pts.append(p)
        lits = [p_to_var[p] for p in present_r1_pts]
        r1_groups_hist[(size, cap)] += 1; r1_row_var_hist[len(lits)] += 1; r1_cap_hist[cap] += 1
        if opb is not None:
            if cap < 0:
                constraints.append('+1 x1 >= 2 ;'); r1_added += 1; r1_empty += 1
            elif len(lits) <= cap:
                r1_skipped += 1
            else:
                constraints.append(le_constraint(lits, cap)); r1_added += 1
        if support is not None:
            occ = sum(1 for p in present_r1_pts if p in support)
            excess = add_or_check_violation(occ, cap)
            if excess:
                r1_violations += 1; r1_max_excess = max(r1_max_excess, excess)
                if len(r1_violation_head) < 20:
                    r1_violation_head.append({'key': int(rkey), 'intersection_size': size, 'cap': cap, 'occ': occ, 'excess': excess})

    if opb is not None:
        opb.parent.mkdir(parents=True, exist_ok=True)
        with opb.open('w') as f:
            f.write(f'* #variable= {len(pts)} #constraint= {len(constraints)} #equal= 0 intsize= 64\n')
            f.write(f'* fixed-E11 Wang support OPB; dense variable map saved in metadata\n')
            for line in constraints:
                f.write(line + '\n')

    payload = {
        'problem': 'fixed-E11 Wang support OPB with rank-1-count range',
        'field': 'F2',
        'rank_s': rank_s,
        'fixed_points': fixed,
        'fixed_extra': list(fixed_extra),
        'exclude_second_orbits_before': exclude_second_orbits_before,
        'min_rank1_count': min_rank1_count,
        'max_rank1_count': max_rank1_count,
        'variable_point_count': len(pts),
        'point_to_var': {str(p): p_to_var[p] for p in pts},
        'var_to_point': {str(v): p for p, v in p_to_var.items()},
        'variable_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in pts).items())),
        'excluded_point_count': len(excluded),
        'excluded_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in excluded).items())),
        'include_dims': sorted(include_dims),
        'through_fixed_dims': sorted(through_fixed_dims),
        'seed_dims': sorted(seed_dims),
        'seed_key_count': len(seed_keys),
        'opb_path': None if opb is None else str(opb),
        'opb_hash': None if opb is None else sha256(opb),
        'opb_constraint_count': len(constraints) if opb is not None else None,
        'opb_equal_count': 0 if opb is not None else None,
        'support_total_equality_ineqs': equality_as_two_ineq,
        'fixed_unit_constraints': fixed_unit_count,
        'wang_rows_added': wang_added,
        'wang_rows_seen': sum(wang_rows_by_dim.values()),
        'wang_rows_by_dim': dict(sorted(wang_rows_by_dim.items())),
        'wang_rows_by_lb': dict(sorted(wang_rows_by_lb.items())),
        'wang_source_by_dim': {f'{s},{d}': c for (s, d), c in sorted(wang_source_by_dim.items())},
        'wang_row_var_hist': dict(sorted(wang_row_var_hist.items())),
        'wang_cap_hist': dict(sorted(wang_cap_hist.items())),
        'wang_fixed_in_row_hist': dict(sorted(wang_fixed_in_hist.items())),
        'wang_skipped_vacuous': wang_skipped,
        'wang_empty': wang_empty,
        'rank1_projection_cache_meta_brief': {'compressed_intersections': r1_meta.get('compressed_intersections'), 'nonvacuous_constraints': r1_meta.get('nonvacuous_constraints'), 'lut_coverage_ok': r1_lmeta.get('coverage_ok'), 'lut_conflict_count': r1_lmeta.get('conflict_count')},
        'rank1_projection_filter': {'max_intersection_size': rank1_max_intersection_size, 'include_groups': None if rank1_include_groups is None else sorted([list(g) for g in rank1_include_groups])},
        'rank1_projection_rows_added': r1_added,
        'rank1_projection_rows_seen': sum(r1_groups_hist.values()),
        'rank1_projection_skipped_vacuous': r1_skipped,
        'rank1_projection_empty': r1_empty,
        'rank1_projection_hist': {f'{a},{b}': c for (a, b), c in sorted(r1_groups_hist.items())},
        'rank1_projection_row_var_hist': dict(sorted(r1_row_var_hist.items())),
        'rank1_projection_cap_hist': dict(sorted(r1_cap_hist.items())),
        'support_json': None if support_json is None else str(support_json),
        'support_errors': support_errors,
        'support_rank1_count': support_rank1_count,
        'support_wang_violation_count': None if support is None else wang_violations,
        'support_wang_max_excess': None if support is None else wang_max_excess,
        'support_wang_violation_head': wang_violation_head,
        'support_rank1_projection_violation_count': None if support is None else r1_violations,
        'support_rank1_projection_max_excess': None if support is None else r1_max_excess,
        'support_rank1_projection_violation_head': r1_violation_head,
        'lut_meta_brief': {'coverage_ok': lut_meta.get('coverage_ok'), 'conflict_count': lut_meta.get('conflict_count'), 'subspace_count': lut_meta.get('subspace_count')},
        'elapsed_sec': time.time() - t0,
        'meaning': 'Native PB encoding/evaluation of the same Wang necessary-condition row families used by the CP-SAT range tool. A solver proof must be checked separately before theorem use.',
    }
    meta_path.parent.mkdir(parents=True, exist_ok=True)
    meta_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    brief_keys = ['variable_point_count', 'opb_constraint_count', 'wang_rows_added', 'rank1_projection_rows_added', 'support_wang_violation_count', 'support_rank1_projection_violation_count', 'elapsed_sec']
    print(json.dumps({k: payload[k] for k in brief_keys}, indent=2, sort_keys=True))
    return payload


def run_roundingsat(opb: Path, proof_log: Path, solver_log: Path, solver: Path, timeout: int, extra_args: Sequence[str]) -> dict:
    proof_log.parent.mkdir(parents=True, exist_ok=True)
    solver_log.parent.mkdir(parents=True, exist_ok=True)
    cmd = [str(solver), '--lp=0', f'--proof-log={proof_log}', *extra_args, str(opb)]
    t0 = time.time()
    with solver_log.open('w') as f:
        try:
            proc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, text=True, timeout=timeout if timeout > 0 else None)
            exit_code = proc.returncode
            timed_out = False
        except subprocess.TimeoutExpired:
            exit_code = -1
            timed_out = True
    text = solver_log.read_text(errors='replace') if solver_log.exists() else ''
    status = {
        'cmd': cmd,
        'exit_code': exit_code,
        'timed_out': timed_out,
        'elapsed_sec': time.time() - t0,
        'opb': str(opb),
        'proof_log': str(proof_log),
        'solver_log': str(solver_log),
        'proof_log_bytes': proof_log.stat().st_size if proof_log.exists() else 0,
        'solver_log_bytes': solver_log.stat().st_size if solver_log.exists() else 0,
        'solver_s_unsat': 's UNSATISFIABLE' in text,
        'solver_s_sat': 's SATISFIABLE' in text,
        'hashes': {str(p): sha256(p) for p in [opb, proof_log, solver_log] if p.exists()},
    }
    status_path = solver_log.with_suffix('.status.json')
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + '\n')
    print(json.dumps(status, indent=2, sort_keys=True))
    return status


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=DEFAULT_LUT)
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--fixed-extra', default='')
    ap.add_argument('--exclude-second-orbits-before', action='store_true')
    ap.add_argument('--include-dims', default='1,2,3')
    ap.add_argument('--through-fixed-dims', default='4-8')
    ap.add_argument('--seed-json', type=Path, action='append', default=[])
    ap.add_argument('--seed-dims', default='4-8')
    ap.add_argument('--rank1-cache', type=Path, default=DEFAULT_R1_CACHE)
    ap.add_argument('--rank1-max-intersection-size', type=int, default=None)
    ap.add_argument('--rank1-include-groups', default='')
    ap.add_argument('--min-rank1-count', type=int, default=None)
    ap.add_argument('--max-rank1-count', type=int, default=None)
    ap.add_argument('--opb', type=Path, default=None)
    ap.add_argument('--meta', type=Path, required=True)
    ap.add_argument('--support-json', type=Path, default=None)
    ap.add_argument('--solve-roundingsat', action='store_true')
    ap.add_argument('--roundingsat', type=Path, default=DEFAULT_ROUNDINGSAT)
    ap.add_argument('--proof-log', type=Path, default=None)
    ap.add_argument('--solver-log', type=Path, default=None)
    ap.add_argument('--solver-time', type=int, default=0)
    ap.add_argument('--solver-extra-arg', action='append', default=[])
    args = ap.parse_args()

    fixed_extra = parse_ints(args.fixed_extra)
    seed_keys: Set[int] = set()
    for p in args.seed_json:
        got = collect_violation_keys(p)
        print(f'seed {p}: {len(got)} keys', flush=True)
        seed_keys.update(got)
    lut, lmeta = load_lut(args.lut)
    print(f'loaded LUT {len(lut):,} coverage={lmeta.get("coverage_ok")} conflicts={lmeta.get("conflict_count")}', flush=True)
    generate_or_check(
        lut, lmeta, lut_path=args.lut, rank_s=args.rank, fixed_extra=fixed_extra,
        exclude_second_orbits_before=args.exclude_second_orbits_before,
        min_rank1_count=args.min_rank1_count, max_rank1_count=args.max_rank1_count,
        include_dims=parse_dims(args.include_dims), through_fixed_dims=parse_dims(args.through_fixed_dims),
        seed_keys=seed_keys, seed_dims=parse_dims(args.seed_dims), rank1_cache=args.rank1_cache,
        rank1_max_intersection_size=args.rank1_max_intersection_size,
        rank1_include_groups=parse_groups(args.rank1_include_groups),
        opb=args.opb, meta_path=args.meta, support_json=args.support_json,
    )
    if args.solve_roundingsat:
        if args.opb is None:
            raise SystemExit('--solve-roundingsat requires --opb')
        proof = args.proof_log or args.opb.with_suffix('.pbp')
        slog = args.solver_log or args.opb.with_suffix('.roundingsat.log')
        run_roundingsat(args.opb, proof, slog, args.roundingsat, args.solver_time, args.solver_extra_arg)


if __name__ == '__main__':
    main()
