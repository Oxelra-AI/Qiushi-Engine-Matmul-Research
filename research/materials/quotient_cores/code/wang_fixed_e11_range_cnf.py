#!/usr/bin/env python3
"""Proof-producing CNF for fixed-E11 Wang supports with a rank-1-count range.

This is the DIMACS/DRAT counterpart of wang_fixed_e11_range_cpsat.py.  It fixes
E11, optionally fixes one additional Stab(E11)-orbit representative and omits
earlier second-orbit points, constrains the total support size, constrains the
number of selected rank-1 projective A-directions to an exact value or interval,
and encodes selected Wang occupation rows plus the compressed rank-1 projection.

UNSAT with a verified DRAT trace is a leaf in the finite F2 Wang support branch.
SAT is only an A-support candidate and must still be scanned against the complete
Wang LUT before any algebraic interpretation.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import pickle
import shutil
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Sequence, Set

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from rank1_capacity_profile import load_or_build as load_or_build_rank1_projection  # noqa: E402
from wang_capacity_cnf_e11_fixed import E11, collect_violation_keys, parse_dims, stab_e11_orbits  # noqa: E402
from wang_capacity_lazy import in_rowspace, matrix_rank_of_mask, unpack_basis, subspace_points_from_basis  # noqa: E402


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
            raise ValueError(f'bad group {part!r}')
        out.add((int(a), int(b)))
    return out


class DimacsWriter:
    def __init__(self, final_path: Path):
        self.final_path = final_path
        self.body_path = final_path.with_suffix(final_path.suffix + '.body.tmp')
        self.final_path.parent.mkdir(parents=True, exist_ok=True)
        self.fh = self.body_path.open('w')
        self.nclauses = 0
        self.empty_clause_count = 0

    def add_clause(self, clause: Sequence[int]):
        self.fh.write(' '.join(map(str, clause)) + ' 0\n')
        self.nclauses += 1
        if not clause:
            self.empty_clause_count += 1

    def add_clauses(self, clauses: Sequence[Sequence[int]]):
        for cl in clauses:
            self.add_clause(cl)

    def close_with_header(self, nv: int):
        self.fh.close()
        with self.final_path.open('w') as out:
            out.write(f'p cnf {nv} {self.nclauses}\n')
            with self.body_path.open('r') as body:
                shutil.copyfileobj(body, out, length=16 * 1024 * 1024)
        self.body_path.unlink(missing_ok=True)


def add_card(writer: DimacsWriter, lits: list[int], relation: str, bound: int, top_id: int):
    from pysat.card import CardEnc, EncType
    if relation == 'atmost':
        if bound < 0:
            writer.add_clause([])
            return top_id, 1, 0
        if len(lits) <= bound:
            return top_id, 0, 0
        enc = CardEnc.atmost(lits=lits, bound=bound, top_id=top_id, encoding=EncType.seqcounter)
    elif relation == 'atleast':
        if bound <= 0:
            return top_id, 0, 0
        if len(lits) < bound:
            writer.add_clause([])
            return top_id, 1, 0
        enc = CardEnc.atleast(lits=lits, bound=bound, top_id=top_id, encoding=EncType.seqcounter)
    elif relation == 'equals':
        if bound < 0 or bound > len(lits):
            writer.add_clause([])
            return top_id, 1, 0
        enc = CardEnc.equals(lits=lits, bound=bound, top_id=top_id, encoding=EncType.seqcounter)
    else:
        raise ValueError(relation)
    writer.add_clauses(enc.clauses)
    return enc.nv, len(enc.clauses), max(0, enc.nv - top_id)


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


def encode_atmost_row(writer: DimacsWriter, lits: list[int], cap: int, top_id: int, direct_comb_limit: int):
    if cap < 0:
        writer.add_clause([])
        return top_id, 1, 0, 'empty', 1
    if len(lits) <= cap:
        return top_id, 0, 0, 'skip', 0
    combs = math.comb(len(lits), cap + 1) if cap + 1 <= len(lits) else 0
    if cap >= 0 and combs <= direct_comb_limit:
        for comb in itertools.combinations(lits, cap + 1):
            writer.add_clause([-v for v in comb])
        return top_id, combs, 0, 'direct', combs
    top_id, ncl, naux = add_card(writer, lits, 'atmost', cap, top_id)
    return top_id, ncl, naux, 'card', combs


def row_contains_fixed(basis: Sequence[int], fixed: Sequence[int]) -> bool:
    return all(in_rowspace(p, basis, n=9) for p in fixed)


def generate(lut: Dict[int, int], lut_meta: dict, *, lut_path: Path, rank_s: int, fixed_extra: Sequence[int],
             exclude_second_orbits_before: bool, include_dims: Set[int], through_fixed_dims: Set[int],
             seed_keys: Set[int], seed_dims: Set[int], rank1_cache: Path,
             exact_rank1_count: int | None, min_rank1_count: int | None, max_rank1_count: int | None,
             rank1_max_intersection_size: int | None, rank1_include_groups: set[tuple[int, int]] | None,
             cnf: Path, meta_path: Path, direct_comb_limit: int) -> dict:
    t0 = time.time()
    fixed, excluded, pts, p_to_var = branch_points(fixed_extra, exclude_second_orbits_before)
    fixed_set = set(fixed)
    fixed_rank1 = [p for p in fixed if matrix_rank_of_mask(p) == 1]
    writer = DimacsWriter(cnf)
    top = len(pts)

    # Fixed unit clauses and total support cardinality.
    for p in fixed:
        writer.add_clause([p_to_var[p]])
    top, global_ncl, global_naux = add_card(writer, [p_to_var[p] for p in pts], 'equals', rank_s, top)

    # Rank-1 count over present rank-1 variables.  Excluded variables are fixed zero by the branch.
    rank1_lits = [p_to_var[p] for p in pts if matrix_rank_of_mask(p) == 1]
    r1_count_clauses = 0; r1_count_aux = 0
    if exact_rank1_count is not None:
        top, ncl, naux = add_card(writer, rank1_lits, 'equals', exact_rank1_count, top)
        r1_count_clauses += ncl; r1_count_aux += naux
    else:
        if min_rank1_count is not None:
            top, ncl, naux = add_card(writer, rank1_lits, 'atleast', min_rank1_count, top)
            r1_count_clauses += ncl; r1_count_aux += naux
        if max_rank1_count is not None:
            top, ncl, naux = add_card(writer, rank1_lits, 'atmost', max_rank1_count, top)
            r1_count_clauses += ncl; r1_count_aux += naux

    # Selected full Wang rows.
    wang_rows_by_dim = Counter(); wang_rows_by_lb = Counter(); wang_source_by_dim = Counter(); wang_row_var_hist = Counter(); wang_cap_hist = Counter(); wang_fixed_in_hist = Counter()
    wang_added = 0; wang_skipped = 0; wang_empty = 0; wang_direct_rows = 0; wang_direct_clauses = 0; wang_card_rows = 0; wang_card_clauses = 0; wang_aux = 0
    for idx, (key, lb0) in enumerate(lut.items(), 1):
        d = int(key) & 0xF
        basis = None
        source = None
        if d in include_dims:
            source = 'include_dim'
        elif d in through_fixed_dims:
            basis = unpack_basis(key)
            if row_contains_fixed(basis, fixed):
                source = 'through_fixed'
        if source is None and key in seed_keys and d in seed_dims:
            source = 'seed'
        if source is None:
            continue
        if basis is None:
            basis = unpack_basis(key)
        pts_in = subspace_points_from_basis(basis)
        cap = rank_s - int(lb0)
        fixed_in = sum(1 for p in fixed if p in pts_in)
        cap_rem = cap - fixed_in
        lits = [p_to_var[p] for p in pts_in if p in p_to_var and p not in fixed_set]
        wang_rows_by_dim[d] += 1; wang_rows_by_lb[int(lb0)] += 1; wang_source_by_dim[(source, d)] += 1; wang_row_var_hist[len(lits)] += 1; wang_cap_hist[cap_rem] += 1; wang_fixed_in_hist[fixed_in] += 1
        old_top = top
        top, ncl, naux, mode, combs = encode_atmost_row(writer, lits, cap_rem, top, direct_comb_limit)
        if mode == 'skip':
            wang_skipped += 1
        elif mode == 'empty':
            wang_added += 1; wang_empty += 1
        elif mode == 'direct':
            wang_added += 1; wang_direct_rows += 1; wang_direct_clauses += ncl
        elif mode == 'card':
            wang_added += 1; wang_card_rows += 1; wang_card_clauses += ncl; wang_aux += naux
        if top < old_top:
            raise RuntimeError('top id decreased')
        if idx % 1_000_000 == 0:
            print(f'scanned {idx:,}/{len(lut):,}; wang_added={wang_added:,}; elapsed={time.time()-t0:.1f}s', flush=True)

    # Rank-1 projected Wang rows: subtract fixed rank-1 unit variables.
    r1_pts, r1_cons, r1_meta, r1_lmeta = load_or_build_rank1_projection(rank1_cache, lut_path, rank_s, False)
    r1_index = {p: i for i, p in enumerate(r1_pts)}
    rank1_groups_hist = Counter(); rank1_row_var_hist = Counter(); rank1_cap_hist = Counter(); rank1_fixed_in_hist = Counter()
    rank1_added = 0; rank1_skipped = 0; rank1_empty = 0; rank1_direct_rows = 0; rank1_direct_clauses = 0; rank1_card_rows = 0; rank1_card_clauses = 0; rank1_aux = 0
    for mask0, cap0, rkey in r1_cons:
        mask = int(mask0); cap = int(cap0); size = mask.bit_count()
        if rank1_include_groups is not None and (size, cap) not in rank1_include_groups:
            continue
        if rank1_include_groups is None and rank1_max_intersection_size is not None and size > rank1_max_intersection_size:
            continue
        fixed_in = 0
        for p in fixed_rank1:
            j = r1_index.get(p)
            if j is not None and ((mask >> j) & 1):
                fixed_in += 1
        cap_rem = cap - fixed_in
        lits = []
        y = mask
        while y:
            lb = y & -y
            j = lb.bit_length() - 1
            y ^= lb
            p = int(r1_pts[j])
            if p in p_to_var and p not in fixed_set:
                lits.append(p_to_var[p])
        rank1_groups_hist[(size, cap)] += 1; rank1_row_var_hist[len(lits)] += 1; rank1_cap_hist[cap_rem] += 1; rank1_fixed_in_hist[fixed_in] += 1
        old_top = top
        top, ncl, naux, mode, combs = encode_atmost_row(writer, lits, cap_rem, top, direct_comb_limit)
        if mode == 'skip':
            rank1_skipped += 1
        elif mode == 'empty':
            rank1_added += 1; rank1_empty += 1
        elif mode == 'direct':
            rank1_added += 1; rank1_direct_rows += 1; rank1_direct_clauses += ncl
        elif mode == 'card':
            rank1_added += 1; rank1_card_rows += 1; rank1_card_clauses += ncl; rank1_aux += naux
        if top < old_top:
            raise RuntimeError('top id decreased')

    writer.close_with_header(top)
    payload = {
        'problem': 'fixed-E11 Wang support CNF with rank-1-count range',
        'field': 'F2',
        'rank_s': rank_s,
        'fixed_points': fixed,
        'fixed_extra': list(fixed_extra),
        'exclude_second_orbits_before': exclude_second_orbits_before,
        'min_rank1_count': min_rank1_count,
        'max_rank1_count': max_rank1_count,
        'exact_rank1_count': exact_rank1_count,
        'variable_point_count': len(pts),
        'variable_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in pts).items())),
        'excluded_point_count': len(excluded),
        'excluded_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in excluded).items())),
        'include_dims': sorted(include_dims),
        'through_fixed_dims': sorted(through_fixed_dims),
        'seed_dims': sorted(seed_dims),
        'seed_key_count': len(seed_keys),
        'fixed_unit_clauses': len(fixed),
        'global_cardinality_clauses': global_ncl,
        'global_cardinality_aux_vars': global_naux,
        'rank1_count_clauses': r1_count_clauses,
        'rank1_count_aux_vars': r1_count_aux,
        'wang_rows_added': wang_added,
        'wang_rows_by_dim': dict(sorted(wang_rows_by_dim.items())),
        'wang_rows_by_lb': dict(sorted(wang_rows_by_lb.items())),
        'wang_source_by_dim': {f'{s},{d}': c for (s, d), c in sorted(wang_source_by_dim.items())},
        'wang_row_var_hist': dict(sorted(wang_row_var_hist.items())),
        'wang_residual_cap_hist': dict(sorted(wang_cap_hist.items())),
        'wang_fixed_in_row_hist': dict(sorted(wang_fixed_in_hist.items())),
        'wang_skipped_vacuous': wang_skipped,
        'wang_empty': wang_empty,
        'wang_direct_rows': wang_direct_rows,
        'wang_direct_capacity_clauses': wang_direct_clauses,
        'wang_cardinality_capacity_rows': wang_card_rows,
        'wang_cardinality_capacity_clauses': wang_card_clauses,
        'wang_capacity_aux_vars': wang_aux,
        'rank1_projection_cache_meta_brief': {'compressed_intersections': r1_meta.get('compressed_intersections'), 'nonvacuous_constraints': r1_meta.get('nonvacuous_constraints'), 'lut_coverage_ok': r1_lmeta.get('coverage_ok'), 'lut_conflict_count': r1_lmeta.get('conflict_count')},
        'rank1_projection_filter': {'max_intersection_size': rank1_max_intersection_size, 'include_groups': None if rank1_include_groups is None else sorted([list(g) for g in rank1_include_groups])},
        'rank1_projection_rows_added': rank1_added,
        'rank1_projection_skipped_vacuous': rank1_skipped,
        'rank1_projection_empty': rank1_empty,
        'rank1_projection_hist': {f'{a},{b}': c for (a, b), c in sorted(rank1_groups_hist.items())},
        'rank1_projection_row_var_hist': dict(sorted(rank1_row_var_hist.items())),
        'rank1_projection_residual_cap_hist': dict(sorted(rank1_cap_hist.items())),
        'rank1_projection_fixed_in_row_hist': dict(sorted(rank1_fixed_in_hist.items())),
        'rank1_projection_direct_rows': rank1_direct_rows,
        'rank1_projection_direct_capacity_clauses': rank1_direct_clauses,
        'rank1_projection_cardinality_capacity_rows': rank1_card_rows,
        'rank1_projection_cardinality_capacity_clauses': rank1_card_clauses,
        'rank1_projection_capacity_aux_vars': rank1_aux,
        'num_vars': top,
        'num_clauses': writer.nclauses,
        'empty_clause_count': writer.empty_clause_count,
        'direct_comb_limit': direct_comb_limit,
        'cnf_path': str(cnf),
        'lut_meta_brief': {'coverage_ok': lut_meta.get('coverage_ok'), 'conflict_count': lut_meta.get('conflict_count'), 'subspace_count': lut_meta.get('subspace_count')},
        'elapsed_sec': time.time() - t0,
        'meaning': 'UNSAT plus verified DRAT excludes this fixed-E11 rank-1-count branch under the encoded sound Wang row family. SAT is only an A-support candidate needing full-LUT scan.',
    }
    meta_path.parent.mkdir(parents=True, exist_ok=True)
    meta_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: payload[k] for k in ['num_vars', 'num_clauses', 'empty_clause_count', 'wang_rows_added', 'rank1_projection_rows_added', 'elapsed_sec']}, indent=2, sort_keys=True))
    return payload


def parse_solver_log(path: Path) -> dict:
    if not path.exists():
        return {'exists': False}
    text = path.read_text(errors='replace')
    return {'exists': True, 'unsat': 's UNSATISFIABLE' in text, 'sat': 's SATISFIABLE' in text, 'verified': 's VERIFIED' in text}


def run_solver(cnf: Path, timeout: int) -> dict:
    drat = cnf.with_suffix('.drat')
    cadlog = cnf.with_suffix('.cadical.log')
    trimlog = cnf.with_suffix('.drat_trim.log')
    status_path = cnf.with_suffix('.status.json')
    cmd = ['cadical', '--unsat', '--binary=false', '-n']
    if timeout > 0:
        cmd += ['-t', str(timeout)]
    cmd += [str(cnf), str(drat)]
    t0 = time.time()
    with cadlog.open('w') as f:
        proc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, text=True)
    status = {'cnf': str(cnf), 'drat': str(drat), 'cadical_log': str(cadlog), 'drat_trim_log': str(trimlog), 'cadical_exit': proc.returncode, 'cadical_elapsed_sec': time.time() - t0}
    if proc.returncode == 20:
        t1 = time.time()
        with trimlog.open('w') as f:
            trim = subprocess.run(['drat-trim', str(cnf), str(drat)], stdout=f, stderr=subprocess.STDOUT, text=True)
        status['drat_trim_exit'] = trim.returncode
        status['drat_trim_elapsed_sec'] = time.time() - t1
    else:
        status['drat_trim_exit'] = None
        status['drat_trim_elapsed_sec'] = None
    status['hashes'] = {str(p): sha256(p) for p in [cnf, cnf.with_suffix('.meta.json'), drat, cadlog, trimlog] if p.exists()}
    status['cadical_log_parse'] = parse_solver_log(cadlog)
    status['drat_trim_log_parse'] = parse_solver_log(trimlog)
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + '\n')
    print(json.dumps(status, indent=2, sort_keys=True))
    return status


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--fixed-extra', default='')
    ap.add_argument('--exclude-second-orbits-before', action='store_true')
    ap.add_argument('--include-dims', default='1,2,3')
    ap.add_argument('--through-fixed-dims', default='4-8')
    ap.add_argument('--seed-json', type=Path, action='append', default=[])
    ap.add_argument('--seed-dims', default='4-8')
    ap.add_argument('--rank1-cache', type=Path, default=Path('data/wang_capacity_rank1_profile/rank1_intersection_cache.pkl'))
    ap.add_argument('--exact-rank1-count', type=int, default=None)
    ap.add_argument('--min-rank1-count', type=int, default=None)
    ap.add_argument('--max-rank1-count', type=int, default=None)
    ap.add_argument('--rank1-max-intersection-size', type=int, default=None)
    ap.add_argument('--rank1-include-groups', default='')
    ap.add_argument('--direct-comb-limit', type=int, default=2000)
    ap.add_argument('--cnf', type=Path, required=True)
    ap.add_argument('--meta', type=Path, required=True)
    ap.add_argument('--solve', action='store_true')
    ap.add_argument('--solver-time', type=int, default=0)
    args = ap.parse_args()

    fixed_extra = parse_ints(args.fixed_extra)
    seed_keys: Set[int] = set()
    for p in args.seed_json:
        got = collect_violation_keys(p)
        print(f'seed {p}: {len(got)} keys')
        seed_keys.update(got)
    lut, lmeta = load_lut(args.lut)
    print(f'loaded LUT {len(lut):,} coverage={lmeta.get("coverage_ok")} conflicts={lmeta.get("conflict_count")}', flush=True)
    generate(
        lut, lmeta, lut_path=args.lut, rank_s=args.rank, fixed_extra=fixed_extra,
        exclude_second_orbits_before=args.exclude_second_orbits_before,
        include_dims=parse_dims(args.include_dims), through_fixed_dims=parse_dims(args.through_fixed_dims),
        seed_keys=seed_keys, seed_dims=parse_dims(args.seed_dims), rank1_cache=args.rank1_cache,
        exact_rank1_count=args.exact_rank1_count, min_rank1_count=args.min_rank1_count,
        max_rank1_count=args.max_rank1_count,
        rank1_max_intersection_size=args.rank1_max_intersection_size,
        rank1_include_groups=parse_groups(args.rank1_include_groups),
        cnf=args.cnf, meta_path=args.meta, direct_comb_limit=args.direct_comb_limit,
    )
    if args.solve:
        run_solver(args.cnf, args.solver_time)


if __name__ == '__main__':
    main()
