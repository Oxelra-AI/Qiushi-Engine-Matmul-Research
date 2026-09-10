#!/usr/bin/env python3
"""Proof-producing CNF from an explicit fixed-branch Wang row core.

Input is a JSON file produced by rep10_exactk_row_core_cp.py or
rep10_mus_core_cp.py containing `core_keys`.  The CNF keeps the original branch
variables (fixed E11 plus fixed-extra, optional earlier-orbit exclusions), the
total support cardinality, an optional exact rank-1 count, and exactly the
listed Wang occupation rows.  It does not remove support variables using
CP-SAT singleton/pair conclusions.  Thus a verified DRAT proves precisely the
row-core implication that CP-SAT suggested.
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
from typing import Sequence

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_cnf_e11_fixed import E11, stab_e11_orbits  # noqa: E402
from wang_capacity_lazy import matrix_rank_of_mask, subspace_points_from_basis, unpack_basis  # noqa: E402


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

    def add_clauses(self, clauses):
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
    excluded = set()
    if exclude_second_orbits_before:
        if len(fixed_extra) != 1:
            raise ValueError('exclude_second_orbits_before requires exactly one fixed-extra point')
        second = int(fixed_extra[0])
        found = False
        for orb in stab_e11_orbits():
            if int(orb['rep']) == second:
                found = True
                break
            excluded.update(int(p) for p in orb['members'])
        if not found:
            raise ValueError(f'{second} is not a Stab(E11) representative')
        for p in fixed:
            excluded.discard(p)
    pts = [p for p in range(1, 512) if p not in excluded]
    p_to_var = {p: i + 1 for i, p in enumerate(pts)}
    for p in fixed:
        if p not in p_to_var:
            raise ValueError(f'fixed point {p} excluded')
    return fixed, excluded, pts, p_to_var


def encode_atmost(writer: DimacsWriter, lits: list[int], cap: int, top_id: int, direct_comb_limit: int):
    if cap < 0:
        writer.add_clause([])
        return top_id, 1, 0, 'empty', 1
    if len(lits) <= cap:
        return top_id, 0, 0, 'skip', 0
    combs = math.comb(len(lits), cap + 1) if cap + 1 <= len(lits) else 0
    if combs <= direct_comb_limit:
        for comb in itertools.combinations(lits, cap + 1):
            writer.add_clause([-v for v in comb])
        return top_id, combs, 0, 'direct', combs
    top_id, ncl, naux = add_card(writer, lits, 'atmost', cap, top_id)
    return top_id, ncl, naux, 'card', combs


def generate(lut, lmeta, core_payload, *, rank_s: int, fixed_extra: Sequence[int],
             exclude_second_orbits_before: bool, exact_rank1_count: int | None,
             cnf: Path, meta_path: Path, direct_comb_limit: int):
    t0 = time.time()
    core_keys = [int(k) for k in core_payload.get('core_keys', [])]
    if not core_keys:
        raise ValueError('row-core JSON has no core_keys')
    fixed, excluded, pts, p_to_var = branch_points(fixed_extra, exclude_second_orbits_before)
    fixed_set = set(fixed)
    writer = DimacsWriter(cnf)
    top = len(pts)

    for p in fixed:
        writer.add_clause([p_to_var[p]])
    top, global_ncl, global_naux = add_card(writer, [p_to_var[p] for p in pts], 'equals', rank_s, top)
    rank1_lits = [p_to_var[p] for p in pts if matrix_rank_of_mask(p) == 1]
    r1_ncl = r1_naux = 0
    if exact_rank1_count is not None:
        top, r1_ncl, r1_naux = add_card(writer, rank1_lits, 'equals', int(exact_rank1_count), top)

    row_hist = Counter(); row_var_hist = Counter(); cap_hist = Counter(); fixed_in_hist = Counter(); by_source = Counter()
    added = skipped = empty = direct_rows = direct_clauses = card_rows = card_clauses = aux = 0
    witness_head = []
    for key in core_keys:
        if key not in lut:
            raise ValueError(f'core key {key} is not in LUT')
        lb0 = int(lut[key])
        basis = unpack_basis(key)
        pts_in = subspace_points_from_basis(basis)
        cap = rank_s - lb0
        fixed_in = sum(1 for p in fixed if p in pts_in)
        cap_rem = cap - fixed_in
        lits = [p_to_var[p] for p in pts_in if p in p_to_var and p not in fixed_set]
        d = int(key) & 0xF
        row_hist[(d, lb0)] += 1; row_var_hist[len(lits)] += 1; cap_hist[cap_rem] += 1; fixed_in_hist[fixed_in] += 1
        source = None
        for rec in core_payload.get('core_rows_preview', []):
            if int(rec.get('key', -1)) == key:
                source = rec.get('source')
                break
        by_source[source or 'unknown'] += 1
        old_top = top
        top, ncl, naux, mode, combs = encode_atmost(writer, lits, cap_rem, top, direct_comb_limit)
        if mode == 'skip':
            skipped += 1
        elif mode == 'empty':
            added += 1; empty += 1
        elif mode == 'direct':
            added += 1; direct_rows += 1; direct_clauses += ncl
        elif mode == 'card':
            added += 1; card_rows += 1; card_clauses += ncl; aux += naux
        if top < old_top:
            raise RuntimeError('top id decreased')
        if len(witness_head) < 80:
            witness_head.append({'key': key, 'dim': d, 'lb': lb0, 'cap_rem': cap_rem,
                                 'fixed_in': fixed_in, 'var_count': len(lits),
                                 'basis': list(basis), 'mode': mode,
                                 'clauses_if_direct': combs})

    writer.close_with_header(top)
    payload = {
        'problem': 'CNF replay of explicit Wang row-core branch',
        'field': 'F2',
        'rank_s': rank_s,
        'fixed_points': fixed,
        'fixed_extra': list(fixed_extra),
        'exclude_second_orbits_before': exclude_second_orbits_before,
        'exact_rank1_count': exact_rank1_count,
        'variable_point_count': len(pts),
        'variable_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in pts).items())),
        'excluded_point_count': len(excluded),
        'excluded_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in excluded).items())),
        'core_source_problem': core_payload.get('problem'),
        'core_source_exact_rank1_count': core_payload.get('exact_rank1_count'),
        'core_source_final_check': core_payload.get('final_check'),
        'core_key_count': len(core_keys),
        'core_rows_added': added,
        'core_rows_skipped_vacuous': skipped,
        'core_rows_empty': empty,
        'core_rows_by_dim_lb': {f'{d},{lb}': c for (d, lb), c in sorted(row_hist.items())},
        'core_row_var_hist': dict(sorted(row_var_hist.items())),
        'core_residual_cap_hist': dict(sorted(cap_hist.items())),
        'core_fixed_in_row_hist': dict(sorted(fixed_in_hist.items())),
        'core_source_hist_preview': dict(sorted(by_source.items())),
        'direct_rows': direct_rows,
        'direct_capacity_clauses': direct_clauses,
        'cardinality_capacity_rows': card_rows,
        'cardinality_capacity_clauses': card_clauses,
        'capacity_aux_vars': aux,
        'global_cardinality_clauses': global_ncl,
        'global_cardinality_aux_vars': global_naux,
        'rank1_count_clauses': r1_ncl,
        'rank1_count_aux_vars': r1_naux,
        'num_vars': top,
        'num_clauses': writer.nclauses,
        'empty_clause_count': writer.empty_clause_count,
        'direct_comb_limit': direct_comb_limit,
        'witness_head': witness_head,
        'cnf_path': str(cnf),
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'elapsed_sec': time.time() - t0,
        'meaning': 'UNSAT with verified DRAT proves this exact rank-1-count branch infeasible under the explicit listed Wang rows; it does not depend on CP-SAT removal of support variables.',
    }
    meta_path.parent.mkdir(parents=True, exist_ok=True)
    meta_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: payload[k] for k in ['core_key_count','num_vars','num_clauses','empty_clause_count','core_rows_added','elapsed_sec']}, indent=2, sort_keys=True))
    return payload


def parse_solver_log(path: Path) -> dict:
    if not path.exists():
        return {'exists': False}
    text = path.read_text(errors='replace')
    return {'exists': True, 'unsat': 's UNSATISFIABLE' in text, 'sat': 's SATISFIABLE' in text, 'verified': 's VERIFIED' in text}


def run_solver(cnf: Path, timeout: int):
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
    status = {'cnf': str(cnf), 'drat': str(drat), 'cadical_log': str(cadlog),
              'drat_trim_log': str(trimlog), 'cadical_exit': proc.returncode,
              'cadical_elapsed_sec': time.time() - t0}
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--core-json', type=Path, required=True)
    ap.add_argument('--rank', type=int, default=20)
    ap.add_argument('--fixed-extra', default='10')
    ap.add_argument('--exclude-second-orbits-before', action='store_true')
    ap.add_argument('--exact-rank1-count', type=int, default=None)
    ap.add_argument('--direct-comb-limit', type=int, default=2000)
    ap.add_argument('--cnf', type=Path, required=True)
    ap.add_argument('--meta', type=Path, required=True)
    ap.add_argument('--solve', action='store_true')
    ap.add_argument('--solver-time', type=int, default=0)
    args = ap.parse_args()
    lut, lmeta = load_lut(args.lut)
    core_payload = json.loads(args.core_json.read_text())
    fixed_extra = parse_ints(args.fixed_extra)
    generate(lut, lmeta, core_payload, rank_s=args.rank, fixed_extra=fixed_extra,
             exclude_second_orbits_before=args.exclude_second_orbits_before,
             exact_rank1_count=args.exact_rank1_count, cnf=args.cnf,
             meta_path=args.meta, direct_comb_limit=args.direct_comb_limit)
    if args.solve:
        run_solver(args.cnf, args.solver_time)


if __name__ == '__main__':
    main()
