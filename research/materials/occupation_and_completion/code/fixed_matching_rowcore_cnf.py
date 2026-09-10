#!/usr/bin/env python3
"""Proof-producing CNF for a fixed rank-1 matching stratum row core.

Input: a lazy fixed-matching record from matching_stratum_lazy.py or
matching_stratum_lazy_bulk.py.  The formula fixes exactly the listed
rank-1 matching (including E11), uses Boolean variables only for higher-rank
projective A-points, selects exactly 20-k higher-rank points, and encodes the
Wang row keys appearing in the lazy record's cut_records with residual capacity
20-L(Phi)-|M cap Phi|.

A verified DRAT UNSAT proves this fixed matching stratum infeasible under the
explicit row core, independent of CP-SAT.  It remains an F2 Wang-support
component, not a characteristic-zero matrix-multiplication lower bound.
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

from wang_capacity_cnf_e11_fixed import E11  # noqa: E402
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


def outer_mask(u: int, v: int) -> int:
    mask = 0
    for i in range(3):
        if (u >> i) & 1:
            mask |= int(v) << (3 * i)
    return mask


def rank1_points() -> set[int]:
    return {p for p in range(1, 512) if matrix_rank_of_mask(p) == 1}


def uv_map() -> dict[int, tuple[int, int]]:
    out = {outer_mask(u, v): (u, v) for u in range(1, 8) for v in range(1, 8)}
    if set(out) != rank1_points() or out.get(E11) != (1, 1):
        raise RuntimeError('rank1 uv map mismatch')
    return out


def matching_ok(points: Sequence[int]) -> bool:
    uv = uv_map()
    us: set[int] = set(); vs: set[int] = set()
    for p in points:
        if int(p) not in uv:
            return False
        u, v = uv[int(p)]
        if u in us or v in vs:
            return False
        us.add(u); vs.add(v)
    return True


def parse_solver_log(path: Path) -> dict:
    if not path.exists():
        return {'exists': False}
    text = path.read_text(errors='replace')
    return {
        'exists': True,
        'unsat': 's UNSATISFIABLE' in text,
        'sat': 's SATISFIABLE' in text,
        'verified': 's VERIFIED' in text or 'VERIFIED' in text,
        'head': text[:1000],
        'tail': text[-1000:],
    }


class DimacsWriter:
    def __init__(self, final_path: Path):
        self.final_path = final_path
        self.body_path = final_path.with_suffix(final_path.suffix + '.body.tmp')
        self.final_path.parent.mkdir(parents=True, exist_ok=True)
        self.fh = self.body_path.open('w')
        self.nclauses = 0
        self.empty_clause_count = 0

    def add_clause(self, clause: Sequence[int]) -> None:
        self.fh.write(' '.join(map(str, clause)) + ' 0\n')
        self.nclauses += 1
        if not clause:
            self.empty_clause_count += 1

    def add_clauses(self, clauses: Sequence[Sequence[int]]) -> None:
        for cl in clauses:
            self.add_clause(cl)

    def close_with_header(self, nv: int) -> None:
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
    old = top_id
    top_id, ncl, naux = add_card(writer, lits, 'atmost', cap, top_id)
    if top_id < old:
        raise RuntimeError('top id decreased')
    return top_id, ncl, naux, 'card', combs


def extract_core_keys(lazy_payload: dict, only_effective: bool) -> list[int]:
    direct_field = 'core_keys_effective' if only_effective else 'core_keys_all'
    if lazy_payload.get(direct_field):
        return sorted({int(k) for k in lazy_payload[direct_field]})
    if (not only_effective) and lazy_payload.get('core_keys_effective'):
        return sorted({int(k) for k in lazy_payload['core_keys_effective']})
    keys = []
    seen = set()
    for rec in lazy_payload.get('cut_records', []):
        mode = rec.get('mode')
        if only_effective and mode == 'vacuous':
            continue
        key = int(rec['key'])
        if key not in seen:
            seen.add(key)
            keys.append(key)
    if not keys:
        raise ValueError('no core keys extracted; rerun the lazy solver after analysis core_keys patch')
    return keys


def generate(lut, lmeta, lazy_payload: dict, *, cnf: Path, meta: Path, direct_comb_limit: int, only_effective: bool) -> dict:
    t0 = time.time()
    rank_s = int(lazy_payload.get('rank_s', 20))
    matching = sorted(int(p) for p in lazy_payload['fixed_rank1_matching'])
    if E11 not in matching or not matching_ok(matching):
        raise ValueError(f'bad fixed matching {matching}')
    r1 = rank1_points()
    hr_pts = [p for p in range(1, 512) if p not in r1]
    target_hr = rank_s - len(matching)
    if target_hr != int(lazy_payload.get('target_higher_rank_count', target_hr)):
        raise ValueError('target_hr mismatch')
    p_to_var = {p: i + 1 for i, p in enumerate(hr_pts)}
    writer = DimacsWriter(cnf)
    top = len(hr_pts)
    top, glob_ncl, glob_naux = add_card(writer, [p_to_var[p] for p in hr_pts], 'equals', target_hr, top)

    core_keys = extract_core_keys(lazy_payload, only_effective=only_effective)
    row_hist = Counter(); row_var_hist = Counter(); cap_hist = Counter(); fixed_occ_hist = Counter(); mode_hist = Counter(); reason_hist = Counter()
    added = skipped = empty = direct_rows = card_rows = direct_clauses = card_clauses = cap_aux = 0
    witness_head = []
    lazy_rec_by_key = {}
    for rec in lazy_payload.get('cut_records', []):
        lazy_rec_by_key.setdefault(int(rec['key']), rec)
    for key in core_keys:
        lazy_rec_by_key.setdefault(int(key), {'key': int(key), 'reason': 'core_key_list', 'mode': 'unknown'})
    for key in core_keys:
        if key not in lut:
            raise ValueError(f'core key {key} not in LUT')
        lb = int(lut[key])
        basis = unpack_basis(key)
        pts = subspace_points_from_basis(basis)
        fixed_occ = sum(1 for p in matching if p in pts)
        cap = rank_s - lb - fixed_occ
        lits = [p_to_var[p] for p in pts if p in p_to_var]
        d = key & 0xF
        row_hist[(d, lb)] += 1; row_var_hist[len(lits)] += 1; cap_hist[cap] += 1; fixed_occ_hist[fixed_occ] += 1
        reason_hist[lazy_rec_by_key.get(key, {}).get('reason', 'unknown')] += 1
        top, ncl, naux, mode, combs = encode_atmost(writer, lits, cap, top, direct_comb_limit)
        mode_hist[mode] += 1
        if mode == 'skip':
            skipped += 1
        elif mode == 'empty':
            added += 1; empty += 1
        elif mode == 'direct':
            added += 1; direct_rows += 1; direct_clauses += ncl
        elif mode == 'card':
            added += 1; card_rows += 1; card_clauses += ncl; cap_aux += naux
        if len(witness_head) < 100:
            lr = lazy_rec_by_key.get(key, {})
            witness_head.append({
                'key': key, 'dim': d, 'lb': lb, 'fixed_rank1_occ': fixed_occ,
                'residual_cap': cap, 'hr_var_count': len(lits), 'mode': mode,
                'clauses_if_direct': combs, 'lazy_reason': lr.get('reason'),
                'lazy_mode': lr.get('mode'), 'basis': list(basis),
            })
    writer.close_with_header(top)
    payload = {
        'problem': 'CNF replay of fixed rank-1 matching stratum row core',
        'field': 'F2',
        'rank_s': rank_s,
        'fixed_rank1_matching': matching,
        'fixed_rank1_matching_uv': [{'point': p, 'u': uv_map()[p][0], 'v': uv_map()[p][1]} for p in matching],
        'target_higher_rank_count': target_hr,
        'variable_point_count': len(hr_pts),
        'variable_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in hr_pts).items())),
        'source_lazy_problem': lazy_payload.get('problem'),
        'source_lazy_path_recorded': lazy_payload.get('source_path'),
        'source_lazy_final_status': lazy_payload.get('final_status'),
        'source_lazy_iteration_count': lazy_payload.get('iteration_count'),
        'source_lazy_cut_count_total': lazy_payload.get('cut_count_total'),
        'only_effective_core_keys': bool(only_effective),
        'core_key_count': len(core_keys),
        'core_rows_added': added,
        'core_rows_skipped_vacuous': skipped,
        'core_rows_empty': empty,
        'core_rows_by_dim_lb': {f'{d},{lb}': c for (d, lb), c in sorted(row_hist.items())},
        'core_row_var_hist': dict(sorted(row_var_hist.items())),
        'core_residual_cap_hist': dict(sorted(cap_hist.items())),
        'core_fixed_rank1_occ_hist': dict(sorted(fixed_occ_hist.items())),
        'core_reencoded_mode_hist': dict(sorted(mode_hist.items())),
        'core_lazy_reason_hist': dict(sorted(reason_hist.items())),
        'direct_rows': direct_rows,
        'direct_capacity_clauses': direct_clauses,
        'cardinality_capacity_rows': card_rows,
        'cardinality_capacity_clauses': card_clauses,
        'capacity_aux_vars': cap_aux,
        'global_cardinality_clauses': glob_ncl,
        'global_cardinality_aux_vars': glob_naux,
        'num_vars': top,
        'num_clauses': writer.nclauses,
        'empty_clause_count': writer.empty_clause_count,
        'direct_comb_limit': direct_comb_limit,
        'witness_head': witness_head,
        'cnf_path': str(cnf),
        'meta_path': str(meta),
        'lut_meta_brief': {'coverage_ok': lmeta.get('coverage_ok'), 'conflict_count': lmeta.get('conflict_count'), 'subspace_count': lmeta.get('subspace_count')},
        'elapsed_sec': time.time() - t0,
        'meaning': 'UNSAT with a verified DRAT trace proves this exact fixed rank-1 matching stratum infeasible under the listed Wang rows.',
    }
    meta.parent.mkdir(parents=True, exist_ok=True)
    meta.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'core_key_count': payload['core_key_count'],
        'core_rows_added': payload['core_rows_added'],
        'num_vars': payload['num_vars'],
        'num_clauses': payload['num_clauses'],
        'empty_clause_count': payload['empty_clause_count'],
        'core_reencoded_mode_hist': payload['core_reencoded_mode_hist'],
        'cnf_path': str(cnf),
        'meta_path': str(meta),
        'elapsed_sec': payload['elapsed_sec'],
    }, indent=2, sort_keys=True), flush=True)
    return payload


def run_solver(cnf: Path, meta: Path, timeout: int) -> dict:
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
    status = {
        'cnf': str(cnf), 'meta': str(meta), 'drat': str(drat),
        'cadical_log': str(cadlog), 'drat_trim_log': str(trimlog),
        'cadical_exit': proc.returncode,
        'cadical_elapsed_sec': time.time() - t0,
    }
    if proc.returncode == 20:
        t1 = time.time()
        with trimlog.open('w') as f:
            trim = subprocess.run(['drat-trim', str(cnf), str(drat)], stdout=f, stderr=subprocess.STDOUT, text=True)
        status['drat_trim_exit'] = trim.returncode
        status['drat_trim_elapsed_sec'] = time.time() - t1
    else:
        status['drat_trim_exit'] = None
        status['drat_trim_elapsed_sec'] = None
    paths = [cnf, meta, drat, cadlog, trimlog]
    status['hashes'] = {str(p): sha256(p) for p in paths if p.exists()}
    status['cadical_log_parse'] = parse_solver_log(cadlog)
    status['drat_trim_log_parse'] = parse_solver_log(trimlog)
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'cadical_exit': status['cadical_exit'],
        'cadical_elapsed_sec': status['cadical_elapsed_sec'],
        'drat_trim_exit': status['drat_trim_exit'],
        'drat_trim_elapsed_sec': status['drat_trim_elapsed_sec'],
        'cadical_unsat': status['cadical_log_parse'].get('unsat'),
        'trim_verified': status['drat_trim_log_parse'].get('verified'),
        'status_path': str(status_path),
    }, indent=2, sort_keys=True), flush=True)
    return status


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--lazy-json', type=Path, required=True)
    ap.add_argument('--cnf', type=Path, required=True)
    ap.add_argument('--meta', type=Path, required=True)
    ap.add_argument('--direct-comb-limit', type=int, default=2000)
    ap.add_argument('--include-vacuous-core-keys', action='store_true')
    ap.add_argument('--solve', action='store_true')
    ap.add_argument('--solver-time', type=int, default=0)
    args = ap.parse_args()
    lut, lmeta = load_lut(args.lut)
    lazy = json.loads(args.lazy_json.read_text())
    lazy['source_path'] = str(args.lazy_json)
    generate(lut, lmeta, lazy, cnf=args.cnf, meta=args.meta,
             direct_comb_limit=args.direct_comb_limit,
             only_effective=not args.include_vacuous_core_keys)
    if args.solve:
        run_solver(args.cnf, args.meta, args.solver_time)


if __name__ == '__main__':
    main()
