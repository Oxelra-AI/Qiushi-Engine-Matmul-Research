#!/usr/bin/env python3
r"""analysis: proof-producing CNF for exact exchange-neighborhood Wang repair.

This script encodes the same exact local occupation model as
`neighborhood_repair.py`, but as DIMACS CNF so that an UNSAT outcome can
be replayed by CaDiCaL + drat-trim.  Scope is deliberately local: it proves only
that no 19-point distinct E11-core A-support satisfying the complete Wang rows
lies within the chosen exchange radius d of the supplied base support.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable, List, Sequence

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from pysat.card import CardEnc, EncType  # noqa: E402

from complete_core_and_transversal import ROOT, build_core_constraints  # noqa: E402
from core_capacity_from_wang_lut import CoreQuotient  # noqa: E402
from neighborhood_repair import (  # noqa: E402
    DEFAULT_SUPPORT,
    augment_records_with_bitsets,
    filtered_rows,
    load_lut,
    parse_support_arg,
    points_bitset,
    slack_profile,
)

OUTDIR = ROOT / "workspace/data/neighborhood_repair/cnf"


def sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


class CnfWriter:
    def __init__(self, final_path: Path):
        self.final_path = final_path
        self.body_path = final_path.with_suffix(final_path.suffix + ".body")
        self.body_path.parent.mkdir(parents=True, exist_ok=True)
        self.fh = self.body_path.open('w')
        self.nclauses = 0
        self.empty_clause_count = 0

    def add_clause(self, lits: Sequence[int]) -> None:
        lits = [int(x) for x in lits if int(x) != 0]
        if not lits:
            self.empty_clause_count += 1
        self.fh.write(" ".join(str(x) for x in lits) + " 0\n")
        self.nclauses += 1

    def add_clauses(self, clauses: Iterable[Sequence[int]]) -> int:
        n = 0
        for cl in clauses:
            self.add_clause(cl)
            n += 1
        return n

    def close_with_header(self, nv: int) -> None:
        self.fh.close()
        with self.final_path.open('w') as out:
            out.write(f"p cnf {int(nv)} {int(self.nclauses)}\n")
            with self.body_path.open('r') as body:
                shutil.copyfileobj(body, out, length=16 * 1024 * 1024)
        try:
            self.body_path.unlink()
        except FileNotFoundError:
            pass


def add_card(writer: CnfWriter, lits: Sequence[int], relation: str, bound: int, top: int) -> tuple[int, int, int]:
    lits = list(map(int, lits))
    if relation == "atmost":
        if bound < 0:
            writer.add_clause([])
            return top, 1, 0
        if len(lits) <= bound:
            return top, 0, 0
        if bound == 0:
            for lit in lits:
                writer.add_clause([-lit])
            return top, len(lits), 0
        enc = CardEnc.atmost(lits=lits, bound=int(bound), top_id=int(top), encoding=EncType.seqcounter)
    elif relation == "atleast":
        if bound <= 0:
            return top, 0, 0
        if len(lits) < bound:
            writer.add_clause([])
            return top, 1, 0
        if len(lits) == bound:
            for lit in lits:
                writer.add_clause([lit])
            return top, len(lits), 0
        enc = CardEnc.atleast(lits=lits, bound=int(bound), top_id=int(top), encoding=EncType.seqcounter)
    elif relation == "equals":
        if bound < 0 or bound > len(lits):
            writer.add_clause([])
            return top, 1, 0
        enc = CardEnc.equals(lits=lits, bound=int(bound), top_id=int(top), encoding=EncType.seqcounter)
    else:
        raise ValueError(relation)
    ncl = writer.add_clauses(enc.clauses)
    new_top = max(int(top), int(enc.nv))
    return new_top, ncl, max(0, new_top - int(top))


def parse_solver_log(path: Path) -> dict:
    if not path.exists():
        return {}
    txt = path.read_text(errors='replace')
    return {
        'contains_unsat': 'UNSATISFIABLE' in txt,
        'contains_sat': 'SATISFIABLE' in txt and 'UNSATISFIABLE' not in txt,
        'contains_verified': 'VERIFIED' in txt,
        'tail': txt[-4000:],
    }


def run_solver(cnf: Path, timeout: int) -> dict:
    drat = cnf.with_suffix('.drat')
    cadlog = cnf.with_suffix('.cadical.log')
    trimlog = cnf.with_suffix('.drat_trim.log')
    status_path = cnf.with_suffix('.status.json')
    cmd = ['cadical', '--unsat', '--binary=false', '-n']
    if timeout and timeout > 0:
        cmd += ['-t', str(int(timeout))]
    cmd += [str(cnf), str(drat)]
    t0 = time.time()
    with cadlog.open('w') as f:
        proc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, text=True)
    res = {
        'cnf': str(cnf),
        'drat': str(drat),
        'cadical_log': str(cadlog),
        'drat_trim_log': str(trimlog),
        'cadical_exit': proc.returncode,
        'cadical_elapsed_sec': round(time.time() - t0, 3),
    }
    if proc.returncode == 20:
        t1 = time.time()
        with trimlog.open('w') as f:
            trim = subprocess.run(['drat-trim', str(cnf), str(drat)], stdout=f, stderr=subprocess.STDOUT, text=True)
        res['drat_trim_exit'] = trim.returncode
        res['drat_trim_elapsed_sec'] = round(time.time() - t1, 3)
    else:
        res['drat_trim_exit'] = None
        res['drat_trim_elapsed_sec'] = None
    for p in [cnf, cnf.with_suffix('.meta.json'), drat, cadlog, trimlog]:
        if p.exists():
            res.setdefault('hashes', {})[str(p)] = sha256(p)
    res['cadical_log_parse'] = parse_solver_log(cadlog)
    res['drat_trim_log_parse'] = parse_solver_log(trimlog)
    status_path.write_text(json.dumps(res, indent=2, sort_keys=True) + '\n')
    return res


def build_cnf(base_support: List[int], d: int, cnf: Path, direct_limit: int = 0) -> dict:
    t0 = time.time()
    s = 19
    core = CoreQuotient(1)
    lut, lut_meta = load_lut(ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl")
    records_raw, meta = build_core_constraints(core, lut)
    records = augment_records_with_bitsets(records_raw)
    profile = slack_profile(records, base_support, s=s, max_d=max(4, d))
    rows, row_summary = filtered_rows(records, base_support, d=d, s=s)
    writer = CnfWriter(cnf)
    top = 255
    point_vars = {p: p for p in range(1, 256)}

    # Exactly 19 selected directions.
    top, ncl_exact, naux_exact = add_card(writer, list(point_vars.values()), 'equals', s, top)
    # Exchange radius: keep at least 19-d of the base points.
    top, ncl_neigh, naux_neigh = add_card(writer, [point_vars[p] for p in base_support], 'atleast', s - d, top)

    row_clause_count = 0
    row_aux_count = 0
    empty_before_rows = writer.empty_clause_count
    row_size_hist = Counter()
    cap_hist = Counter()
    relation_hist = Counter()
    for rec in rows:
        lits = [point_vars[p] for p in rec['points']]
        cap = int(rec['cap'])
        row_size_hist[len(lits)] += 1
        cap_hist[cap] += 1
        old_top = top
        top, ncl, naux = add_card(writer, lits, 'atmost', cap, top)
        row_clause_count += ncl
        row_aux_count += naux
        relation_hist['wang_atmost_rows_encoded'] += 1
        if top < old_top:
            raise RuntimeError('top variable id decreased')

    writer.close_with_header(top)
    meta_payload = {
        'schema': 'local_repair_cnf_meta_v1',
        'field': 'F2',
        'core': 'E11 quotient core',
        'rank_s': s,
        'd': d,
        'base_support': base_support,
        'base_support_bitset_sha256': hashlib.sha256(str(points_bitset(base_support)).encode()).hexdigest(),
        'meaning': 'CNF encodes exact complete-Wang exchange-neighborhood A-support repair. UNSAT+DRAT proves no complete-Wang support within this local radius only.',
        'complete_core_table_meta': meta,
        'base_slack_profile_summary': {
            'violation_count': profile['violation_count'],
            'violations_by_L': profile['violations_by_L'],
            'violations_by_dim8': profile['violations_by_dim8'],
            'rows_with_slack_lt_d': profile['rows_with_slack_lt_d'],
            'slack_histogram': profile['slack_histogram'],
        },
        'selected_neighborhood_row_summary': row_summary,
        'encoding': {
            'primary_point_variables': 255,
            'final_num_vars': top,
            'num_clauses': writer.nclauses,
            'empty_clause_count': writer.empty_clause_count,
            'empty_clause_count_from_rows': writer.empty_clause_count - empty_before_rows,
            'exact19_clauses': ncl_exact,
            'exact19_aux_vars': naux_exact,
            'neighborhood_clauses': ncl_neigh,
            'neighborhood_aux_vars': naux_neigh,
            'wang_row_clauses': row_clause_count,
            'wang_row_aux_vars': row_aux_count,
            'row_size_hist': {str(k): int(v) for k, v in sorted(row_size_hist.items())},
            'cap_hist': {str(k): int(v) for k, v in sorted(cap_hist.items())},
            'relation_hist': {str(k): int(v) for k, v in sorted(relation_hist.items())},
            'cardinality_encoding': 'pysat CardEnc seqcounter with fresh monotonically increasing top_id; cap=0 rows emitted as units',
        },
        'cnf_path': str(cnf),
        'cnf_sha256': sha256(cnf),
        'build_elapsed_sec': round(time.time() - t0, 3),
    }
    meta_path = cnf.with_suffix('.meta.json')
    meta_path.write_text(json.dumps(meta_payload, indent=2, sort_keys=True) + '\n')
    return meta_payload


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--support', type=str, default=None)
    ap.add_argument('--d', type=int, required=True)
    ap.add_argument('--cnf', type=Path, default=None)
    ap.add_argument('--solve', action='store_true')
    ap.add_argument('--solver-time', type=int, default=300)
    args = ap.parse_args()
    base = parse_support_arg(args.support)
    cnf = args.cnf or (OUTDIR / f'current_support_repair_d{args.d}.cnf')
    cnf.parent.mkdir(parents=True, exist_ok=True)
    meta = build_cnf(base, int(args.d), cnf)
    res = None
    if args.solve:
        res = run_solver(cnf, int(args.solver_time))
    print(json.dumps({
        'cnf': str(cnf),
        'd': args.d,
        'num_vars': meta['encoding']['final_num_vars'],
        'num_clauses': meta['encoding']['num_clauses'],
        'row_count': meta['selected_neighborhood_row_summary']['row_count'],
        'cnf_sha256': meta['cnf_sha256'],
        'solver': None if res is None else {
            'cadical_exit': res['cadical_exit'],
            'drat_trim_exit': res.get('drat_trim_exit'),
            'cadical_elapsed_sec': res['cadical_elapsed_sec'],
            'drat_trim_elapsed_sec': res.get('drat_trim_elapsed_sec'),
            'contains_verified': res.get('drat_trim_log_parse', {}).get('contains_verified'),
        },
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
