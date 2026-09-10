#!/usr/bin/env python3
r"""Encode graph independent-set exclusion for fixed-matching Wang certificates.

Given a fixed matching stratum, residual-0 Wang rows remove vertices and residual-1
rows create incompatibility edges among the surviving higher-rank points.  This
script writes a small CNF for existence of an independent set of size at least
20-|M| in that incompatibility graph:

  * one variable per surviving higher-rank point;
  * for each incompatibility edge {u,v}, clause (not u or not v);
  * one cardinality constraint sum variables >= target.

UNSAT, together with a DRAT replay and separately checked Wang-row provenance for
the edge clauses, is a certifying graph upper-bound component.  SAT gives a graph
survivor showing that residual-0/1 consequences alone do not exclude the stratum.
"""
import argparse
import hashlib
import json
import pathlib
import pickle
import subprocess
import sys
import time
from typing import List

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))
from graph_coloring_certificate import (  # noqa:E402
    rank1_points, load_lut, iter_strata, process_stratum,
)


class DimacsWriter:
    def __init__(self, path: pathlib.Path):
        self.path = path
        self.clauses: List[List[int]] = []
        self.nv = 0
    def add_clause(self, cl):
        cl = [int(x) for x in cl]
        for x in cl:
            self.nv = max(self.nv, abs(x))
        self.clauses.append(cl)
    def write(self, nv=None):
        if nv is None:
            nv = self.nv
        self.path.parent.mkdir(parents=True, exist_ok=True)
        with self.path.open('w') as f:
            f.write(f'p cnf {nv} {len(self.clauses)}\n')
            for cl in self.clauses:
                f.write(' '.join(map(str, cl)) + ' 0\n')


def sha256(path: pathlib.Path):
    if not path.exists():
        return None
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def parse_log(path: pathlib.Path):
    text = path.read_text(errors='ignore') if path.exists() else ''
    return {
        'unsat': ('UNSATISFIABLE' in text or '\ns UNSAT' in text),
        'sat': ('SATISFIABLE' in text and 'UNSATISFIABLE' not in text),
        'verified': ('VERIFIED' in text or 's VERIFIED' in text),
        'tail': text[-2000:],
    }


def add_atleast(writer: DimacsWriter, lits: List[int], bound: int, top_id: int):
    from pysat.card import CardEnc, EncType
    if bound <= 0:
        return top_id, 0
    if bound > len(lits):
        writer.add_clause([])
        return top_id, 1
    enc = CardEnc.atleast(lits=lits, bound=bound, top_id=top_id, encoding=EncType.seqcounter)
    for cl in enc.clauses:
        writer.add_clause(cl)
    return enc.nv, len(enc.clauses)


def write_graph_cnf(info: dict, st: dict, idx: int, cnf_path: pathlib.Path, meta_path: pathlib.Path):
    survivors = [int(x) for x in info['survivors']]
    target = int(info['target'])
    var = {h: i + 1 for i, h in enumerate(survivors)}
    writer = DimacsWriter(cnf_path)
    edge_records = []
    for (a, b), key in sorted(info['edge_key'].items()):
        if a in var and b in var:
            writer.add_clause([-var[a], -var[b]])
            edge_records.append([int(a), int(b), int(key)])
    top, card_clauses = add_atleast(writer, list(var.values()), target, len(var))
    writer.write(nv=top)
    meta = {
        'schema': 'graph_is_cnf_v1',
        'idx': int(idx),
        'k': int(st['k']),
        'matching': [int(x) for x in st['canonical']],
        'target': target,
        'survivor_count': len(survivors),
        'vertex_exclusions': [[int(h), int(key)] for h, key in sorted(info['vertex_key'].items())],
        'survivors': survivors,
        'edge_clause_count': len(edge_records),
        'edge_rows': edge_records,
        'atleast_cardinality_clauses': card_clauses,
        'var_of_point': {str(h): var[h] for h in survivors},
        'cnf_vars': top,
        'cnf_clauses': len(writer.clauses),
        'meaning': 'UNSAT proves no independent set of size target in the residual-0/1 incompatibility graph, provided edge_rows are checked against Wang residual capacities.',
    }
    meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True) + '\n')
    return meta


def run_solver(cnf_path: pathlib.Path, timeout: int):
    drat = cnf_path.with_suffix('.drat')
    cad_log = cnf_path.with_suffix('.cadical.log')
    trim_log = cnf_path.with_suffix('.drat_trim.log')
    cmd = ['cadical', '--unsat', '--binary=false', '-n']
    if timeout > 0:
        cmd += ['-t', str(timeout)]
    cmd += [str(cnf_path), str(drat)]
    t0 = time.time()
    with cad_log.open('w') as f:
        proc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, text=True)
    status = {
        'cnf': str(cnf_path), 'drat': str(drat), 'cadical_log': str(cad_log),
        'drat_trim_log': str(trim_log), 'cadical_exit': proc.returncode,
        'cadical_elapsed_sec': time.time() - t0,
    }
    if proc.returncode == 20:
        t1 = time.time()
        with trim_log.open('w') as f:
            trim = subprocess.run(['drat-trim', str(cnf_path), str(drat)], stdout=f, stderr=subprocess.STDOUT, text=True)
        status['drat_trim_exit'] = trim.returncode
        status['drat_trim_elapsed_sec'] = time.time() - t1
    else:
        status['drat_trim_exit'] = None
        status['drat_trim_elapsed_sec'] = None
    status['cadical_log_parse'] = parse_log(cad_log)
    status['drat_trim_log_parse'] = parse_log(trim_log)
    status['hashes'] = {p.name: sha256(p) for p in [cnf_path, cnf_path.with_suffix('.meta.json'), drat, cad_log, trim_log] if p.exists()}
    status_path = cnf_path.with_suffix('.status.json')
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + '\n')
    return status


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--strata', default='workspace/data/matching_strata/anchored_matching_strata.json')
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--indices', required=True, help='comma-separated global stratum indices')
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--solve-time', type=int, default=300)
    args = ap.parse_args()

    out_dir = pathlib.Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    wanted = {int(x) for x in args.indices.replace(';', ',').split(',') if x.strip()}

    r1 = rank1_points()
    hr_list = sorted(m for m in range(1, 512) if m not in r1)
    hr_set = set(hr_list)

    strata = [(idx, st) for idx, st in iter_strata(pathlib.Path(args.strata), 0) if idx in wanted]
    if sorted(idx for idx, _ in strata) != sorted(wanted):
        raise SystemExit(f'missing requested strata: wanted={sorted(wanted)}, got={sorted(idx for idx,_ in strata)}')

    print(f'Loading LUT {args.lut}')
    lut = load_lut(pathlib.Path(args.lut))
    records = []
    for idx, st in strata:
        matching = [int(x) for x in st['canonical']]
        print(f'idx={idx} k={st["k"]} matching={matching}')
        info = process_stratum(lut, matching, hr_set, hr_list)
        if info['impossible_rows']:
            rec = {'idx': idx, 'status': 'matching_already_violates', 'matching': matching}
            records.append(rec)
            print(json.dumps(rec, sort_keys=True))
            continue
        stem = f'idx{idx:03d}_k{st["k"]}_graph_is'
        cnf = out_dir / f'{stem}.cnf'
        meta = write_graph_cnf(info, st, idx, cnf, out_dir / f'{stem}.meta.json')
        status = run_solver(cnf, args.solve_time)
        rec = {
            'idx': idx, 'matching': matching, 'target': meta['target'],
            'survivor_count': meta['survivor_count'], 'edge_clause_count': meta['edge_clause_count'],
            'cnf_vars': meta['cnf_vars'], 'cnf_clauses': meta['cnf_clauses'],
            'cadical_exit': status['cadical_exit'],
            'cadical_elapsed_sec': status['cadical_elapsed_sec'],
            'drat_trim_exit': status['drat_trim_exit'],
            'drat_trim_elapsed_sec': status['drat_trim_elapsed_sec'],
            'unsat': status['cadical_log_parse']['unsat'],
            'verified': status['drat_trim_log_parse']['verified'],
            'cnf': str(cnf), 'meta': str(out_dir / f'{stem}.meta.json'),
            'status_path': str(cnf.with_suffix('.status.json')),
        }
        records.append(rec)
        print(json.dumps(rec, sort_keys=True))
    summary = {'schema': 'graph_is_cnf_summary_v1', 'records': records}
    (out_dir / 'summary.json').write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(f'Saved {out_dir / "summary.json"}')


if __name__ == '__main__':
    main()
