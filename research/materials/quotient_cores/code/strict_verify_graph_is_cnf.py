#!/usr/bin/env python3
r"""Strictly verify graph-IS CNF artifacts against Wang-row provenance.

This strengthens verify_graph_is_cnf.py by parsing the DIMACS file and
comparing it, clause-for-clause as a multiset, with a freshly regenerated graph
independent-set encoding from the metadata: all residual-1 edge clauses plus one
fresh sequential-counter at-least-target circuit.  It also rechecks every cited
Wang row and the DRAT replay status.
"""
import argparse
import json
import pathlib
import pickle
import sys
from collections import Counter
from typing import Dict

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))
from verify_graph_certificate import rank1_points, in_span_piv, row_residual  # noqa:E402


def load_lut(path: pathlib.Path) -> Dict[int, int]:
    with path.open('rb') as f:
        data = pickle.load(f)
    lut = data['lut'] if isinstance(data, dict) and 'lut' in data else data
    return {int(k): int(v) for k, v in lut.items()}


def normalize_clause(cl):
    return tuple(sorted(int(x) for x in cl))


def parse_cnf(path: pathlib.Path):
    nv = nc = None
    clauses = []
    with path.open() as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('c'):
                continue
            if line.startswith('p '):
                parts = line.split()
                assert parts[1] == 'cnf'
                nv, nc = int(parts[2]), int(parts[3])
                continue
            lits = [int(x) for x in line.split()]
            assert lits and lits[-1] == 0
            clauses.append(normalize_clause(lits[:-1]))
    assert nv is not None and nc is not None
    assert nc == len(clauses), f'header clause count {nc} != parsed {len(clauses)}'
    return nv, Counter(clauses)


def expected_clause_counter(meta):
    from pysat.card import CardEnc, EncType
    var = {int(k): int(v) for k, v in meta['var_of_point'].items()}
    clauses = []
    for a, b, _key in meta['edge_rows']:
        clauses.append(normalize_clause([-var[int(a)], -var[int(b)]]))
    lits = [var[h] for h in sorted(var, key=lambda x: var[x])]
    enc = CardEnc.atleast(lits=lits, bound=int(meta['target']), top_id=len(var), encoding=EncType.seqcounter)
    clauses.extend(normalize_clause(cl) for cl in enc.clauses)
    return enc.nv, Counter(clauses)


def log_has(path: pathlib.Path, token: str):
    return token in path.read_text(errors='ignore') if path.exists() else False


def verify_pair(meta_path: pathlib.Path, status_path: pathlib.Path, lut: Dict[int, int]):
    meta = json.loads(meta_path.read_text())
    status = json.loads(status_path.read_text())
    matching = [int(x) for x in meta['matching']]
    r1 = rank1_points(); hr = sorted(m for m in range(1,512) if m not in r1); hr_set=set(hr)

    forbidden = set()
    for h, key in meta.get('vertex_exclusions', []):
        h=int(h); key=int(key); assert h in hr_set
        rr=row_residual(lut,key,matching); assert rr['residual']==0; assert in_span_piv(rr['piv'],h)
        forbidden.add(h)
    assert [h for h in hr if h not in forbidden] == [int(x) for x in meta['survivors']]
    for a,b,key in meta['edge_rows']:
        a=int(a); b=int(b); key=int(key)
        rr=row_residual(lut,key,matching); assert rr['residual']==1; assert in_span_piv(rr['piv'],a) and in_span_piv(rr['piv'],b)

    cnf_path = pathlib.Path(status['cnf'])
    nv_actual, ctr_actual = parse_cnf(cnf_path)
    nv_expected, ctr_expected = expected_clause_counter(meta)
    assert nv_actual == nv_expected == int(meta['cnf_vars'])
    assert sum(ctr_actual.values()) == sum(ctr_expected.values()) == int(meta['cnf_clauses'])
    assert ctr_actual == ctr_expected, 'DIMACS clauses differ from regenerated encoding'
    assert log_has(pathlib.Path(status['cadical_log']), 'UNSATISFIABLE')
    assert log_has(pathlib.Path(status['drat_trim_log']), 'VERIFIED')
    assert int(status.get('drat_trim_exit')) == 0
    return {
        'status':'strictly_verified', 'idx':int(meta['idx']), 'target':int(meta['target']),
        'survivors':len(meta['survivors']), 'vertex_exclusions':len(forbidden),
        'edge_rows':len(meta['edge_rows']), 'cnf_vars':nv_actual,
        'cnf_clauses':sum(ctr_actual.values()), 'drat_trim_exit':status.get('drat_trim_exit')
    }


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--lut',default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl'); ap.add_argument('--pairs',nargs='+',required=True); ap.add_argument('--out')
    args=ap.parse_args(); lut=load_lut(pathlib.Path(args.lut)); results=[]
    for pair in args.pairs:
        a,b=pair.split(',',1); res=verify_pair(pathlib.Path(a),pathlib.Path(b),lut); print(json.dumps(res,sort_keys=True)); results.append(res)
    if args.out:
        pathlib.Path(args.out).parent.mkdir(parents=True,exist_ok=True); pathlib.Path(args.out).write_text(json.dumps({'checked':len(results),'results':results},indent=2,sort_keys=True)+'\n')

if __name__=='__main__': main()
