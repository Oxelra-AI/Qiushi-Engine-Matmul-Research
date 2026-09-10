#!/usr/bin/env python3
r"""Verify provenance and DRAT status for graph independent-set CNF artifacts."""
import argparse
import json
import pathlib
import pickle
import sys
from typing import Dict, Sequence

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))
from wang_capacity_lazy import unpack_basis  # noqa:E402
from verify_graph_certificate import rank1_points, make_pivot_dict, in_span_piv, row_residual  # noqa:E402


def load_lut(path: pathlib.Path) -> Dict[int, int]:
    with path.open('rb') as f:
        data = pickle.load(f)
    lut = data['lut'] if isinstance(data, dict) and 'lut' in data else data
    return {int(k): int(v) for k, v in lut.items()}


def parse_header(cnf: pathlib.Path):
    with cnf.open() as f:
        for line in f:
            if line.startswith('p cnf'):
                _, _, nv, nc = line.split()[:4]
                return int(nv), int(nc)
    raise AssertionError('CNF header missing')


def parse_log(path: pathlib.Path):
    text = path.read_text(errors='ignore') if path.exists() else ''
    return {
        'unsat': ('UNSATISFIABLE' in text or '\ns UNSAT' in text),
        'verified': ('VERIFIED' in text or 's VERIFIED' in text),
        'tail': text[-1000:],
    }


def verify_one(meta_path: pathlib.Path, status_path: pathlib.Path, lut: Dict[int, int]):
    meta = json.loads(meta_path.read_text())
    status = json.loads(status_path.read_text())
    matching = [int(x) for x in meta['matching']]
    target = int(meta['target'])
    r1 = rank1_points()
    hr = sorted(m for m in range(1, 512) if m not in r1)
    hr_set = set(hr)

    forbidden = set()
    for h, key in meta.get('vertex_exclusions', []):
        h = int(h); key = int(key)
        assert h in hr_set
        rr = row_residual(lut, key, matching)
        assert rr['residual'] == 0, f'vertex row residual {rr["residual"]}'
        assert in_span_piv(rr['piv'], h)
        forbidden.add(h)
    survivors_expected = [h for h in hr if h not in forbidden]
    survivors = [int(x) for x in meta['survivors']]
    assert survivors == survivors_expected, 'survivors not implied by vertex_exclusions'
    assert len(survivors) == int(meta['survivor_count'])
    var = {int(k): int(v) for k, v in meta['var_of_point'].items()}
    assert set(var) == set(survivors)

    for a, b, key in meta['edge_rows']:
        a = int(a); b = int(b); key = int(key)
        assert a in var and b in var and a != b
        rr = row_residual(lut, key, matching)
        assert rr['residual'] == 1, f'edge row residual {rr["residual"]}'
        assert in_span_piv(rr['piv'], a) and in_span_piv(rr['piv'], b)

    cnf = pathlib.Path(status['cnf'])
    nv, nc = parse_header(cnf)
    assert nv == int(meta['cnf_vars'])
    assert nc == int(meta['cnf_clauses'])
    cad = parse_log(pathlib.Path(status['cadical_log']))
    trim = parse_log(pathlib.Path(status['drat_trim_log']))
    assert cad['unsat'], 'CaDiCaL log does not report UNSAT'
    assert trim['verified'], 'drat-trim log does not report VERIFIED'
    assert int(status.get('drat_trim_exit', -1)) == 0

    return {
        'status': 'verified',
        'idx': meta['idx'],
        'target': target,
        'survivors': len(survivors),
        'vertex_exclusions': len(forbidden),
        'edge_rows': len(meta['edge_rows']),
        'cnf_vars': nv,
        'cnf_clauses': nc,
        'drat_trim_exit': status.get('drat_trim_exit'),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--pairs', nargs='+', required=True, help='meta.json,status.json pairs separated by comma')
    ap.add_argument('--out')
    args = ap.parse_args()
    lut = load_lut(pathlib.Path(args.lut))
    results = []
    for pair in args.pairs:
        a, b = pair.split(',', 1)
        res = verify_one(pathlib.Path(a), pathlib.Path(b), lut)
        print(json.dumps(res, sort_keys=True))
        results.append(res)
    payload = {'checked': len(results), 'results': results}
    if args.out:
        pathlib.Path(args.out).parent.mkdir(parents=True, exist_ok=True)
        pathlib.Path(args.out).write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')


if __name__ == '__main__':
    main()
