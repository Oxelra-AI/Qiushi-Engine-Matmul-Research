#!/usr/bin/env python3
r"""Verify direct Wang-row graph certificates for fixed matching strata.

This checker does not trust solver search labels.  It reads a certificate JSON
from graph_coloring_certificate.py and verifies directly from the Wang LUT:

* matching_violates: the cited row has L and contains more fixed matching points
  than capacity 20-L.
* vertex_count: every cited forbidden vertex lies in its residual-zero Wang row,
  and the remaining vertices are fewer than target.
* clique_cover: the color classes are a partition of the surviving higher-rank
  vertices into at most target-1 cliques of the incompatibility graph; for each
  same-color pair, the cited Wang row has residual one and contains both points.

This is a checker for one support-side fixed matching stratum over F2, not a
checker for the whole tensor-rank problem.
"""
import argparse
import json
import pathlib
import pickle
import sys
from typing import Dict, List, Sequence

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))
from wang_capacity_lazy import unpack_basis, matrix_rank_of_mask  # noqa:E402


def load_lut(path: pathlib.Path) -> Dict[int, int]:
    with path.open('rb') as f:
        data = pickle.load(f)
    lut = data['lut'] if isinstance(data, dict) and 'lut' in data else data
    return {int(k): int(v) for k, v in lut.items()}


def rank1_points() -> set:
    pts = set()
    for u in range(1, 8):
        for v in range(1, 8):
            m = 0
            for i in range(3):
                if (u >> i) & 1:
                    m |= v << (3 * i)
            pts.add(m)
    return pts


def make_pivot_dict(basis: Sequence[int]):
    return {int(b).bit_length() - 1: int(b) for b in basis if int(b)}


def in_span_piv(piv, v: int) -> bool:
    x = int(v)
    while x:
        p = x.bit_length() - 1
        b = piv.get(p)
        if b is None:
            return False
        x ^= b
    return True


def row_residual(lut: Dict[int, int], key: int, matching: Sequence[int]):
    key = int(key)
    if key not in lut:
        raise AssertionError(f'row key {key} absent from LUT')
    lb = int(lut[key])
    cap = 20 - lb
    basis = unpack_basis(key)
    piv = make_pivot_dict(basis)
    cnt = sum(1 for m in matching if in_span_piv(piv, int(m)))
    return {'key': key, 'lb': lb, 'cap': cap, 'matching_count': cnt, 'residual': cap - cnt, 'piv': piv}


def all_hr_vertices() -> List[int]:
    r1 = rank1_points()
    return sorted(m for m in range(1, 512) if m not in r1)


def verify(cert_path: pathlib.Path, lut_path: pathlib.Path) -> dict:
    cert = json.loads(cert_path.read_text())
    lut = load_lut(lut_path)
    ctype = cert['certificate_type']
    matching = [int(x) for x in cert['matching']]
    target = int(cert['target_higher_rank_count'])
    hr = all_hr_vertices()
    hr_set = set(hr)

    if ctype == 'matching_violates':
        vr = cert['violating_row']
        rr = row_residual(lut, int(vr['key']), matching)
        assert rr['lb'] == int(vr['lb'])
        assert rr['cap'] == int(vr['cap'])
        assert rr['matching_count'] == int(vr['matching_count'])
        assert rr['residual'] < 0
        return {'status': 'verified', 'certificate_type': ctype, 'row': {k: rr[k] for k in ['key','lb','cap','matching_count','residual']}}

    vertex_exclusions = [[int(h), int(key)] for h, key in cert.get('vertex_exclusions', [])]
    forbidden = set()
    for h, key in vertex_exclusions:
        assert h in hr_set, f'forbidden non-HR vertex {h}'
        rr = row_residual(lut, key, matching)
        assert rr['residual'] == 0, f'vertex row {key} residual {rr["residual"]}'
        assert in_span_piv(rr['piv'], h), f'vertex {h} not in row {key}'
        forbidden.add(h)
    survivors_expected = [h for h in hr if h not in forbidden]
    survivors = [int(x) for x in cert.get('survivors', [])]
    assert survivors == survivors_expected, 'survivor list differs from verified vertex exclusions'

    if ctype == 'vertex_count':
        assert len(survivors) < target
        return {'status': 'verified', 'certificate_type': ctype, 'target': target, 'surviving': len(survivors), 'vertex_excluded': len(forbidden)}

    if ctype == 'clique_cover':
        classes = [[int(x) for x in cls] for cls in cert['color_classes']]
        flat = [x for cls in classes for x in cls]
        assert sorted(flat) == survivors, 'color classes are not a partition of survivors'
        assert len(classes) <= target - 1, 'too many color classes to prove alpha < target'
        pair_map = {(int(a), int(b)): int(key) for a, b, key in cert['intra_color_edge_rows']}
        checked_pairs = 0
        for cls in classes:
            assert all(x in hr_set for x in cls)
            for i, a in enumerate(cls):
                for b in cls[i+1:]:
                    x, y = (a, b) if a < b else (b, a)
                    assert (x, y) in pair_map, f'missing pair row for {x},{y}'
                    rr = row_residual(lut, pair_map[(x, y)], matching)
                    assert rr['residual'] == 1, f'edge row residual not 1 for {x},{y}'
                    assert in_span_piv(rr['piv'], x) and in_span_piv(rr['piv'], y), f'edge endpoints not both in row for {x},{y}'
                    checked_pairs += 1
        return {'status': 'verified', 'certificate_type': ctype, 'target': target, 'surviving': len(survivors), 'color_count': len(classes), 'checked_intra_color_pairs': checked_pairs}

    if ctype == 'unresolved':
        return {'status': 'not_a_certificate', 'certificate_type': ctype}
    raise AssertionError(f'unknown certificate_type {ctype}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('certificates', nargs='+')
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--out')
    args = ap.parse_args()
    results = []
    for c in args.certificates:
        r = verify(pathlib.Path(c), pathlib.Path(args.lut))
        r['certificate_path'] = c
        print(json.dumps(r, sort_keys=True))
        results.append(r)
    payload = {'checked': len(results), 'results': results}
    if args.out:
        pathlib.Path(args.out).parent.mkdir(parents=True, exist_ok=True)
        pathlib.Path(args.out).write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')


if __name__ == '__main__':
    main()
