#!/usr/bin/env python3
r"""Decode SAT models from graph independent-set CNFs and scan full Wang LUT."""
import argparse
import json
import pathlib
import pickle
import re
import sys
from typing import Dict, List, Sequence

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))
from wang_capacity_lazy import unpack_basis  # noqa:E402
from verify_graph_certificate import make_pivot_dict, in_span_piv  # noqa:E402


def load_lut(path: pathlib.Path) -> Dict[int, int]:
    with path.open('rb') as f:
        data = pickle.load(f)
    lut = data['lut'] if isinstance(data, dict) and 'lut' in data else data
    return {int(k): int(v) for k, v in lut.items()}


def parse_model(log_path: pathlib.Path, var_of_point: Dict[int, int]) -> List[int]:
    inv = {v: p for p, v in var_of_point.items()}
    selected = set()
    text = log_path.read_text(errors='ignore')
    for line in text.splitlines():
        if line.startswith('v '):
            for tok in line.split()[1:]:
                try:
                    lit = int(tok)
                except ValueError:
                    continue
                if lit > 0 and lit in inv:
                    selected.add(inv[lit])
    return sorted(selected)


def scan_support(lut: Dict[int, int], support: Sequence[int], top: int = 20):
    viol = []
    for key, lb in lut.items():
        cap = 20 - int(lb)
        if cap >= len(support):
            continue
        basis = unpack_basis(int(key))
        piv = make_pivot_dict(basis)
        cnt = sum(1 for p in support if in_span_piv(piv, int(p)))
        if cnt > cap:
            viol.append({'key': int(key), 'lb': int(lb), 'cap': int(cap), 'count': int(cnt), 'excess': int(cnt - cap)})
    viol.sort(key=lambda r: (-r['excess'], -r['count'], -r['lb'], r['key']))
    return viol[:top], len(viol), max([v['excess'] for v in viol], default=0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--items', nargs='+', required=True, help='meta.json,status.json[,model.log] items separated by comma')
    ap.add_argument('--out', required=True)
    args = ap.parse_args()
    lut = load_lut(pathlib.Path(args.lut))
    records = []
    for item in args.items:
        parts = item.split(',')
        if len(parts) == 2:
            meta_path, status_path = parts
            model_log = None
        elif len(parts) == 3:
            meta_path, status_path, model_log = parts
        else:
            raise ValueError(f'bad item spec {item!r}')
        meta = json.loads(pathlib.Path(meta_path).read_text())
        status = json.loads(pathlib.Path(status_path).read_text())
        var_of_point = {int(k): int(v) for k, v in meta['var_of_point'].items()}
        selected = parse_model(pathlib.Path(model_log or status['cadical_log']), var_of_point)
        support = sorted([int(x) for x in meta['matching']] + selected)
        vh, vc, me = scan_support(lut, support, top=10)
        rec = {
            'idx': int(meta['idx']),
            'matching': [int(x) for x in meta['matching']],
            'target': int(meta['target']),
            'selected_hr_count': len(selected),
            'selected_hr': selected,
            'support_size': len(support),
            'full_lut_violation_count': vc,
            'max_excess': me,
            'violations_head': vh,
            'meta': meta_path,
            'status': status_path,
            'model_log': model_log or status['cadical_log'],
        }
        print(json.dumps({k: rec[k] for k in ['idx','selected_hr_count','support_size','full_lut_violation_count','max_excess']}, sort_keys=True))
        records.append(rec)
    payload = {'records': records, 'meaning': 'SAT graph independent sets show residual-0/1 rows do not close these strata; violations_head gives higher-residual Wang rows needed next.'}
    pathlib.Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    pathlib.Path(args.out).write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')


if __name__ == '__main__':
    main()
