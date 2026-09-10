#!/usr/bin/env python3
"""analysis: estimate SAT expansion size for E11-core Wang systems.

The full E11 core ILP has only 255 multiplicity variables, but a SAT/PB proof
requires expanding hundreds of thousands of overlapping occupancy constraints.
This script quantifies that expansion without writing the full CNF.
It aggregates Wang rows by encoded token length and bound, then evaluates PySAT
cardinality encodings once per class.
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter, defaultdict
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from pysat.card import CardEnc, EncType as CardEncType
from pysat.pb import PBEnc, EncType as PBEncType

from core_capacity_from_wang_lut import CoreQuotient
from complete_core_and_transversal import ROOT, build_core_constraints
from quotient_rank_cuts import build_contractions, point_mask_for_q
from core_repeat_symmetry_and_cnf import extract_compact_constraints
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis
import numpy as np

OUTDIR = ROOT / 'workspace/data/repeat_branch_certificate'


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}


def card_stats(n: int, bound: int, encoding_name: str):
    if bound < 0:
        return {'clauses': 1, 'aux': 0, 'kind': 'empty'}
    if bound >= n:
        return {'clauses': 0, 'aux': 0, 'kind': 'taut'}
    if bound == 0:
        return {'clauses': n, 'aux': 0, 'kind': 'units'}
    if bound == n:
        return {'clauses': n, 'aux': 0, 'kind': 'allunits'}
    enc_map = {
        'seqcounter': CardEncType.seqcounter,
        'totalizer': CardEncType.totalizer,
        'cardnetwrk': CardEncType.cardnetwrk,
        'sortnetwrk': CardEncType.sortnetwrk,
    }
    lits = list(range(1, n + 1))
    enc = CardEnc.atmost(lits=lits, bound=bound, top_id=n, encoding=enc_map[encoding_name])
    return {'clauses': len(enc.clauses), 'aux': max(0, enc.nv - n), 'kind': 'encoded'}


def pb_atleast_stats(weights, bound: int, encoding_name: str):
    n = len(weights)
    maxw = sum(weights)
    if bound <= 0:
        return {'clauses': 0, 'aux': 0, 'kind': 'taut'}
    if bound > maxw:
        return {'clauses': 1, 'aux': 0, 'kind': 'empty'}
    if all(w == 1 for w in weights):
        # at least b == at most n-b on negated lits; same clause count in CardEnc.atleast
        enc = CardEnc.atleast(lits=list(range(1, n + 1)), bound=bound, top_id=n, encoding=CardEncType.seqcounter)
        return {'clauses': len(enc.clauses), 'aux': max(0, enc.nv - n), 'kind': 'card'}
    enc_map = {
        'best': PBEncType.best,
        'bdd': PBEncType.bdd,
        'seqcounter': PBEncType.seqcounter,
        'sortnetwrk': PBEncType.sortnetwrk,
        'adder': PBEncType.adder,
        'binmerge': PBEncType.binmerge,
    }
    enc = PBEnc.atleast(lits=list(range(1, n + 1)), weights=weights, bound=bound, top_id=n, encoding=enc_map[encoding_name])
    return {'clauses': len(enc.clauses), 'aux': max(0, enc.nv - n), 'kind': 'pb'}


def wang_aggregate(records, keys, point_cap, fixed_counts, s):
    token_len_by_point = {p: max(0, point_cap[p] - fixed_counts.get(p, 0)) for p in range(1, 256)}
    cls = Counter()
    dim_cls = Counter()
    skipped = Counter()
    for key8 in keys:
        rec = records[key8]
        pts = subspace_points_from_basis(unpack_basis(key8))
        fixed = sum(fixed_counts.get(p, 0) for p in pts)
        n = sum(token_len_by_point[p] for p in pts)
        cap = s - int(rec['L']) - fixed
        if cap >= n:
            skipped['tautological'] += 1
        elif cap < 0:
            skipped['impossible'] += 1
        cls[(n, cap)] += 1
        dim_cls[(int(rec['dim8']), n, cap)] += 1
    return cls, dim_cls, skipped


def estimate_card_classes(cls, encoding):
    total_clauses = 0
    total_aux_if_not_reused = 0
    rows = []
    for (n, b), count in sorted(cls.items()):
        st = card_stats(n, b, encoding)
        total_clauses += count * st['clauses']
        total_aux_if_not_reused += count * st['aux']
        rows.append({'n_lits': n, 'bound': b, 'count': count, 'clauses_each': st['clauses'], 'aux_each': st['aux'], 'kind': st['kind']})
    return total_clauses, total_aux_if_not_reused, rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--encoding', choices=['seqcounter', 'totalizer', 'cardnetwrk', 'sortnetwrk'], default='seqcounter')
    ap.add_argument('--pb-encoding', choices=['best', 'bdd', 'seqcounter', 'sortnetwrk', 'adder', 'binmerge'], default='best')
    ap.add_argument('--source', type=Path, default=ROOT / 'workspace/data/quotient_rank_cuts/core_e11_multiset_quotient_sep_24r_fullstored.json')
    ap.add_argument('--out', type=Path, default=OUTDIR / 'cnf_expansion_assessment.json')
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

    t0 = time.time()
    s = 19
    core = CoreQuotient(1)
    lut = load_lut(ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    rec_list, meta = build_core_constraints(core, lut)
    records = {int(r['key8']): r for r in rec_list}
    points = list(range(1, 256))
    point_cap = {}
    for p in points:
        key8 = core.key8_from_rows([p])
        key9 = core.key9_from_key8(key8)
        point_cap[p] = max(0, min(s, s - int(lut[key9])))
    cap2 = sorted(p for p, c in point_cap.items() if c >= 2)

    compact_wang, qcuts = extract_compact_constraints(args.source, rec_list, core, lut)
    # Full table: use every row except the full ambient dim-8 row, matching analysis full test.
    full_wang = {int(r['key8']) for r in rec_list if int(r['dim8']) <= 7}

    scenarios = []
    for name, keys, fixed_counts in [
        ('compact_fixed_repeat_p1', compact_wang, {1: 2}),
        ('full_fixed_repeat_p1', full_wang, {1: 2}),
        ('full_no_fixed_repeat_token_model', full_wang, {}),
        ('compact_no_fixed_repeat_token_model', compact_wang, {}),
    ]:
        cls, dim_cls, skipped = wang_aggregate(records, keys, point_cap, fixed_counts, s)
        clauses, aux, class_rows = estimate_card_classes(cls, args.encoding)
        total_token_vars = sum(max(0, point_cap[p] - fixed_counts.get(p, 0)) for p in points)
        scenarios.append({
            'name': name,
            'fixed_counts': {str(k): int(v) for k, v in fixed_counts.items()},
            'wang_rows': len(keys),
            'distinct_length_bound_classes': len(cls),
            'token_variables_before_aux': total_token_vars,
            'estimated_wang_clauses': int(clauses),
            'estimated_wang_aux_variables_if_expanded_independently': int(aux),
            'skipped_counts': dict(skipped),
            'largest_classes': sorted(class_rows, key=lambda z: z['count'], reverse=True)[:20],
            'largest_clause_contributors': sorted(class_rows, key=lambda z: z['count'] * z['clauses_each'], reverse=True)[:20],
        })

    # Estimate compact qcuts under fixed p=1 just as context, using the real PB encoder per unique signature.
    T = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2
    contractions = build_contractions(T)
    masks = {q: point_mask_for_q(q) for q in contractions}
    fixed_counts = {1: 2}
    token_len_by_point = {p: max(0, point_cap[p] - fixed_counts.get(p, 0)) for p in points}
    pb_cls = Counter()
    for c in qcuts:
        q1, q2 = int(c['sources'][0]), int(c['sources'][1])
        target = int(c['target'])
        req = int(c['requirement'])
        rhs = req + int(contractions[q1]['rank']) + int(contractions[q2]['rank'])
        source_union = masks[q1] | masks[q2]
        outside_mask = masks[target] & (~source_union) & ((1 << 255) - 1)
        weights = []
        fixed_coeff = 0
        for p in points:
            coeff = 0
            if (outside_mask >> (p - 1)) & 1:
                coeff += 1
            if ((q1 & p).bit_count() & 1):
                coeff += 1
            if ((q2 & p).bit_count() & 1):
                coeff += 1
            if coeff:
                fixed_coeff += coeff * fixed_counts.get(p, 0)
                for _ in range(token_len_by_point[p]):
                    weights.append(coeff)
        pb_cls[(tuple(sorted(Counter(weights).items())), rhs - fixed_coeff)] += 1
    pb_clause_total = 0
    pb_aux_total = 0
    pb_rows = []
    for (hist_tuple, bound), count in pb_cls.items():
        weights = []
        for w, c in hist_tuple:
            weights.extend([int(w)] * int(c))
        st = pb_atleast_stats(weights, int(bound), args.pb_encoding)
        pb_clause_total += count * st['clauses']
        pb_aux_total += count * st['aux']
        pb_rows.append({'weight_hist': dict(hist_tuple), 'bound': int(bound), 'count': count, 'clauses_each': st['clauses'], 'aux_each': st['aux'], 'kind': st['kind']})

    out = {
        'schema': 'core_cnf_expansion_assessment_v1',
        'field': 'F2',
        'core': 'E11',
        'rank_s': s,
        'cardinality_encoding': args.encoding,
        'pb_encoding': args.pb_encoding,
        'point_cap_distribution': {str(k): int(v) for k, v in sorted(Counter(point_cap.values()).items())},
        'capacity_two_points': cap2,
        'complete_core_table_meta': meta,
        'scenarios': scenarios,
        'compact_fixed_repeat_qcut_pb_estimate': {
            'unique_qcuts': len(qcuts),
            'distinct_pb_classes': len(pb_cls),
            'estimated_qcut_clauses': int(pb_clause_total),
            'estimated_qcut_aux_variables_if_expanded_independently': int(pb_aux_total),
            'largest_clause_contributors': sorted(pb_rows, key=lambda z: z['count'] * z['clauses_each'], reverse=True)[:20],
        },
        'interpretation': (
            'Full-table proof-producing SAT is not small merely because the ILP has 255 integer variables: '
            'cardinality expansion scales over hundreds of thousands of overlapping rows. The compact learned-row fixed-repeat CNF is the present proof target; full-table encoding should be attempted only with this expansion cost in view or with a stronger proof system/row-selection strategy.'
        ),
        'elapsed_sec': round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'out': str(args.out),
        'encoding': args.encoding,
        'scenarios': [(s['name'], s['wang_rows'], s['estimated_wang_clauses'], s['estimated_wang_aux_variables_if_expanded_independently']) for s in scenarios],
        'compact_qcut_clauses': pb_clause_total,
        'elapsed_sec': out['elapsed_sec'],
    }, sort_keys=True))


if __name__ == '__main__':
    main()
