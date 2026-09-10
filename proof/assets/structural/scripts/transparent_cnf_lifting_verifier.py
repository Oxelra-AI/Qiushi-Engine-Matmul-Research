#!/usr/bin/env python3
"""Clause-level verifier for research transparent unary-count CNFs.

This script checks the risk that a DRAT proof cannot detect: an accidental
encoding that overconstrains the intended integer occupation system.  For one
transparent CNF, it reconstructs the exact emitted clauses from the source core
and the documented prefix-threshold formulas, compares them with the actual
DIMACS file, verifies auxiliary ranges are disjoint and in the expected order,
and records the forward lifting proof by clause family.

Forward lifting statement checked here:
If x_p are nonnegative integers of total L satisfying every source row
sum_{p in row} x_p <= cap(row), define u[p,ell]=1 iff ell<=x_p.  Define every
prefix-counter auxiliary y[i,j] as the truth value of "among the first i input
literals of that counter, at least j are true".  Then every clause in the actual
DIMACS file is satisfied.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def row_hash(rows: Sequence[Tuple[int, int]]) -> str:
    return hashlib.sha256(';'.join(f'{int(m)}:{int(c)}' for m, c in rows).encode()).hexdigest()


def count_var(p0: int, ell: int, L: int) -> int:
    return p0 * L + ell


class ClauseStream:
    def __init__(self, top: int):
        self.top = int(top)
        self.clauses: List[List[int]] = []
        self.stats: Dict[str, int] = {}
        self.ranges: List[Dict] = []

    def add(self, cl: Sequence[int], tag: str):
        seen = set(); out: List[int] = []
        for lit0 in cl:
            lit = int(lit0)
            if -lit in seen:
                return
            if lit not in seen:
                seen.add(lit); out.append(lit)
        self.clauses.append(out); self.stats[tag] = self.stats.get(tag, 0) + 1

    def alloc_matrix(self, n: int, m: int, name: str, meta: Dict | None = None) -> List[List[int]]:
        start = self.top + 1
        mat = []
        for _ in range(n + 1):
            row = []
            for _ in range(m + 1):
                self.top += 1; row.append(self.top)
            mat.append(row)
        rec = {'name': name, 'start_var': start, 'end_var': self.top, 'n_prefix': n, 'thresholds': m}
        if meta: rec.update(meta)
        self.ranges.append(rec)
        return mat


def add_row_atmost_forward(s: ClauseStream, lits: Sequence[int], cap: int, name: str) -> Dict:
    n = len(lits); before_top = s.top; before_clause = len(s.clauses)
    if cap >= n:
        return {'name': name, 'kind': 'row_atmost_forward', 'cap': cap, 'n_lits': n, 'skipped': True, 'start_var': before_top + 1, 'end_var': before_top, 'clauses_before': before_clause, 'clauses_after': before_clause, 'aux_vars': 0}
    if cap < 0:
        s.add([], 'row_negative_empty')
    elif cap == 0:
        for x in lits:
            s.add([-x], 'row_cap0_units')
    else:
        Kp = cap + 1
        y = s.alloc_matrix(n, Kp, name, {'kind': 'row_atmost_forward', 'cap': cap, 'n_lits': n})
        for i, x in enumerate(lits, start=1):
            s.add([-x, y[i][1]], 'row_x_implies_ge1')
            if i > 1:
                for j in range(1, Kp + 1):
                    s.add([-y[i - 1][j], y[i][j]], 'row_prefix_monotone')
                for j in range(2, Kp + 1):
                    s.add([-x, -y[i - 1][j - 1], y[i][j]], 'row_prefix_increment')
        s.add([-y[n][Kp]], 'row_atmost_terminal')
    end_top = s.top
    return {'name': name, 'kind': 'row_atmost_forward', 'cap': cap, 'n_lits': n, 'skipped': False, 'start_var': before_top + 1, 'end_var': end_top, 'clauses_before': before_clause, 'clauses_after': len(s.clauses), 'aux_vars': end_top - before_top}


def add_total_exact_prefix(s: ClauseStream, lits: Sequence[int], L: int) -> Dict:
    n = len(lits); Kp = L + 1
    before_top = s.top; before_clause = len(s.clauses)
    y = s.alloc_matrix(n, Kp, 'total_exact_prefix', {'kind': 'total_exact_prefix', 'target': L, 'n_lits': n})

    def prev_var(i_minus_1: int, j: int):
        if j == 0:
            return True
        if i_minus_1 == 0:
            return False
        return y[i_minus_1][j]

    def add_or_with_constants(neg_y: int, terms: Sequence[object], tag: str):
        cl = [neg_y]
        for t in terms:
            if t is True:
                return
            if t is False:
                continue
            cl.append(int(t))
        s.add(cl, tag)

    for i, x in enumerate(lits, start=1):
        s.add([-x, y[i][1]], 'total_x_implies_ge1')
        for j in range(1, Kp + 1):
            pv = prev_var(i - 1, j)
            if pv is True:
                s.add([y[i][j]], 'total_prev_true_unit')
            elif pv is not False:
                s.add([-int(pv), y[i][j]], 'total_prefix_monotone')
        for j in range(2, Kp + 1):
            pm = prev_var(i - 1, j - 1)
            if pm is True:
                s.add([-x, y[i][j]], 'total_increment_from_true_boundary')
            elif pm is not False:
                s.add([-x, -int(pm), y[i][j]], 'total_prefix_increment')
        for j in range(1, Kp + 1):
            pv = prev_var(i - 1, j)
            pm = prev_var(i - 1, j - 1)
            add_or_with_constants(-y[i][j], [pv, x], 'total_reverse_prev_or_x')
            add_or_with_constants(-y[i][j], [pv, pm], 'total_reverse_prev_or_prevminus')
    s.add([y[n][L]], 'total_lower_unit')
    s.add([-y[n][L + 1]], 'total_upper_unit')
    return {'name': 'total_exact_prefix', 'kind': 'total_exact_prefix', 'target': L, 'n_lits': n, 'start_var': before_top + 1, 'end_var': s.top, 'clauses_before': before_clause, 'clauses_after': len(s.clauses), 'aux_vars': s.top - before_top}


def load_core(core_json: Path):
    d = json.loads(core_json.read_text())
    L = int(d.get('old_lb', d.get('L', 18)))
    k = int(d.get('quotient_dim', d.get('k', 7)))
    row_key = 'shrunk_rows' if d.get('shrunk_rows') else 'selected_core_rows'
    rows = [(int(r['mask']), int(r['cap'])) for r in d[row_key]]
    return rows, k, L, {'core_path': str(core_json), 'source_index': d.get('index'), 'row_key': row_key, 'row_count': len(rows), 'row_sha256': row_hash(rows)}


def reconstruct(core_json: Path):
    rows, k, L, src = load_core(core_json)
    npts = (1 << k) - 1
    s = ClauseStream(top=npts * L)
    for p in range(npts):
        for ell in range(1, L):
            s.add([-count_var(p, ell + 1, L), count_var(p, ell, L)], 'u_monotonicity')
    all_u = [count_var(p, ell, L) for p in range(npts) for ell in range(1, L + 1)]
    total = add_total_exact_prefix(s, all_u, L)
    row_records = []
    for rno, (mask, cap) in enumerate(rows):
        lits = []
        for p in range(npts):
            if (mask >> p) & 1:
                for ell in range(1, L + 1):
                    lits.append(count_var(p, ell, L))
        row_records.append(add_row_atmost_forward(s, lits, cap, f'row_{rno}_mask_{mask}_cap_{cap}'))
    return s, rows, k, L, src, total, row_records


def parse_dimacs(path: Path):
    clauses = []; header = None; comments = 0
    with path.open('rt') as f:
        for line in f:
            line = line.strip()
            if not line: continue
            if line.startswith('c'):
                comments += 1; continue
            if line.startswith('p'):
                parts = line.split(); header = {'vars': int(parts[2]), 'clauses': int(parts[3]), 'raw': line}; continue
            vals = [int(x) for x in line.split()]
            if not vals or vals[-1] != 0:
                raise ValueError(f'bad DIMACS line: {line[:80]}')
            clauses.append(vals[:-1])
    return header, clauses, comments


def eval_clause(cl: Sequence[int], val: Dict[int, bool]) -> bool:
    for lit in cl:
        v = val.get(abs(lit), False)
        if (lit > 0 and v) or (lit < 0 and not v):
            return True
    return False


def extension_values_for_total_and_rows(rows: Sequence[Tuple[int, int]], ranges: Sequence[Dict], k: int, L: int, x_counts: Sequence[int]) -> Dict[int, bool]:
    npts = (1 << k) - 1
    vals: Dict[int, bool] = {}
    for p in range(npts):
        for ell in range(1, L + 1):
            vals[count_var(p, ell, L)] = (ell <= int(x_counts[p]))
    # total range first.
    total = ranges[0]
    n = total['n_prefix']; Kp = total['thresholds']; start = total['start_var']
    input_lits = [count_var(p, ell, L) for p in range(npts) for ell in range(1, L + 1)]
    assert n == len(input_lits)
    # variable id in allocated matrix: start + i*(Kp+1)+j where i,j are 0-indexed.
    pref = 0
    for i in range(1, n + 1):
        if vals[input_lits[i-1]]: pref += 1
        for j in range(1, Kp + 1):
            vals[start + i * (Kp + 1) + j] = (pref >= j)
    # row ranges follow, but cap0 rows have no range and therefore no auxiliary values.
    rr_idx = 1
    for rno, (mask, cap) in enumerate(rows):
        lits = []
        for p in range(npts):
            if (mask >> p) & 1:
                for ell in range(1, L + 1):
                    lits.append(count_var(p, ell, L))
        if cap <= 0 or cap >= len(lits):
            continue
        rec = ranges[rr_idx]; rr_idx += 1
        assert rec['name'].startswith(f'row_{rno}_')
        Kp = rec['thresholds']; start = rec['start_var']; n = rec['n_prefix']
        assert n == len(lits) and Kp == cap + 1
        pref = 0
        for i in range(1, n + 1):
            if vals[lits[i-1]]: pref += 1
            for j in range(1, Kp + 1):
                vals[start + i * (Kp + 1) + j] = (pref >= j)
    return vals


def run_forward_samples(clauses: Sequence[Sequence[int]], rows: Sequence[Tuple[int, int]], ranges: Sequence[Dict], total_record: Dict, row_records: Sequence[Dict], k: int, L: int) -> Dict:
    # The full core is UNSAT, so there is no single legal x for all rows.  We test
    # total/monotone clauses on deterministic total-L samples, and row blocks one
    # at a time with locally satisfying patterns.  The general proof is recorded
    # by clause family in proof_text below.
    npts = (1 << k) - 1
    samples = []
    for off in [0, 1, 7, 31, 63]:
        x = [0] * npts
        for i in range(L):
            x[(off + i * 5) % npts] += 1
        samples.append(x)
    failures = []
    # Row clauses begin after the global monotonicity clauses and the total
    # exact-prefix block.  total_record stores this boundary from reconstruction.
    total_end = int(total_record['clauses_after'])
    for si, x in enumerate(samples):
        vals = extension_values_for_total_and_rows(rows, ranges, k, L, x)
        for ci, cl in enumerate(clauses[:total_end]):
            if not eval_clause(cl, vals):
                failures.append({'sample': si, 'clause_index': ci, 'clause': list(cl)})
                if len(failures) >= 10: break
        if len(failures) >= 10: break
    # For each row block, choose the all-zero count vector when cap>=0.  It has
    # total 0, not total L, but row-prefix clauses only read row u-literals; this
    # tests every row-atmost block under a locally satisfying input.
    local_row_fail = []
    zero = [0] * npts
    vals_zero = extension_values_for_total_and_rows(rows, ranges, k, L, zero)
    for rec in row_records:
        for ci in range(int(rec['clauses_before']), int(rec['clauses_after'])):
            if not eval_clause(clauses[ci], vals_zero):
                local_row_fail.append({'range': rec['name'], 'clause_index': ci, 'clause': list(clauses[ci])})
                if len(local_row_fail) >= 10: break
        if len(local_row_fail) >= 10: break
    return {'total_clause_sample_failures': failures, 'local_row_zero_sample_failures': local_row_fail, 'sample_count': len(samples), 'note': 'Samples support the clause-family proof; they are not the proof because the core rows are intentionally infeasible together.'}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--meta', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args(); args.out.parent.mkdir(parents=True, exist_ok=True)
    meta = json.loads(args.meta.read_text())
    core = Path(meta['source']['source_core'])
    s, rows, k, L, src, total, row_records = reconstruct(core)
    header, clauses, comments = parse_dimacs(Path(meta['cnf_path']))
    mismatch = []
    if len(clauses) == len(s.clauses):
        for i, (a, b) in enumerate(zip(clauses, s.clauses)):
            if a != b:
                mismatch.append({'index': i, 'file': a, 'reconstructed': b})
                if len(mismatch) >= 20: break
    else:
        mismatch.append({'error': 'clause_count_mismatch', 'file_count': len(clauses), 'reconstructed_count': len(s.clauses)})
    ranges = s.ranges
    range_ok = True; prev_end = (1 << k) * L - L  # equals npts*L, written this way only to keep relation visible
    # Actually count-variable top is npts*L.
    prev_end = ((1 << k) - 1) * L
    range_problems = []
    for r in ranges:
        if r['start_var'] != prev_end + 1 or r['end_var'] < r['start_var']:
            range_ok = False; range_problems.append(r)
        prev_end = r['end_var']
    samples = run_forward_samples(clauses, rows, ranges, total, row_records, k, L)
    out = {
        'schema': 's0908_transparent_cnf_lifting_verifier_v1',
        'meaning': 'Clause-level reconstruction and forward-lifting proof record for one transparent unary-count CNF. If clauses_match_actual_file and auxiliary_ranges_disjoint_ordered are true, the DRAT UNSAT result applies to exactly the clause families whose lifting proof is recorded here.',
        'meta_path': str(args.meta),
        'core_path': str(core),
        'cnf_path': meta['cnf_path'],
        'source': src,
        'k': k,
        'L': L,
        'cnf_sha256_meta': meta.get('cnf_sha256'),
        'cnf_sha256_recomputed': sha256(Path(meta['cnf_path'])),
        'drat_verified_meta': meta.get('drat_verified'),
        'header': header,
        'file_clause_count': len(clauses),
        'reconstructed_clause_count': len(s.clauses),
        'file_comment_count': comments,
        'reconstructed_var_count': s.top,
        'meta_var_count': meta.get('vars'),
        'meta_clause_count': meta.get('clauses'),
        'clauses_match_actual_file': len(mismatch) == 0,
        'mismatches_head': mismatch,
        'stats_match_meta': dict(sorted(s.stats.items())) == meta.get('stats'),
        'stats_reconstructed': dict(sorted(s.stats.items())),
        'auxiliary_ranges_disjoint_ordered': range_ok,
        'auxiliary_range_problem_head': range_problems[:10],
        'auxiliary_range_count': len(ranges),
        'total_counter_record': total,
        'row_record_count': len(row_records),
        'row_aux_total': sum(r['aux_vars'] for r in row_records),
        'sample_checks': samples,
        'forward_lifting_proof_by_clause_family': {
            'u_monotonicity': 'u[p,ell+1] => u[p,ell] holds for u[p,ell]=(ell<=x_p).',
            'total_forward_clauses': 'For y[i,j] defined as prefix count >= j, clauses -input_i or y[i,1], -y[i-1,j] or y[i,j], and -input_i or -y[i-1,j-1] or y[i,j] are immediate monotonicity/increment implications.',
            'total_reverse_clauses': 'If prefix count for i is at least j, then either the previous prefix already had at least j or input_i is true; also either the previous prefix already had at least j or it had at least j-1. These are exactly the two reverse clause families.',
            'total_exact_units': 'The alleged quotient occupation has total L, so y[n,L] is true and y[n,L+1] is false.',
            'row_forward_clauses': 'For each occupation row the same prefix-threshold implications force row y[i,j] values from the row literals.',
            'row_terminal_clause': 'If the occupation row satisfies sum_{p in S} x_p <= cap, then among row unary literals there are at most cap true values, so y[n,cap+1] is false and the terminal clause is satisfied.',
            'cap0_rows': 'For cap 0, every included u[p,ell] must be false because the row occupancy is zero; the emitted unit clauses -u[p,ell] are satisfied.'
        },
        'forward_lifting_established_for_file': (len(mismatch) == 0 and range_ok and header is not None and header['vars'] == s.top and header['clauses'] == len(s.clauses) and meta.get('drat_verified') is True and not samples['total_clause_sample_failures'] and not samples['local_row_zero_sample_failures']),
    }
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'ok', 'out': str(args.out), 'clauses_match_actual_file': out['clauses_match_actual_file'], 'forward_lifting_established_for_file': out['forward_lifting_established_for_file'], 'vars': s.top, 'clauses': len(s.clauses)}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
