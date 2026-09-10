#!/usr/bin/env python3
"""Proof-producing rank-1 skeleton CNF with fixed higher-rank A-points.

For the exact-18 rank-1 part of a hypothetical length-20 Wang-admissible
A-support over F2, fix E11 and one or two specified higher-rank A-points H.
For each Wang row Phi the remaining rank-1 variables must satisfy

    |X ∩ R1 ∩ Phi| <= 20 - L(Phi) - |H ∩ Phi|.

The script scans the full 8,283,458-row LUT, compresses rows by their rank-1
intersection mask using the tightest residual capacity, writes a CNF over the
49 rank-1 variables with exact |X|=K, and optionally runs CaDiCaL+drat-trim.
UNSAT for all symmetry representatives of fixed high points is a checkable way
to close the near-saturated rank-1 completion surface; SAT is only a support
skeleton candidate and must still be extended/scanned if fewer than two high
points are fixed.
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
from typing import Dict, Iterable, List, Sequence, Set, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import matrix_rank_of_mask, unpack_basis, subspace_points_from_basis  # noqa: E402
from wang_capacity_cnf_e11_fixed import E11  # noqa: E402


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


def parse_ints(spec: str) -> List[int]:
    if not spec.strip():
        return []
    return [int(x) for x in spec.replace(';', ',').split(',') if x.strip()]


def rank1_points() -> List[int]:
    pts = [p for p in range(1, 512) if matrix_rank_of_mask(p) == 1]
    if len(pts) != 49:
        raise RuntimeError(f'expected 49 rank-1 points, got {len(pts)}')
    return pts


def compress_for_fixed_high(lut: Dict[int, int], rank_s: int, fixed_high: Sequence[int], r1_pts: Sequence[int]):
    t0 = time.time()
    r1_index = {p: i for i, p in enumerate(r1_pts)}
    high_set = set(int(p) for p in fixed_high)
    tight: Dict[int, int] = {}
    witness: Dict[int, dict] = {}
    raw_by_dim = Counter(); raw_by_lb = Counter(); high_in_hist = Counter(); rmask_size_hist = Counter(); residual_cap_hist = Counter()
    for idx, (key, lb0) in enumerate(lut.items(), 1):
        basis = unpack_basis(key)
        rmask = 0; high_in = 0
        for p in subspace_points_from_basis(basis):
            j = r1_index.get(p)
            if j is not None:
                rmask |= 1 << j
            if p in high_set:
                high_in += 1
        cap = rank_s - int(lb0) - high_in
        old = tight.get(rmask)
        if old is None or cap < old:
            tight[rmask] = cap
            witness[rmask] = {'key': int(key), 'dim': int(key) & 0xF, 'lb': int(lb0), 'fixed_high_in_row': high_in, 'raw_cap': rank_s - int(lb0), 'residual_cap': cap, 'basis': list(basis)}
        raw_by_dim[int(key) & 0xF] += 1; raw_by_lb[int(lb0)] += 1; high_in_hist[high_in] += 1; rmask_size_hist[rmask.bit_count()] += 1; residual_cap_hist[cap] += 1
        if idx % 1_000_000 == 0:
            print(f'compressed {idx:,}/{len(lut):,}; distinct={len(tight):,}; elapsed={time.time()-t0:.1f}s', flush=True)
    cons = [(mask, cap, witness[mask]) for mask, cap in tight.items() if mask.bit_count() > cap]
    cons.sort(key=lambda x: (x[0].bit_count(), x[1], x[0]))
    hist = Counter((m.bit_count(), c) for m, c, _ in cons)
    meta = {
        'fixed_high_points': list(fixed_high),
        'fixed_high_rank_hist': dict(sorted(Counter(matrix_rank_of_mask(p) for p in fixed_high).items())),
        'raw_subspaces': len(lut),
        'compressed_intersections': len(tight),
        'nonvacuous_constraints': len(cons),
        'constraint_size_cap_hist': {f'{a},{b}': c for (a, b), c in sorted(hist.items())},
        'raw_by_dim': dict(sorted(raw_by_dim.items())),
        'raw_by_lb': dict(sorted(raw_by_lb.items())),
        'fixed_high_in_row_hist': dict(sorted(high_in_hist.items())),
        'rank1_intersection_size_hist_raw': dict(sorted(rmask_size_hist.items())),
        'residual_cap_hist_raw': dict(sorted(residual_cap_hist.items())),
        'elapsed_sec': time.time() - t0,
    }
    return cons, meta


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
    def close_with_header(self, nv: int):
        self.fh.close()
        with self.final_path.open('w') as out:
            out.write(f'p cnf {nv} {self.nclauses}\n')
            with self.body_path.open('r') as body:
                shutil.copyfileobj(body, out, length=16 * 1024 * 1024)
        self.body_path.unlink(missing_ok=True)


def add_atmost(writer: DimacsWriter, lits: List[int], bound: int, top_id: int):
    from pysat.card import CardEnc, EncType
    if bound < 0:
        writer.add_clause([])
        return top_id, 1, 0
    if len(lits) <= bound:
        return top_id, 0, 0
    enc = CardEnc.atmost(lits=lits, bound=bound, top_id=top_id, encoding=EncType.seqcounter)
    for cl in enc.clauses:
        writer.add_clause(cl)
    return enc.nv, len(enc.clauses), max(0, enc.nv - top_id)


def write_cnf(r1_pts: List[int], cons: Sequence[Tuple[int, int, dict]], exact_count: int,
              fixed_rank1: Sequence[int], cnf: Path, meta_path: Path, rank_s: int,
              fixed_high: Sequence[int], compression_meta: dict, lut_meta: dict,
              direct_comb_limit: int) -> dict:
    from pysat.card import CardEnc, EncType
    t0 = time.time(); writer = DimacsWriter(cnf); top = len(r1_pts); var = {p: i + 1 for i, p in enumerate(r1_pts)}
    enc = CardEnc.equals(lits=list(var.values()), bound=exact_count, top_id=top, encoding=EncType.seqcounter)
    for cl in enc.clauses:
        writer.add_clause(cl)
    top = enc.nv
    for p in fixed_rank1:
        writer.add_clause([var[p]] if p in var else [])
    hist = Counter(); direct_rows = 0; direct_clauses = 0; card_rows = 0; card_clauses = 0; aux_vars = 0; skipped = 0; witness_head = []
    for mask, cap, wit in cons:
        lits = [i + 1 for i in range(len(r1_pts)) if (int(mask) >> i) & 1]
        hist[(len(lits), int(cap))] += 1
        if len(lits) <= int(cap):
            skipped += 1; continue
        combs = math.comb(len(lits), int(cap) + 1) if int(cap) >= 0 and int(cap) + 1 <= len(lits) else 0
        if int(cap) >= 0 and combs <= direct_comb_limit:
            for comb in itertools.combinations(lits, int(cap) + 1):
                writer.add_clause([-v for v in comb])
            direct_rows += 1; direct_clauses += combs
        else:
            old = top
            top, ncl, naux = add_atmost(writer, lits, int(cap), top)
            card_rows += 1; card_clauses += ncl; aux_vars += naux
            if top < old:
                raise RuntimeError('top_id decreased')
        if len(witness_head) < 200:
            w = dict(wit); w['intersection_size'] = len(lits); w['cap'] = int(cap); w['clauses_if_direct'] = combs
            witness_head.append(w)
    writer.close_with_header(top)
    payload = {
        'problem': 'rank-1 skeleton CNF with fixed higher-rank A-points',
        'field': 'F2',
        'rank_s_for_capacities': rank_s,
        'exact_rank1_count': exact_count,
        'fixed_rank1_points': list(fixed_rank1),
        'fixed_high_points': list(fixed_high),
        'rank1_points': r1_pts,
        'compression': compression_meta,
        'selected_constraint_count': len(cons),
        'selected_constraint_hist': {f'{a},{b}': c for (a, b), c in sorted(hist.items())},
        'num_vars': top,
        'num_clauses': writer.nclauses,
        'empty_clause_count': writer.empty_clause_count,
        'global_exact_count_clauses': len(enc.clauses),
        'fixed_rank1_unit_clauses': len(fixed_rank1),
        'direct_rows': direct_rows,
        'direct_capacity_clauses': direct_clauses,
        'cardinality_capacity_rows': card_rows,
        'cardinality_capacity_clauses': card_clauses,
        'capacity_aux_vars': aux_vars,
        'skipped_vacuous_after_compression': skipped,
        'direct_comb_limit': direct_comb_limit,
        'witness_head': witness_head,
        'lut_meta_brief': {'coverage_ok': lut_meta.get('coverage_ok'), 'conflict_count': lut_meta.get('conflict_count'), 'subspace_count': lut_meta.get('subspace_count')},
        'cnf_path': str(cnf),
        'elapsed_sec': time.time() - t0,
        'meaning': 'UNSAT proves no exact-rank1-count Wang support skeleton with these fixed higher-rank A-points. SAT is only rank-1 skeleton feasibility under the fixed high prefix.'
    }
    meta_path.parent.mkdir(parents=True, exist_ok=True)
    meta_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: payload[k] for k in ['selected_constraint_count','selected_constraint_hist','num_vars','num_clauses','empty_clause_count','direct_rows','cardinality_capacity_rows','elapsed_sec']}, indent=2, sort_keys=True))
    return payload


def parse_solver_log(path: Path) -> dict:
    if not path.exists():
        return {'exists': False}
    text = path.read_text(errors='replace')
    return {'exists': True, 'unsat': 's UNSATISFIABLE' in text, 'sat': 's SATISFIABLE' in text, 'verified': 's VERIFIED' in text}


def run_solver(cnf: Path, timeout: int) -> dict:
    drat = cnf.with_suffix('.drat'); cadlog = cnf.with_suffix('.cadical.log'); trimlog = cnf.with_suffix('.drat_trim.log'); status_path = cnf.with_suffix('.status.json')
    cmd = ['cadical', '--unsat', '--binary=false', '-n']
    if timeout > 0:
        cmd += ['-t', str(timeout)]
    cmd += [str(cnf), str(drat)]
    t0 = time.time()
    with cadlog.open('w') as f:
        proc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, text=True)
    res = {'cnf': str(cnf), 'drat': str(drat), 'cadical_log': str(cadlog), 'drat_trim_log': str(trimlog), 'cadical_exit': proc.returncode, 'cadical_elapsed_sec': time.time() - t0}
    if proc.returncode == 20:
        t1 = time.time()
        with trimlog.open('w') as f:
            trim = subprocess.run(['drat-trim', str(cnf), str(drat)], stdout=f, stderr=subprocess.STDOUT, text=True)
        res['drat_trim_exit'] = trim.returncode; res['drat_trim_elapsed_sec'] = time.time() - t1
    else:
        res['drat_trim_exit'] = None; res['drat_trim_elapsed_sec'] = None
    res['hashes'] = {str(p): sha256(p) for p in [cnf, cnf.with_suffix('.meta.json'), drat, cadlog, trimlog] if p.exists()}
    res['cadical_log_parse'] = parse_solver_log(cadlog); res['drat_trim_log_parse'] = parse_solver_log(trimlog)
    status_path.write_text(json.dumps(res, indent=2, sort_keys=True) + '\n')
    print(json.dumps(res, indent=2, sort_keys=True))
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path, default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank-s', type=int, default=20)
    ap.add_argument('--exact-rank1-count', type=int, default=18)
    ap.add_argument('--fixed-rank1', default='1')
    ap.add_argument('--fixed-high', required=True, help='comma-separated non-rank-1 masks fixed as selected higher-rank A-points')
    ap.add_argument('--cnf', type=Path, required=True)
    ap.add_argument('--meta', type=Path, required=True)
    ap.add_argument('--direct-comb-limit', type=int, default=2000)
    ap.add_argument('--solve', action='store_true')
    ap.add_argument('--solver-time', type=int, default=0)
    args = ap.parse_args()
    fixed_rank1 = parse_ints(args.fixed_rank1); fixed_high = parse_ints(args.fixed_high)
    for p in fixed_rank1:
        if matrix_rank_of_mask(p) != 1:
            raise SystemExit(f'fixed-rank1 point {p} does not have matrix rank 1')
    for p in fixed_high:
        if matrix_rank_of_mask(p) <= 1:
            raise SystemExit(f'fixed-high point {p} is not rank 2 or 3')
    lut, lmeta = load_lut(args.lut)
    print(f'loaded LUT {len(lut):,} coverage={lmeta.get("coverage_ok")} conflicts={lmeta.get("conflict_count")} fixed_high={fixed_high}', flush=True)
    r1_pts = rank1_points()
    cons, cmeta = compress_for_fixed_high(lut, args.rank_s, fixed_high, r1_pts)
    write_cnf(r1_pts, cons, args.exact_rank1_count, fixed_rank1, args.cnf, args.meta, args.rank_s, fixed_high, cmeta, lmeta, args.direct_comb_limit)
    if args.solve:
        run_solver(args.cnf, args.solver_time)


if __name__ == '__main__':
    main()
