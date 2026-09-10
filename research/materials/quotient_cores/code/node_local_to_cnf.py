#!/usr/bin/env python3
"""Export node-local Wang occupation raise instances to CNF and optionally DRAT-check.

For a Wang node W with old LB L, occupation raising asks whether there is an
integer multiset of size L in the quotient A-space satisfying all inherited rows
from strict super-subspaces U>W.  This script encodes the same finite system used
by node_local_occupation_closure.py into SAT with Boolean slot variables y_{s,q}:
slot s chooses quotient point q.  It is intentionally simple and proof-oriented,
not optimized.  UNSAT plus a checked DRAT proof certifies this node-local
occupation raise for the particular W basis and Wang LUT.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))

from node_local_occupation_closure import load_data, node_constraints  # type: ignore


class CNF:
    def __init__(self):
        self.nv = 0
        self.clauses: List[List[int]] = []
    def new_var(self) -> int:
        self.nv += 1
        return self.nv
    def add_clause(self, cl: Sequence[int]):
        self.clauses.append([int(x) for x in cl])
    def add_at_most_seq(self, lits: Sequence[int], k: int):
        lits = list(lits)
        n = len(lits)
        if k < 0:
            self.add_clause([]); return
        if k >= n:
            return
        if k == 0:
            for x in lits: self.add_clause([-x])
            return
        # Sinz sequential counter for at-most-k.
        s = [[self.new_var() for _ in range(k)] for __ in range(n-1)]
        # i=0
        self.add_clause([-lits[0], s[0][0]])
        for j in range(1, k):
            self.add_clause([-s[0][j]])
        # middle
        for i in range(1, n-1):
            self.add_clause([-lits[i], s[i][0]])
            self.add_clause([-s[i-1][0], s[i][0]])
            for j in range(1, k):
                self.add_clause([-lits[i], -s[i-1][j-1], s[i][j]])
                self.add_clause([-s[i-1][j], s[i][j]])
            self.add_clause([-lits[i], -s[i-1][k-1]])
        # last input cannot make k+1
        self.add_clause([-lits[n-1], -s[n-2][k-1]])
    def write(self, path: Path, comments: Sequence[str] = ()): 
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('w') as f:
            for c in comments:
                f.write('c ' + c.replace('\n', ' ') + '\n')
            f.write(f'p cnf {self.nv} {len(self.clauses)}\n')
            for cl in self.clauses:
                f.write(' '.join(map(str, cl)) + ' 0\n')


def find_record(closure: Dict, index: int) -> Dict:
    for r in closure['results']:
        if int(r.get('cert_index', -1)) == index or int(r.get('position', -1)) == index:
            return r
    raise KeyError(index)


def encode_record(rec: Dict, cnf_path: Path) -> Dict:
    lut, _ = load_data()
    basis = tuple(int(x) for x in rec['basis'])
    L = int(rec['support_size_tested'])
    k = int(rec['quotient_dim'])
    constraints, meta = node_constraints(basis, lut, L)
    npts = (1 << k) - 1
    F = CNF()
    y = [[F.new_var() for _ in range(npts)] for __ in range(L)]
    for s in range(L):
        # exactly one point in each slot: at least one + pairwise at most one (127 small enough)
        F.add_clause(y[s])
        for i in range(npts):
            yi = y[s][i]
            for j in range(i+1, npts):
                F.add_clause([-yi, -y[s][j]])
    slot_choice_clauses = len(F.clauses)
    active_constraints = 0
    skipped_taut = 0
    for mask, cap in constraints:
        if cap >= L:
            skipped_taut += 1
            continue
        lits = [y[s][i] for s in range(L) for i in range(npts) if (mask >> i) & 1]
        F.add_at_most_seq(lits, int(cap))
        active_constraints += 1
    F.write(cnf_path, comments=[
        f'node-local occupation raise cert_index={rec["cert_index"]}',
        f'basis={rec["basis"]} old_lb={rec["old_lb"]} support_size={L} quotient_dim={k}',
        f'constraints={active_constraints} taut={skipped_taut}',
    ])
    return {
        'cert_index': int(rec['cert_index']),
        'basis': [int(x) for x in basis],
        'old_lb': int(rec['old_lb']),
        'attempted_new_lb': int(rec['attempted_new_lb']),
        'support_size': L,
        'quotient_dim': k,
        'npts': npts,
        'constraint_meta': meta,
        'active_constraints': active_constraints,
        'skipped_taut_constraints': skipped_taut,
        'cnf_vars': F.nv,
        'cnf_clauses': len(F.clauses),
        'slot_choice_clauses': slot_choice_clauses,
        'cnf_path': str(cnf_path),
    }


def run_cmd(cmd: List[str], timeout: int) -> Dict:
    t0 = time.time()
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 20)
    return {
        'command': cmd,
        'returncode': int(proc.returncode),
        'elapsed_sec': time.time() - t0,
        'stdout_tail': '\n'.join(proc.stdout.splitlines()[-80:]),
        'stderr_tail': '\n'.join(proc.stderr.splitlines()[-80:]),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--closure-json', type=Path, default=Path('data/wang_analysis/node_local/dim2_raise_original_900s.json'))
    ap.add_argument('--index', type=int, required=True)
    ap.add_argument('--outdir', type=Path, required=True)
    ap.add_argument('--timeout', type=int, default=300)
    ap.add_argument('--proof', action='store_true')
    ap.add_argument('--check-proof', action='store_true')
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    closure = json.loads(args.closure_json.read_text())
    rec = find_record(closure, args.index)
    cnf = args.outdir / f'node_{args.index}_raise.cnf'
    info = encode_record(rec, cnf)
    drat = args.outdir / f'node_{args.index}_raise.drat'
    cmd = ['cadical', '-n', '-t', str(args.timeout), str(cnf)]
    if args.proof:
        cmd.append(str(drat))
    solver = run_cmd(cmd, args.timeout)
    solver['sat'] = False if solver['returncode'] == 20 else True if solver['returncode'] == 10 else None
    solver['proof_path'] = str(drat) if args.proof else None
    solver['proof_size'] = drat.stat().st_size if args.proof and drat.exists() else None
    check = None
    if args.check_proof and args.proof and solver['sat'] is False:
        check = run_cmd(['drat-trim', str(cnf), str(drat)], max(40000, args.timeout))
    out = {'schema': 'node_local_to_cnf_result_v1', 'encoding': info, 'solver': solver, 'proof_check': check}
    out_path = args.outdir / f'node_{args.index}_raise_result.json'
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'out': str(out_path),
        'index': args.index,
        'sat': solver['sat'],
        'returncode': solver['returncode'],
        'vars': info['cnf_vars'],
        'clauses': info['cnf_clauses'],
        'proof_size': solver['proof_size'],
        'proof_check_returncode': None if check is None else check['returncode'],
        'elapsed_sec': solver['elapsed_sec'],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
