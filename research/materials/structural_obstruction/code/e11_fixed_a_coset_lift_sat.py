#!/usr/bin/env python3
"""Fixed-A-assignment coset lift SAT for E11 quotient decompositions.

Given a quotient CPD, a prefix V, and a specific cover assignment of A-vectors
for the residual terms, this builds a much smaller SAT instance than the
general coset SAT by eliminating the A-factor search layer.

Variables: c_{k,j} corrections (4*q) + b_t (s*9) + d_t (s*9) + p_{t,b,c} (s*81)
Total: 4*q + s*(9+9+81) = 4*q + 99*s  (vs 4*q + 4*s + 18*s + 324*s for general)
"""
from __future__ import annotations
import argparse, json, time, re, subprocess, hashlib
from pathlib import Path
from collections import Counter
import numpy as np

import sys
SCRIPTS = Path('scripts')
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import e11_quotient_lift_general_sat as glift


class XCNF:
    def __init__(self):
        self.next = 1
        self.cnf = []
        self.xors = []

    def new(self):
        v = self.next; self.next += 1; return v

    def add(self, lits):
        self.cnf.append([int(x) for x in lits])

    def add_and(self, z, a, b):
        self.add([-a, -b, z]); self.add([a, -z]); self.add([b, -z])

    def add_xor(self, lits, rhs):
        ll = [int(x) for x in lits]; rhs = int(rhs) & 1
        if not ll:
            if rhs: self.add([])
            return
        self.xors.append((ll, rhs))

    def write_native(self, path, comments=None):
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('w') as f:
            for c in (comments or []):
                f.write('c ' + str(c) + '\n')
            f.write(f'p cnf {self.next-1} {len(self.cnf)+len(self.xors)}\n')
            for lits, rhs in self.xors:
                ll = list(lits)
                if rhs == 0: ll[0] = -ll[0]
                f.write('x ' + ' '.join(map(str, ll)) + ' 0\n')
            for cl in self.cnf:
                f.write(' '.join(map(str, cl)) + ' 0\n')


class FixedACosetSAT:
    def __init__(self, Rcoords, M_rows, a_assignment, q):
        """
        Rcoords: (4,9,9) residual tensor in V-coordinates
        M_rows: list of q items, each a list of 9 row-ints (9-bit) for quotient M_j
        a_assignment: list of s 4-bit masks (A-vectors in V-coordinates for residual terms)
        q: number of quotient terms
        """
        self.Rcoords = np.array(Rcoords, dtype=np.uint8) & 1
        self.M_rows = M_rows
        self.a_assign = [int(a) for a in a_assignment]
        self.s = len(a_assignment)
        self.q = q
        self.F = XCNF()
        self.corr = {}
        self.bvar = {}
        self.dvar = {}
        self.pvar = {}
        self._build()

    def _build(self):
        # Correction variables c_{k,j}
        for k in range(4):
            for j in range(self.q):
                self.corr[(k,j)] = self.F.new()
        # Residual B and C (here called d) variables
        for t in range(self.s):
            for b in range(9):
                self.bvar[(t,b)] = self.F.new()
            for c in range(9):
                self.dvar[(t,c)] = self.F.new()
            # Nonzero constraints
            self.F.add([self.bvar[(t,b)] for b in range(9)])
            self.F.add([self.dvar[(t,c)] for c in range(9)])
        # Product variables p_{t,b,c} = bvar[t,b] AND dvar[t,c]
        for t in range(self.s):
            for b in range(9):
                for c in range(9):
                    z = self.F.new()
                    self.pvar[(t,b,c)] = z
                    self.F.add_and(z, self.bvar[(t,b)], self.dvar[(t,c)])
        # XOR constraints: for each k,b,c
        for k in range(4):
            for b in range(9):
                for c in range(9):
                    lits = []
                    bit = 1 << c
                    # Correction terms
                    for j, rows in enumerate(self.M_rows):
                        if rows[b] & bit:
                            lits.append(self.corr[(k,j)])
                    # Residual terms with a_t[k]=1
                    for t in range(self.s):
                        if (self.a_assign[t] >> k) & 1:
                            lits.append(self.pvar[(t,b,c)])
                    self.F.add_xor(lits, int(self.Rcoords[k,b,c]))

    def decode(self, model_lits):
        pos = {int(x) for x in model_lits if int(x) > 0}
        C = np.zeros((4, self.q), dtype=np.uint8)
        for k in range(4):
            for j in range(self.q):
                if self.corr[(k,j)] in pos: C[k,j] = 1
        res_b = []
        res_d = []
        for t in range(self.s):
            vm = sum((1 << b) for b in range(9) if self.bvar[(t,b)] in pos)
            wm = sum((1 << c) for c in range(9) if self.dvar[(t,c)] in pos)
            res_b.append(vm)
            res_d.append(wm)
        return C, self.a_assign, res_b, res_d


def solve_native(cnf_path, solver, timeout, threads):
    cmd = [solver, '--verb', '0', '-t', str(threads), '--maxtime', str(timeout), str(cnf_path)]
    t0 = time.time()
    try:
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            text=True, timeout=timeout+20)
        status = 'UNKNOWN'
        if re.search(r'\bUNSATISFIABLE\b', proc.stdout): status = 'UNSAT'
        elif re.search(r'\bSATISFIABLE\b', proc.stdout): status = 'SAT'
        model = None
        if status == 'SAT':
            model = []
            for line in proc.stdout.splitlines():
                if line.startswith('v'):
                    for tok in line.split()[1:]:
                        try:
                            z = int(tok)
                            if z: model.append(z)
                        except ValueError: pass
        return {'status': status, 'elapsed_sec': time.time()-t0, 'model': model,
                'returncode': proc.returncode}
    except subprocess.TimeoutExpired:
        return {'status': 'TIMEOUT', 'elapsed_sec': time.time()-t0, 'model': None}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pool', type=Path, required=True)
    ap.add_argument('--prefix', required=True)
    ap.add_argument('--cover', required=True,
                    help='comma-separated A-mask assignment, e.g. "2,2,3,4,5,8,9,12"')
    ap.add_argument('--outdir', type=Path, required=True)
    ap.add_argument('--name', default='fixed_a_lift')
    ap.add_argument('--scheme-idx', type=int, default=-1)
    ap.add_argument('--max-schemes', type=int, default=0)
    ap.add_argument('--timeout-per-scheme', type=int, default=120)
    ap.add_argument('--threads', type=int, default=8)
    ap.add_argument('--solver', default='cryptominisat5')
    ap.add_argument('--stop-on-first-sat', action='store_true')
    args = ap.parse_args()

    t0 = time.time()
    args.outdir.mkdir(parents=True, exist_ok=True)
    prefix = [int(x) for x in args.prefix.split(',') if x.strip()]
    a_assign = [int(x) for x in args.cover.split(',') if x.strip()]
    s = len(a_assign)

    core = glift.build_e11_core()
    pool = np.load(args.pool)
    indices = [args.scheme_idx] if args.scheme_idx >= 0 else list(range(pool.shape[0]))
    if args.max_schemes > 0: indices = indices[:args.max_schemes]

    records = []
    witness = None
    for pos, idx in enumerate(indices):
        scheme = pool[idx]
        meta, Rcoords, lifts, b_masks, c_masks, M_rows = glift.scheme_to_residual(core, prefix, scheme)
        q = meta['qrank']
        rec = {'scheme_idx': int(idx), **meta, 'a_assignment': a_assign, 's': s}

        if meta['quotient_diff'] or any(meta['annihilator_residual_nnz']):
            rec['status'] = 'BAD_INPUT'; records.append(rec); continue

        enc = FixedACosetSAT(Rcoords, M_rows, a_assign, q)
        cnf_path = args.outdir / f'{args.name}_s{idx}.xor.cnf'
        enc.F.write_native(cnf_path, [
            f'fixed-A coset lift: prefix={prefix} cover={a_assign}',
            f'scheme_idx={idx} q={q} s={s}',
        ])
        sol = solve_native(cnf_path, args.solver, args.timeout_per_scheme, args.threads)
        model = sol.pop('model', None)
        rec.update({
            'vars': enc.F.next-1, 'cnf_clauses': len(enc.F.cnf),
            'xor_clauses': len(enc.F.xors), 'solve': sol,
        })

        if sol['status'] == 'SAT' and model:
            C, res_a4, res_b, res_d = enc.decode(model)
            # Convert to full E11 decomposition
            e11_dec = glift.lift_to_full_e11(core, prefix, lifts, b_masks, c_masks,
                                             C, res_a4, res_b, res_d)
            rec['e11_decomposition'] = e11_dec
            if e11_dec['e11_verified']:
                t333_dec = glift.lift_e11_to_t333(e11_dec)
                rec['t333_decomposition'] = t333_dec
                witness = rec
                rank = e11_dec['e11_rank_upper_bound']
                print(f"SCHEME {idx}: SAT verified E11 rank <= {rank}")
                if t333_dec['t333_verified']:
                    print(f"SCHEME {idx}: FULL T333 rank <= {t333_dec['t333_rank_upper_bound']} verified")
                if args.stop_on_first_sat:
                    records.append(rec); break

        if not cnf_path.exists() or sol['status'] != 'SAT':
            if cnf_path.exists(): cnf_path.unlink()
        records.append(rec)
        print(f"scheme {idx}: {sol['status']} {sol['elapsed_sec']:.1f}s "
              f"vars={rec['vars']} xors={rec['xor_clauses']}")

    counts = Counter(r.get('solve',{}).get('status', r.get('status','?')) for r in records)
    summary = {
        'purpose': 'fixed-A-assignment coset lift SAT for E11 quotient schemes',
        'field': 'F2', 'prefix': prefix, 'a_assignment': a_assign, 's': s,
        'pool': str(args.pool), 'schemes_tested': len(records),
        'status_counts': dict(counts),
        'witness_found': witness is not None,
        'elapsed_sec': time.time()-t0,
        'records': records,
    }
    out = args.outdir / f'{args.name}.json'
    out.write_text(json.dumps(summary, indent=2, sort_keys=True, default=int)+'\n')
    print(json.dumps({k: summary[k] for k in
          ['schemes_tested','status_counts','witness_found','elapsed_sec']}, indent=2))
    print(f'wrote {out}')


if __name__ == '__main__':
    main()
