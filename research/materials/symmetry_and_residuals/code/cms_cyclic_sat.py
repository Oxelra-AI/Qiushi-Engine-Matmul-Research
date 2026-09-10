#!/usr/bin/env python3
"""
analysis: CryptoMiniSat5 encoding for cyclic-invariant rank-22 over F_2.

Uses native XOR clauses (Gaussian elimination) instead of Tseitin XOR chains.
AND gates remain as regular Tseitin clauses; the top-level Brent equations
become single XOR clauses of the product variables.

CryptoMiniSat's built-in Gauss elimination can propagate parity constraints
far more efficiently than pure CDCL on the equivalent CNF.
"""

import json, os, subprocess, sys, time
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA_DIR = WS / 'data' / 'cyclic_sat'


def build_T333():
    T = [[[0]*9 for _ in range(9)] for _ in range(9)]
    for a in range(3):
        for b in range(3):
            for c in range(3):
                T[3*a+b][3*b+c][3*c+a] = 1
    return T


def cyclic_orbit_reps():
    seen = set()
    reps = []
    for i in range(9):
        for j in range(9):
            for k in range(9):
                if (i,j,k) not in seen:
                    orb = set(); t = (i,j,k)
                    while t not in orb:
                        orb.add(t); t = (t[1],t[2],t[0])
                    reps.append(min(orb)); seen |= orb
    reps.sort()
    return reps


class CMSEncoder:
    """Encoder producing AND-gates + native XOR clauses for CryptoMiniSat5."""

    def __init__(self):
        self.nv = 0
        self.reg = []      # regular (Tseitin AND + symmetry) clauses
        self.xors = []      # native XOR clauses: (target_bit, [var_list])

    def new_var(self):
        self.nv += 1; return self.nv

    def new_vars(self, n):
        return [self.new_var() for _ in range(n)]

    def _cl(self, *lits):
        self.reg.append(lits)

    def AND2(self, a, b):
        if a == b: return a
        p = self.new_var()
        self._cl(-a, -b, p); self._cl(a, -p); self._cl(b, -p)
        return p

    def AND3(self, a, b, c):
        if a == b: return self.AND2(a, c)
        if a == c: return self.AND2(a, b)
        if b == c: return self.AND2(a, b)
        return self.AND2(self.AND2(a, b), c)

    def add_xor(self, terms, target):
        """Native XOR clause: XOR(terms) = target ∈ {0,1}."""
        self.xors.append((target, list(terms)))

    def add_lex_le(self, a, b):
        n = len(a); eq = None
        for j in range(n):
            if eq is None:
                self._cl(-a[j], b[j])
            else:
                self._cl(-eq, -a[j], b[j])
            if j < n - 1:
                eq_j = self.new_var()
                if eq is None:
                    self._cl(-eq_j, -a[j], b[j])
                    self._cl(-eq_j, a[j], -b[j])
                    self._cl(-a[j], -b[j], eq_j)
                    self._cl(a[j], b[j], eq_j)
                else:
                    self._cl(-eq_j, eq)
                    self._cl(-eq_j, -a[j], b[j])
                    self._cl(-eq_j, a[j], -b[j])
                    self._cl(-eq, -a[j], -b[j], eq_j)
                    self._cl(-eq, a[j], b[j], eq_j)
                eq = eq_j

    def write(self, path):
        nc = len(self.reg) + len(self.xors)
        with open(path, 'w') as f:
            f.write(f'p cnf {self.nv} {nc}\n')
            for cl in self.reg:
                f.write(' '.join(map(str, cl)) + ' 0\n')
            for (tgt, terms) in self.xors:
                if not terms:
                    if tgt: f.write('0\n')
                    continue
                lits = terms[:]
                if tgt == 0:
                    lits[0] = -lits[0]
                f.write('x ' + ' '.join(map(str, lits)) + ' 0\n')


def encode(f, m, T333, reps, sym_break=True):
    """Encode cyclic-invariant Brent equations with CMS-native XOR."""
    enc = CMSEncoder()
    u = [enc.new_vars(9) for _ in range(f)]
    U = [enc.new_vars(9) for _ in range(m)]
    V = [enc.new_vars(9) for _ in range(m)]
    W = [enc.new_vars(9) for _ in range(m)]

    if sym_break:
        for s in range(f - 1):
            enc.add_lex_le(u[s], u[s+1])
        for o in range(m - 1):
            enc.add_lex_le(U[o]+V[o]+W[o], U[o+1]+V[o+1]+W[o+1])
        for o in range(m):
            enc.add_lex_le(U[o], V[o])
            enc.add_lex_le(U[o], W[o])

    for (i,j,k) in reps:
        target = T333[i][j][k]
        terms = []

        for s in range(f):
            terms.append(enc.AND3(u[s][i], u[s][j], u[s][k]))

        for o in range(m):
            if i == j == k:
                terms.append(enc.AND3(U[o][i], V[o][i], W[o][i]))
            else:
                terms.append(enc.AND3(U[o][i], V[o][j], W[o][k]))
                terms.append(enc.AND3(V[o][i], W[o][j], U[o][k]))
                terms.append(enc.AND3(W[o][i], U[o][j], V[o][k]))

        enc.add_xor(terms, target)

    return enc, {'u': u, 'U': U, 'V': V, 'W': W}


def run_cms(cnf, timeout=300):
    t0 = time.time()
    try:
        r = subprocess.run(['cryptominisat5', '--verb', '0', str(cnf)],
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT', {}, time.time()-t0
    dt = time.time()-t0
    if r.returncode == 10:
        assign = {}
        for line in r.stdout.splitlines():
            if line.startswith('v '):
                for tok in line[2:].split():
                    lit = int(tok)
                    if lit == 0: break
                    assign[abs(lit)] = (lit > 0)
        return 'SAT', assign, dt
    elif r.returncode == 20:
        return 'UNSAT', {}, dt
    return 'UNKNOWN', {}, dt


def verify_brent(u_vecs, orbits, T333):
    err = 0
    for i in range(9):
        for j in range(9):
            for k in range(9):
                v = 0
                for u in u_vecs:
                    v ^= (u[i] & u[j] & u[k])
                for (U,V,W) in orbits:
                    v ^= (U[i] & V[j] & W[k])
                    v ^= (V[i] & W[j] & U[k])
                    v ^= (W[i] & U[j] & V[k])
                if v != T333[i][j][k]:
                    err += 1
    return err


def extract(assign, vmap, f, m):
    u_vecs = [[int(assign.get(vmap['u'][s][i], False)) for i in range(9)]
              for s in range(f)]
    orbits = [([int(assign.get(vmap['U'][o][i], False)) for i in range(9)],
               [int(assign.get(vmap['V'][o][i], False)) for i in range(9)],
               [int(assign.get(vmap['W'][o][i], False)) for i in range(9)])
              for o in range(m)]
    return u_vecs, orbits


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--timeout', type=int, default=600)
    ap.add_argument('--ranks', default='22,23,27')
    args = ap.parse_args()

    DATA_DIR.mkdir(parents=True, exist_ok=True)
    T333 = build_T333()
    reps = cyclic_orbit_reps()
    assert len(reps) == 249

    print(f"CryptoMiniSat5 cyclic-invariant Brent SAT")
    print(f"249 equations with native XOR + Gaussian elimination\n")

    target_ranks = sorted(set(int(x) for x in args.ranks.split(',')))
    tests = []
    for r in target_ranks:
        for f in range(r+1):
            if (r - f) % 3 == 0:
                tests.append((f'rank{r}', f, (r-f)//3, r))

    results = []
    for (label, f, m, r) in tests:
        tag = f"{label}_f{f}_m{m}"
        print(f"{'='*60}")
        print(f"{tag}  rank={r}  primary={9*f+27*m}")

        t0 = time.time()
        enc, vmap = encode(f, m, T333, reps, sym_break=True)
        t_enc = time.time()-t0

        path = DATA_DIR / f'cms_{tag}.cnf'
        enc.write(str(path))

        n_reg = len(enc.reg); n_xor = len(enc.xors)
        print(f"  {enc.nv} vars, {n_reg} regular + {n_xor} XOR clauses ({t_enc:.2f}s)")

        status, assign, dt = run_cms(path, args.timeout)
        print(f"  {status}  ({dt:.2f}s)")

        rec = dict(label=label, f=f, m=m, rank=r,
                   total_vars=enc.nv, regular_clauses=n_reg, xor_clauses=n_xor,
                   status=status, solve_sec=round(dt, 3))

        if status == 'SAT':
            u_vecs, orbits = extract(assign, vmap, f, m)
            err = verify_brent(u_vecs, orbits, T333)
            rec['brent_errors'] = err
            if err == 0:
                rec['u_vecs'] = u_vecs
                rec['orbits'] = [list(o) for o in orbits]
                nzc = sum(1 for u in u_vecs if any(u))
                nzo = sum(1 for (U,V,W) in orbits if any(U) or any(V) or any(W))
                print(f"  *** VERIFIED: {nzc} cubes + {nzo} orbits ***")
            else:
                print(f"  SAT but {err} Brent errors!")
        results.append(rec)

    # Summary
    print(f"\n{'='*60}")
    print("SUMMARY")
    for rec in results:
        tag = f"({rec['f']},{rec['m']})"
        extra = f"  err={rec.get('brent_errors','')}" if rec['status']=='SAT' else ""
        print(f"  {rec['label']:8s} {tag:8s} r={rec['rank']:2d}: "
              f"{rec['status']:8s} {rec['solve_sec']:8.2f}s{extra}")

    r22 = [r for r in results if r['label']=='rank22']
    r22u = sum(1 for r in r22 if r['status']=='UNSAT')
    r22s = sum(1 for r in r22 if r['status']=='SAT')
    print(f"\nRank-22: {len(r22)} total, {r22u} UNSAT, {r22s} SAT, "
          f"{len(r22)-r22u-r22s} other")
    if r22u == len(r22) and len(r22) > 0:
        print("  ==> ALL rank-22 cyclic skeletons UNSAT over F_2!")

    out = DATA_DIR / 'cms_cyclic_results.json'
    out.write_text(json.dumps({'results': results}, indent=2, default=str)+'\n')
    print(f"\nSaved: {out}")


if __name__ == '__main__':
    main()
