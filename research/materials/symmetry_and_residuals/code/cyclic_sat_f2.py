#!/usr/bin/env python3
"""
analysis: Cyclic-invariant rank-22 SAT search for T_{<3,3,3>} over F_2.

For each skeleton (f,m) with f + 3m = target_rank, encodes the cyclic-
invariant Brent equations as DIMACS CNF and solves with Kissat.

Over F_2, the cyclic ansatz has:
  f "cube" terms  u_s ⊗ u_s ⊗ u_s           (s = 1..f)
  m "orbit" terms, each giving 3 rank-one tensors via cyclic rotation
Total rank = f + 3m.

The 729 Brent equations reduce to 249 (= dim of cyclic-invariant subspace).
Each equation is a degree-3 polynomial over GF(2).

If ALL rank-22 skeletons are UNSAT, the entire cyclic-invariant F_2 family
at rank ≤ 22 is excluded.  DRAT proofs are generated and verified when UNSAT.
"""

import argparse, json, os, subprocess, sys, time
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA_DIR = WS / 'data' / 'cyclic_sat'


# ────────────────── tensor and orbit infrastructure ──────────────────────────

def build_T333():
    """Build the 9×9×9 matrix multiplication tensor T_{<3,3,3>}."""
    T = [[[0]*9 for _ in range(9)] for _ in range(9)]
    for a in range(3):
        for b in range(3):
            for c in range(3):
                T[3*a+b][3*b+c][3*c+a] = 1
    return T


def cyclic_orbit_reps(n=9):
    """Return sorted orbit representatives for {0..n-1}^3 / cyclic."""
    seen = set()
    reps = []
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if (i, j, k) not in seen:
                    orb = set()
                    t = (i, j, k)
                    while t not in orb:
                        orb.add(t)
                        t = (t[1], t[2], t[0])
                    reps.append(min(orb))
                    seen |= orb
    reps.sort()
    return reps


def sym3_quotient(T333, orbit_reps):
    """
    Compute 84-dim quotient of T333 modulo Sym^3(F_2^9).
    
    All-different cyclic orbits come in transpose pairs:
    orbit A = {(i,j,k), ...} pairs with orbit B = {(j,i,k), ...}.
    Quotient coordinate = T333[rep_A] XOR T333[rep_B].
    """
    seen = set()
    pairs = []
    for rep in orbit_reps:
        i, j, k = rep
        if i == j or j == k or i == k:
            continue  # fixed or two-equal: in Sym^3
        t_orb = [(j, i, k), (i, k, j), (k, j, i)]
        t_rep = min(t_orb)
        pair = (min(rep, t_rep), max(rep, t_rep))
        if pair not in seen:
            seen.add(pair)
            pairs.append(pair)

    qvec = [T333[a[0]][a[1]][a[2]] ^ T333[b[0]][b[1]][b[2]]
            for (a, b) in pairs]
    hw = sum(qvec)
    return qvec, pairs, {
        'quotient_dim': len(pairs),
        'hamming_weight': hw,
        'T333_in_sym3': (hw == 0),
    }


# ─────────────────────────── SAT encoder ─────────────────────────────────────

class SATEncoder:
    """Tseitin-based encoder for GF(2) polynomial constraints."""
    __slots__ = ['nv', 'clauses']

    def __init__(self):
        self.nv = 0
        self.clauses = []

    def new_var(self):
        self.nv += 1
        return self.nv

    def new_vars(self, n):
        return [self.new_var() for _ in range(n)]

    def cl(self, *lits):
        self.clauses.append(lits)

    # ---- gates ----

    def AND2(self, a, b):
        """p ↔ (a ∧ b); returns p.  If a == b, returns a directly."""
        if a == b:
            return a
        p = self.new_var()
        self.cl(-a, -b, p)
        self.cl(a, -p)
        self.cl(b, -p)
        return p

    def AND3(self, a, b, c):
        """p ↔ (a ∧ b ∧ c); handles any pair equality."""
        if a == b:
            return self.AND2(a, c)
        if a == c:
            return self.AND2(a, b)
        if b == c:
            return self.AND2(a, b)
        return self.AND2(self.AND2(a, b), c)

    def XOR2(self, a, b):
        """s ↔ (a ⊕ b); returns s."""
        s = self.new_var()
        self.cl(-a, -b, -s)
        self.cl(a, b, -s)
        self.cl(a, -b, s)
        self.cl(-a, b, s)
        return s

    def assert_xor_eq(self, terms, target):
        """Assert XOR(terms) == target ∈ {0,1}."""
        n = len(terms)
        if n == 0:
            if target:
                self.cl()  # empty clause ⟹ UNSAT
            return
        if n == 1:
            self.cl(terms[0] if target else -terms[0])
            return
        acc = terms[0]
        for t in terms[1:-1]:
            acc = self.XOR2(acc, t)
        last = terms[-1]
        if target == 0:
            self.cl(acc, -last)
            self.cl(-acc, last)
        else:
            self.cl(acc, last)
            self.cl(-acc, -last)

    def add_lex_le(self, a_vars, b_vars):
        """Add clauses: a_vars ≤ b_vars (lexicographic, non-strict).
        Sound for symmetry breaking: selects one sorted representative
        from each permutation class, including degenerate (equal) cases."""
        n = len(a_vars)
        assert len(b_vars) == n
        eq = None
        for j in range(n):
            if eq is None:
                self.cl(-a_vars[j], b_vars[j])  # a[0] ≤ b[0]
            else:
                self.cl(-eq, -a_vars[j], b_vars[j])  # eq_{j-1} → a[j] ≤ b[j]
            if j < n - 1:
                eq_j = self.new_var()
                if eq is None:
                    self.cl(-eq_j, -a_vars[j], b_vars[j])
                    self.cl(-eq_j, a_vars[j], -b_vars[j])
                    self.cl(-a_vars[j], -b_vars[j], eq_j)
                    self.cl(a_vars[j], b_vars[j], eq_j)
                else:
                    self.cl(-eq_j, eq)
                    self.cl(-eq_j, -a_vars[j], b_vars[j])
                    self.cl(-eq_j, a_vars[j], -b_vars[j])
                    self.cl(-eq, -a_vars[j], -b_vars[j], eq_j)
                    self.cl(-eq, a_vars[j], b_vars[j], eq_j)
                eq = eq_j

    def write_dimacs(self, path):
        with open(path, 'w') as f:
            f.write(f'p cnf {self.nv} {len(self.clauses)}\n')
            for c in self.clauses:
                f.write(' '.join(map(str, c)) + ' 0\n')


# ───────────────────────── encoding ──────────────────────────────────────────

def encode_cyclic(f, m, T333, reps, sym_break=True):
    """Encode cyclic-invariant Brent equations for skeleton (f,m) over F_2.
    
    No nonzero constraints are added: zero vectors are permitted,
    so UNSAT excludes all cyclic decompositions fitting in this skeleton
    (including those of lower effective rank).
    
    With sym_break=True, adds lexicographic symmetry breaking:
      - cube ordering: u_0 ≤ u_1 ≤ ... ≤ u_{f-1}
      - orbit ordering: (U_0,V_0,W_0) ≤ (U_1,...) as 27-bit lex
      - within-orbit canonical: U_o ≤ V_o AND U_o ≤ W_o
        (breaks the Z/3 cyclic symmetry of each orbit)
    """
    enc = SATEncoder()
    u = [enc.new_vars(9) for _ in range(f)]
    U = [enc.new_vars(9) for _ in range(m)]
    V = [enc.new_vars(9) for _ in range(m)]
    W = [enc.new_vars(9) for _ in range(m)]

    if sym_break:
        # cube permutation symmetry: S_f
        for s in range(f - 1):
            enc.add_lex_le(u[s], u[s + 1])
        # orbit permutation symmetry: S_m
        for o in range(m - 1):
            enc.add_lex_le(U[o] + V[o] + W[o],
                           U[o + 1] + V[o + 1] + W[o + 1])
        # within-orbit cyclic symmetry: Z/3
        for o in range(m):
            enc.add_lex_le(U[o], V[o])
            enc.add_lex_le(U[o], W[o])

    for (i, j, k) in reps:
        target = T333[i][j][k]
        terms = []

        # cube contributions: u_s[i] · u_s[j] · u_s[k]  (mod 2)
        for s in range(f):
            terms.append(enc.AND3(u[s][i], u[s][j], u[s][k]))

        # orbit contributions
        for o in range(m):
            if i == j == k:
                # All three products identical over F2 (3x = x)
                terms.append(enc.AND3(U[o][i], V[o][i], W[o][i]))
            else:
                p1 = enc.AND3(U[o][i], V[o][j], W[o][k])
                p2 = enc.AND3(V[o][i], W[o][j], U[o][k])
                p3 = enc.AND3(W[o][i], U[o][j], V[o][k])
                terms.append(enc.XOR2(enc.XOR2(p1, p2), p3))

        enc.assert_xor_eq(terms, target)

    return enc, {'u': u, 'U': U, 'V': V, 'W': W}


# ──────────────────────── solver ─────────────────────────────────────────────

def find_solver():
    for name in ['kissat', 'cadical']:
        r = subprocess.run(['which', name], capture_output=True, text=True)
        if r.returncode == 0:
            return name
    return None


def run_sat(cnf, proof=None, timeout=300):
    solver = find_solver()
    if not solver:
        return 'NO_SOLVER', {}, 0.0
    cmd = [solver, str(cnf)]
    if proof:
        cmd.append(str(proof))
    t0 = time.time()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT', {}, time.time() - t0
    dt = time.time() - t0
    if r.returncode == 10:
        assign = {}
        for line in r.stdout.splitlines():
            if line.startswith('v '):
                for tok in line[2:].split():
                    lit = int(tok)
                    if lit == 0:
                        break
                    assign[abs(lit)] = (lit > 0)
        return 'SAT', assign, dt
    elif r.returncode == 20:
        return 'UNSAT', {}, dt
    return 'UNKNOWN', {}, dt


def verify_drat(cnf, proof, timeout=120):
    r = subprocess.run(['which', 'drat-trim'], capture_output=True)
    if r.returncode != 0:
        return 'NO_VERIFIER', 0.0
    t0 = time.time()
    try:
        r = subprocess.run(['drat-trim', str(cnf), str(proof)],
                           capture_output=True, text=True, timeout=timeout)
        out = r.stdout + r.stderr
        if 'VERIFIED' in out:
            return 'VERIFIED', time.time() - t0
        return 'UNVERIFIED', time.time() - t0
    except Exception:
        return 'ERROR', time.time() - t0


# ──────────────────── solution handling ──────────────────────────────────────

def extract_solution(assign, vmap, f, m):
    u_vecs = [[int(assign.get(vmap['u'][s][i], False)) for i in range(9)]
              for s in range(f)]
    orbits = [([int(assign.get(vmap['U'][o][i], False)) for i in range(9)],
               [int(assign.get(vmap['V'][o][i], False)) for i in range(9)],
               [int(assign.get(vmap['W'][o][i], False)) for i in range(9)])
              for o in range(m)]
    return u_vecs, orbits


def verify_brent(u_vecs, orbits, T333):
    """Check all 729 Brent equations.  Return error count."""
    err = 0
    for i in range(9):
        for j in range(9):
            for k in range(9):
                v = 0
                for u in u_vecs:
                    v ^= (u[i] & u[j] & u[k])
                for (U, V, W) in orbits:
                    v ^= (U[i] & V[j] & W[k])
                    v ^= (V[i] & W[j] & U[k])
                    v ^= (W[i] & U[j] & V[k])
                if v != T333[i][j][k]:
                    err += 1
    return err


def rank_info(u_vecs, orbits):
    nz_cubes = [u for u in u_vecs if any(u)]
    nz_orbs = [(U, V, W) for (U, V, W) in orbits
               if any(U) or any(V) or any(W)]
    degen = sum(1 for (U, V, W) in nz_orbs if U == V == W)
    uniq_cubes = len(set(map(tuple, nz_cubes)))
    return {
        'nonzero_cubes': len(nz_cubes),
        'unique_cubes': uniq_cubes,
        'nonzero_orbits': len(nz_orbs),
        'degenerate_orbits_UeqVeqW': degen,
        'skeleton_rank': len(u_vecs) + 3 * len(orbits),
    }


# ────────────────────────── main ─────────────────────────────────────────────

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--timeout', type=int, default=300,
                    help='SAT solver timeout per instance (seconds)')
    ap.add_argument('--no-proof', action='store_true',
                    help='skip DRAT proof generation')
    ap.add_argument('--ranks', default='22,23,27',
                    help='comma-separated target ranks')
    args = ap.parse_args()

    DATA_DIR.mkdir(parents=True, exist_ok=True)

    T333 = build_T333()
    reps = cyclic_orbit_reps()

    # ---- structural checks ----
    n_fixed = sum(1 for r in reps if r[0] == r[1] == r[2])
    n_three = len(reps) - n_fixed
    assert len(reps) == 249 and n_fixed == 9 and n_three == 240

    support = sum(T333[i][j][k]
                  for i in range(9) for j in range(9) for k in range(9))

    for i in range(9):
        for j in range(9):
            for k in range(9):
                assert T333[i][j][k] == T333[j][k][i], \
                    f"T333 not cyclic at {(i,j,k)}"

    qvec, qpairs, qinfo = sym3_quotient(T333, reps)

    print(f"T333 support:  {support}/729")
    print(f"Cyclic orbits: {n_fixed} fixed + {n_three} three-orbits = {len(reps)}")
    print(f"Sym^3 quotient dim={qinfo['quotient_dim']}  "
          f"HW={qinfo['hamming_weight']}  "
          f"T333 in Sym^3={qinfo['T333_in_sym3']}")

    solver = find_solver()
    print(f"Solver: {solver or 'NONE'}\n")

    # ---- build test plan ----
    target_ranks = [int(x) for x in args.ranks.split(',')]
    tests = []
    for r in sorted(set(target_ranks)):
        for f in range(r + 1):
            m_rem = r - f
            if m_rem % 3 == 0:
                m = m_rem // 3
                label = f'rank{r}'
                tests.append((label, f, m, r))

    results = []
    for (label, f, m, r) in tests:
        tag = f"{label}_f{f}_m{m}"
        print(f"{'='*60}")
        print(f"{tag}  rank={r}  vars={9*f+27*m}")

        t0 = time.time()
        enc, vmap = encode_cyclic(f, m, T333, reps)
        t_enc = time.time() - t0

        cnf_path = DATA_DIR / f'{tag}.cnf'
        enc.write_dimacs(str(cnf_path))

        proof_path = None
        if not args.no_proof:
            proof_path = DATA_DIR / f'{tag}.drat'

        print(f"  CNF: {enc.nv} vars  {len(enc.clauses)} clauses  ({t_enc:.2f}s)")

        status, assign, t_sol = run_sat(cnf_path, proof_path, args.timeout)
        print(f"  {status}  ({t_sol:.2f}s)")

        rec = dict(label=label, f=f, m=m, rank=r,
                   primary_vars=9*f+27*m,
                   total_vars=enc.nv, clauses=len(enc.clauses),
                   encode_sec=round(t_enc, 3),
                   status=status, solve_sec=round(t_sol, 3))

        if status == 'SAT':
            u_vecs, orbits = extract_solution(assign, vmap, f, m)
            err = verify_brent(u_vecs, orbits, T333)
            ri = rank_info(u_vecs, orbits)
            rec['brent_errors'] = err
            rec['rank_info'] = ri
            if err == 0:
                rec['u_vecs'] = u_vecs
                rec['orbits'] = [list(o) for o in orbits]
                print(f"  *** VERIFIED: errors=0  {ri} ***")
            else:
                print(f"  SAT but {err} Brent errors!")

        elif status == 'UNSAT' and proof_path and os.path.isfile(str(proof_path)):
            dv, t_dv = verify_drat(cnf_path, proof_path, timeout=300)
            psz = os.path.getsize(str(proof_path))
            rec['drat_status'] = dv
            rec['drat_verify_sec'] = round(t_dv, 3)
            rec['proof_bytes'] = psz
            print(f"  DRAT: {dv}  ({t_dv:.2f}s  {psz} bytes)")

        results.append(rec)

    # ---- summary ----
    print(f"\n{'='*60}")
    print("SUMMARY")
    print(f"{'='*60}")
    for rec in results:
        tag = f"({rec['f']},{rec['m']})"
        extra = ''
        if rec['status'] == 'SAT':
            extra = f"  brent_err={rec.get('brent_errors','?')}"
        elif rec.get('drat_status'):
            extra = f"  drat={rec['drat_status']}"
        print(f"  {rec['label']:8s} {tag:8s} r={rec['rank']:2d}: "
              f"{rec['status']:8s} {rec['solve_sec']:8.2f}s{extra}")

    # count rank-22 exclusions
    r22 = [r for r in results if r['label'] == 'rank22']
    r22_unsat = [r for r in r22 if r['status'] == 'UNSAT']
    r22_sat = [r for r in r22 if r['status'] == 'SAT']
    r22_other = [r for r in r22 if r['status'] not in ('SAT', 'UNSAT')]
    print(f"\nRank-22 skeletons: {len(r22)} total, "
          f"{len(r22_unsat)} UNSAT, {len(r22_sat)} SAT, "
          f"{len(r22_other)} other")
    if len(r22_unsat) == len(r22) and len(r22) > 0:
        print("  ==> ALL rank-22 cyclic skeletons UNSAT over F_2")
        drat_verified = sum(1 for r in r22_unsat
                           if r.get('drat_status') == 'VERIFIED')
        print(f"      DRAT verified: {drat_verified}/{len(r22_unsat)}")

    # ---- save ----
    summary = {
        'sym3_quotient': qinfo,
        'solver': solver,
        'timeout': args.timeout,
        'results': results,
    }
    out = DATA_DIR / 'cyclic_sat_results.json'
    out.write_text(json.dumps(summary, indent=2, default=str) + '\n')
    print(f"\nSaved: {out}")


if __name__ == '__main__':
    main()
