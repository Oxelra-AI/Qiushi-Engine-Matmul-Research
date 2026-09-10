#!/usr/bin/env python3
"""analysis: Compact CryptoMiniSat5 SAT encoding for R_F2(M_<3,3,2>) >= 14.

Tests rank-13 decomposability of M_<3,3,2> over F_2.
UNSAT => R_F2(M_<3,3,2>) >= 14 (F2 lower bound, not char-zero).
SAT   => rank <= 13 over F2 (would mean F2 and char-zero ranks differ for this tensor).

Encoding: compact 2-level AND + native XOR for CryptoMiniSat5.
  q_{s,a,b} = u_{s,a} AND v_{s,b}  (auxiliary)
  p_{s,a,b,c} = q_{s,a,b} AND w_{s,c}  (auxiliary)
  XOR_s p_{s,a,b,c} = T[a,b,c]  (native XOR clause)
"""
import numpy as np
from pathlib import Path
import subprocess, time

WS = Path(__file__).resolve().parent.parent
OUT = WS / 'data' / 'M332_sat'
OUT.mkdir(parents=True, exist_ok=True)

def build_M332_F2():
    T = np.zeros((9, 6, 6), dtype=int)
    for i in range(3):
        for j in range(3):
            for k in range(2):
                T[3*i+j, 2*j+k, 2*i+k] = 1
    return T

def encode_rank_r(T, r, out_path):
    """Generate CryptoMiniSat5 CNF with native XOR for rank-r test of T over F2."""
    da, db, dc = T.shape  # 9, 6, 6
    
    # Variable numbering (1-indexed for DIMACS)
    var_count = 0
    def new_var():
        nonlocal var_count
        var_count += 1
        return var_count
    
    # Primary variables
    u = {}  # u[s,a] -> var
    v = {}  # v[s,b] -> var
    w = {}  # w[s,c] -> var
    for s in range(r):
        for a in range(da):
            u[s,a] = new_var()
        for b in range(db):
            v[s,b] = new_var()
        for c in range(dc):
            w[s,c] = new_var()
    
    # q[s,a,b] = u[s,a] AND v[s,b]
    q = {}
    for s in range(r):
        for a in range(da):
            for b in range(db):
                q[s,a,b] = new_var()
    
    # p[s,a,b,c] = q[s,a,b] AND w[s,c]
    p = {}
    for s in range(r):
        for a in range(da):
            for b in range(db):
                for c in range(dc):
                    p[s,a,b,c] = new_var()
    
    n_primary = r * (da + db + dc)
    n_q = r * da * db
    n_p = r * da * db * dc
    n_vars = var_count
    
    clauses = []
    xor_clauses = []
    
    # AND clauses for q[s,a,b] = u[s,a] AND v[s,b]
    # Tseitin: q -> u, q -> v, u AND v -> q
    for s in range(r):
        for a in range(da):
            for b in range(db):
                qv = q[s,a,b]; uv = u[s,a]; vv = v[s,b]
                clauses.append([-qv, uv])      # q -> u
                clauses.append([-qv, vv])      # q -> v  
                clauses.append([uv, vv, -qv])  # Can be removed for tighter encoding
                clauses.append([-uv, -vv, qv]) # u AND v -> q
    
    # AND clauses for p[s,a,b,c] = q[s,a,b] AND w[s,c]
    for s in range(r):
        for a in range(da):
            for b in range(db):
                for c in range(dc):
                    pv = p[s,a,b,c]; qv = q[s,a,b]; wv = w[s,c]
                    clauses.append([-pv, qv])       # p -> q
                    clauses.append([-pv, wv])       # p -> w
                    clauses.append([-qv, -wv, pv])  # q AND w -> p
    
    # XOR constraints: XOR_s p[s,a,b,c] = T[a,b,c]
    for a in range(da):
        for b in range(db):
            for c in range(dc):
                target = int(T[a, b, c])
                pvars = [p[s, a, b, c] for s in range(r)]
                xor_clauses.append((pvars, target))
    
    # Write CryptoMiniSat5 format
    n_and_clauses = len(clauses)
    n_xor = len(xor_clauses)
    
    with open(out_path, 'w') as f:
        f.write(f'p cnf {n_vars} {n_and_clauses + n_xor}\n')
        # AND clauses
        for cl in clauses:
            f.write(' '.join(map(str, cl)) + ' 0\n')
        # XOR clauses (CryptoMiniSat format: x var1 var2 ... 0 for XOR=1, or negated)
        for pvars, target in xor_clauses:
            if target == 1:
                # x v1 v2 ... 0 means v1 XOR v2 XOR ... = 1
                f.write('x ' + ' '.join(map(str, pvars)) + ' 0\n')
            else:
                # x -v1 v2 ... 0 means NOT(v1) XOR v2 XOR ... = 1
                # which is v1 XOR v2 XOR ... = 0
                neg_first = [-pvars[0]] + pvars[1:]
                f.write('x ' + ' '.join(map(str, neg_first)) + ' 0\n')
    
    return n_vars, n_and_clauses, n_xor

def main():
    T = build_M332_F2()
    nnz = np.count_nonzero(T)
    print(f"M_<3,3,2> over F2: shape={T.shape}, nnz={nnz}")
    
    for target_rank in [13, 12, 11]:
        print(f"\n=== Testing rank {target_rank} ===")
        cnf_path = OUT / f'M332_rank{target_rank}.cnf'
        nv, nc, nx = encode_rank_r(T, target_rank, cnf_path)
        print(f"  Variables: {nv}, AND clauses: {nc}, XOR clauses: {nx}")
        
        # Run CryptoMiniSat5
        t0 = time.time()
        try:
            result = subprocess.run(
                ['cryptominisat5', '--verb', '0', '--maxtime', '300', str(cnf_path)],
                capture_output=True, text=True, timeout=360
            )
            elapsed = time.time() - t0
            
            if result.returncode == 10:
                print(f"  SAT in {elapsed:.1f}s -> R_F2(M_<3,3,2>) <= {target_rank}")
                # Parse solution
                for line in result.stdout.split('\n'):
                    if line.startswith('v '):
                        print(f"  Solution found (first 50 vars): {line[:200]}")
                        break
            elif result.returncode == 20:
                print(f"  UNSAT in {elapsed:.1f}s -> R_F2(M_<3,3,2>) >= {target_rank+1}")
            else:
                print(f"  UNKNOWN (exit {result.returncode}) in {elapsed:.1f}s")
                if result.stderr:
                    print(f"  stderr: {result.stderr[:200]}")
                    
        except subprocess.TimeoutExpired:
            print(f"  Timeout (300s)")
        except FileNotFoundError:
            print(f"  cryptominisat5 not found, trying kissat...")
            # Kissat doesn't support native XOR, skip
            
    # Also test rank 14 (should be SAT since R_Q >= 14 doesn't imply R_F2 >= 14)
    # and rank 6 (definitely SAT)
    for target_rank in [6]:
        print(f"\n=== Positive control: rank {target_rank} ===")
        cnf_path = OUT / f'M332_rank{target_rank}.cnf'
        nv, nc, nx = encode_rank_r(T, target_rank, cnf_path)
        t0 = time.time()
        try:
            result = subprocess.run(
                ['cryptominisat5', '--verb', '0', '--maxtime', '60', str(cnf_path)],
                capture_output=True, text=True, timeout=120
            )
            elapsed = time.time() - t0
            if result.returncode == 10:
                print(f"  SAT in {elapsed:.1f}s (expected: positive control)")
            else:
                print(f"  Exit {result.returncode} in {elapsed:.1f}s")
        except (subprocess.TimeoutExpired, FileNotFoundError) as e:
            print(f"  Error: {e}")

    print(f"\nResults saved to {OUT}")

if __name__ == '__main__':
    main()
