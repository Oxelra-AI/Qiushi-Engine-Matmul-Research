#!/usr/bin/env python3
"""Build F_2 SAT encoding for rank of M_<3,3,2> and test with CaDiCaL.

M_<3,3,2> is 9x6x6 with 18 nonzero entries.
A rank-r decomposition has r terms, each u_i(9 bits) x v_i(6 bits) x w_i(6 bits).
The Brent equations are: for each nonzero (a,b,c), sum_i u_i[a]*v_i[b]*w_i[c] = 1 mod 2
                         for each zero (a,b,c),    sum_i u_i[a]*v_i[b]*w_i[c] = 0 mod 2
Total: 9*6*6 = 324 equations, each a degree-3 XOR over r terms.
Variables: r*(9+6+6) = 21r.
"""
import numpy as np
from pathlib import Path
import subprocess, time

def make_M332():
    T = np.zeros((9, 6, 6), dtype=int)
    for i in range(3):
        for j in range(3):
            for k in range(2):
                a = 3*i + j
                b = 2*j + k
                c = 2*i + k
                T[a, b, c] = 1
    return T

def build_cnf(T, rank, out_path):
    """Build CNF for rank-r decomposition of T over F_2."""
    d1, d2, d3 = T.shape
    r = rank
    
    # Variables: u_i[a] for i=0..r-1, a=0..d1-1  => r*d1 vars
    #           v_i[b] for i=0..r-1, b=0..d2-1  => r*d2 vars
    #           w_i[c] for i=0..r-1, c=0..d3-1  => r*d3 vars
    # Plus auxiliary vars for XOR encoding.
    
    n_base = r * (d1 + d2 + d3)
    
    def u_var(i, a): return i*d1 + a + 1
    def v_var(i, b): return r*d1 + i*d2 + b + 1
    def w_var(i, c): return r*d1 + r*d2 + i*d3 + c + 1
    
    # For each equation (a,b,c): XOR_{i=0}^{r-1} (u_i[a] AND v_i[b] AND w_i[c]) = T[a,b,c]
    # Each product p_i = u_i[a] AND v_i[b] AND w_i[c] needs an auxiliary variable.
    
    clauses = []
    next_var = n_base + 1
    
    for a in range(d1):
        for b in range(d2):
            for c in range(d3):
                target = T[a, b, c]
                
                # Create product variables p_i = u_i[a] AND v_i[b] AND w_i[c]
                p_vars = []
                for i in range(r):
                    p = next_var; next_var += 1
                    p_vars.append(p)
                    ua = u_var(i, a)
                    vb = v_var(i, b)
                    wc = w_var(i, c)
                    
                    # p <=> ua AND vb AND wc
                    # Tseitin: p => ua, p => vb, p => wc, ua AND vb AND wc => p
                    clauses.append([-p, ua])
                    clauses.append([-p, vb])
                    clauses.append([-p, wc])
                    clauses.append([p, -ua, -vb, -wc])
                
                # XOR of p_vars = target
                # Encode as: p_1 XOR p_2 XOR ... XOR p_r = target
                # Use chain of auxiliary XOR variables
                if r == 0:
                    if target == 1:
                        clauses.append([])  # empty clause = UNSAT
                    continue
                
                if r == 1:
                    if target == 1:
                        clauses.append([p_vars[0]])
                    else:
                        clauses.append([-p_vars[0]])
                    continue
                
                # Chain: s_1 = p_1 XOR p_2, s_2 = s_1 XOR p_3, ..., s_{r-1} = T[a,b,c]
                chain = []
                for k in range(r - 1):
                    if k < r - 2:
                        s = next_var; next_var += 1
                        chain.append(s)
                    # else: the last "s" is determined by target
                
                prev = p_vars[0]
                for k in range(1, r):
                    cur = p_vars[k]
                    if k < r - 1:
                        s = chain[k-1]
                        # s <=> prev XOR cur
                        clauses.append([-s, -prev, -cur])
                        clauses.append([-s, prev, cur])
                        clauses.append([s, -prev, cur])
                        clauses.append([s, prev, -cur])
                        prev = s
                    else:
                        # prev XOR cur = target
                        if target == 1:
                            # prev XOR cur = 1: exactly one true
                            clauses.append([prev, cur])
                            clauses.append([-prev, -cur])
                        else:
                            # prev XOR cur = 0: same value
                            clauses.append([prev, -cur])
                            clauses.append([-prev, cur])
    
    n_vars = next_var - 1
    
    with open(out_path, 'w') as f:
        f.write(f'p cnf {n_vars} {len(clauses)}\n')
        for cl in clauses:
            f.write(' '.join(str(x) for x in cl) + ' 0\n')
    
    return n_vars, len(clauses)

def main():
    T = make_M332()
    print(f'M_<3,3,2>: shape={T.shape}, nnz={np.count_nonzero(T)}')
    
    # Verify
    for i in range(3):
        for j in range(3):
            for k in range(2):
                assert T[3*i+j, 2*j+k, 2*i+k] == 1
    print('Tensor verified')
    
    script_dir = Path(__file__).resolve().parent
    out_dir = script_dir.parent / 'data' / 'blaser_verification'
    out_dir.mkdir(parents=True, exist_ok=True)
    
    results = {'tensor': 'M_<3,3,2>', 'dims': [9,6,6], 'nnz': 18, 'field': 2}
    
    # Test ranks 13, 14, 15
    for rank in [14, 15, 13, 12]:
        cnf_path = out_dir / f'M332_rank{rank}.cnf'
        nv, nc = build_cnf(T, rank, cnf_path)
        print(f'\nRank {rank}: {nv} vars, {nc} clauses')
        
        for solver, timeout in [('cadical', 300), ('kissat', 300)]:
            t0 = time.time()
            try:
                proc = subprocess.run(
                    [solver, str(cnf_path)],
                    capture_output=True, text=True, timeout=timeout
                )
                elapsed = time.time() - t0
                
                if proc.returncode == 10:
                    status = 'SAT'
                elif proc.returncode == 20:
                    status = 'UNSAT'
                else:
                    status = 'UNKNOWN'
                
                print(f'  {solver}: {status} ({elapsed:.1f}s)')
                results[f'rank{rank}_{solver}'] = {
                    'status': status, 'time': round(elapsed, 2),
                    'returncode': proc.returncode
                }
                
                if status == 'SAT':
                    # No need to try other solvers
                    break
                    
            except subprocess.TimeoutExpired:
                elapsed = timeout
                print(f'  {solver}: TIMEOUT ({timeout}s)')
                results[f'rank{rank}_{solver}'] = {'status': 'TIMEOUT', 'time': timeout}
    
    out_path = out_dir / 'M332_sat_results.json'
    out_path.write_text(json.dumps(results, indent=2) + '\n')
    print(f'\nSaved to {out_path}')

if __name__ == '__main__':
    main()
