#!/usr/bin/env python3
"""
analysis: Search for a cyclic rank-23 F_2 decomposition with skeleton (11,4).

Adapts the analysis cyclic SAT encoder for arbitrary rank.
A cyclic decomposition with (f,m) at total rank f+3m has:
  - f fixed cubes: u_i ⊗ u_i ⊗ u_i  (9 Boolean bits each)
  - m free 3-orbits: (U_j, V_j, W_j) + cyclic  (27 Boolean bits each)

All 249 cyclic Brent equations over F_2.
"""
from __future__ import annotations
import numpy as np, itertools, time, subprocess, json, os
from pathlib import Path

WS = Path(__file__).resolve().parent.parent
OUT = WS / 'data' / 'cyclic_r23'
OUT.mkdir(parents=True, exist_ok=True)

def build_T333_bool():
    """Build T_{3,3,3} as length-729 F_2 vector (flattened 9x9x9)."""
    T = [0]*729
    for a in range(3):
        for b in range(3):
            for c in range(3):
                for d in range(3):
                    for e in range(3):
                        for f_idx in range(3):
                            if b==c and d==e and f_idx==a:
                                idx = (3*a+b)*81 + (3*c+d)*9 + (3*e+f_idx)
                                T[idx] = 1
    return T

def build_cyclic_invariant_equations(T):
    """
    Build the 249 cyclic-invariant Brent equations.
    Cyclic invariant subspace has coordinates indexed by orbits under cyclic permutation 
    of (i,j,k) -> (j,k,i) on [0,8]^3 positions.
    """
    orbits = {}
    orbit_list = []
    for i in range(9):
        for j in range(9):
            for k in range(9):
                key = tuple(sorted([(i,j,k), (j,k,i), (k,i,j)]))
                if key not in orbits:
                    orbits[key] = len(orbit_list)
                    orbit_list.append((i,j,k))  # representative
    
    # T projected onto cyclic invariant subspace
    T_cyc = [0]*len(orbit_list)
    for idx_o, (i,j,k) in enumerate(orbit_list):
        key = tuple(sorted([(i,j,k), (j,k,i), (k,i,j)]))
        vals = []
        for (a,b,c) in [(i,j,k), (j,k,i), (k,i,j)]:
            vals.append(T[a*81+b*9+c])
        # In cyclic invariant subspace, coordinate = sum of orbit elements (mod 2 for F2)
        T_cyc[idx_o] = sum(vals) % 2
    
    return orbit_list, T_cyc

def encode_cyclic_rank_r(f, m, cnf_path, use_xor=True):
    """
    Encode cyclic Brent equations for (f,m) skeleton over F_2.
    Total rank = f + 3m.
    
    Variables:
    - cube_i_a: 9 bits per cube (i=0..f-1, a=0..8)
    - orbit_j_U_a, orbit_j_V_a, orbit_j_W_a: 27 bits per orbit (j=0..m-1, a=0..8)
    
    Each Brent equation (for cyclic orbit (p,q,r)):
    sum_cubes cube_i_p * cube_i_q * cube_i_r 
    + sum_orbits (U_j_p*V_j_q*W_j_r + V_j_p*W_j_q*U_j_r + W_j_p*U_j_q*V_j_r)
    = T_cyc[orbit_idx]  (mod 2)
    """
    T = build_T333_bool()
    orbit_list, T_cyc = build_cyclic_invariant_equations(T)
    n_eq = len(orbit_list)
    
    # Variable numbering
    next_var = 1
    cube_vars = {}  # (i, a) -> var
    for i in range(f):
        for a in range(9):
            cube_vars[(i, a)] = next_var
            next_var += 1
    
    orbit_vars = {}  # (j, factor, a) -> var  (factor: 0=U, 1=V, 2=W)
    for j in range(m):
        for fac in range(3):
            for a in range(9):
                orbit_vars[(j, fac, a)] = next_var
                next_var += 1
    
    n_primary = next_var - 1
    
    # For each equation, we need to express:
    # XOR of products = target (mod 2)
    
    clauses = []
    xor_clauses = []
    and_cache = {}
    
    def get_and(v1, v2):
        key = (min(v1,v2), max(v1,v2))
        if key in and_cache:
            return and_cache[key]
        nonlocal next_var
        out = next_var
        next_var += 1
        clauses.append([-out, v1])
        clauses.append([-out, v2])
        clauses.append([out, -v1, -v2])
        and_cache[key] = out
        return out
    
    def get_and3(v1, v2, v3):
        ab = get_and(v1, v2)
        return get_and(ab, v3)
    
    for eq_idx, (p, q, r) in enumerate(orbit_list):
        target = T_cyc[eq_idx]
        
        # Collect all product variables for this equation
        products = []
        
        # Cube contributions: cube_i_p * cube_i_q * cube_i_r
        for i in range(f):
            pv = cube_vars[(i, p)]
            qv = cube_vars[(i, q)]
            rv = cube_vars[(i, r)]
            if p == q == r:
                products.append(pv)  # x^3 = x over F_2
            elif p == q:
                products.append(get_and(pv, rv))  # x^2 * y = x*y
            elif q == r:
                products.append(get_and(pv, qv))
            elif p == r:
                products.append(get_and(qv, pv))
            else:
                products.append(get_and3(pv, qv, rv))
        
        # Orbit contributions: for each orbit j,
        # U_j_p*V_j_q*W_j_r + V_j_p*W_j_q*U_j_r + W_j_p*U_j_q*V_j_r
        for j in range(m):
            for (fa, fb, fc) in [(0,1,2), (1,2,0), (2,0,1)]:
                va = orbit_vars[(j, fa, p)]
                vb = orbit_vars[(j, fb, q)]
                vc = orbit_vars[(j, fc, r)]
                if p == q == r:
                    products.append(get_and3(va, vb, vc))
                elif p == q:
                    products.append(get_and3(va, vb, vc))
                elif q == r:
                    products.append(get_and3(va, vb, vc))
                elif p == r:
                    products.append(get_and3(va, vb, vc))
                else:
                    products.append(get_and3(va, vb, vc))
        
        if use_xor:
            xor_clauses.append((products, target))
        else:
            # Tseitin XOR chain
            raise NotImplementedError("Tseitin encoding not implemented here")
    
    # Symmetry breaking: lexicographic ordering on cubes and orbits
    # cube_0 < cube_1 < ... < cube_{f-1} (as 9-bit integers)
    for i in range(f - 1):
        for a in range(9):
            v_curr = cube_vars[(i, a)]
            v_next = cube_vars[(i+1, a)]
            # Lex: if all higher bits equal, current bit <= next bit
            # Simple: just add v_curr <= v_next for first differing bit
            # Actually, just add v_curr -> v_next for each bit (weak but sound)
            pass  # Skip for now, rely on solver
    
    # Write CNF with XOR
    n_vars = next_var - 1
    with open(cnf_path, 'w') as fp:
        fp.write(f'p cnf {n_vars} {len(clauses)}\n')
        for cl in clauses:
            fp.write(' '.join(str(l) for l in cl) + ' 0\n')
        for prods, tgt in xor_clauses:
            parity = 'x' if tgt else 'x-'
            line = parity + ' '.join(str(v) for v in prods) + ' 0\n'
            fp.write(line)
    
    return {
        'n_vars': n_vars,
        'n_primary': n_primary,
        'n_clauses': len(clauses),
        'n_xor': len(xor_clauses),
        'cube_vars': cube_vars,
        'orbit_vars': orbit_vars,
        'orbit_list': orbit_list,
        'T_cyc': T_cyc,
    }

def decode_solution(vals, info, f, m):
    """Decode SAT solution into cube and orbit vectors."""
    cubes = []
    for i in range(f):
        vec = []
        for a in range(9):
            v = info['cube_vars'][(i, a)]
            vec.append(1 if vals[v] else 0)
        cubes.append(vec)
    
    orbits = []
    for j in range(m):
        uvw = []
        for fac in range(3):
            vec = []
            for a in range(9):
                v = info['orbit_vars'][(j, fac, a)]
                vec.append(1 if vals[v] else 0)
            uvw.append(vec)
        orbits.append(uvw)
    
    return cubes, orbits

def verify_cyclic_decomp(cubes, orbits):
    """Verify that the cyclic decomposition satisfies all 729 Brent equations over F_2."""
    T = build_T333_bool()
    
    # Reconstruct: T_recon[i,j,k] = sum cubes + sum orbit terms
    T_recon = [0]*729
    
    for cube in cubes:
        for i in range(9):
            for j in range(9):
                for k in range(9):
                    T_recon[i*81+j*9+k] ^= (cube[i] & cube[j] & cube[k])
    
    for orb in orbits:
        U, V, W = orb
        for perm in [(U,V,W), (V,W,U), (W,U,V)]:
            a, b, c = perm
            for i in range(9):
                for j in range(9):
                    for k in range(9):
                        T_recon[i*81+j*9+k] ^= (a[i] & b[j] & c[k])
    
    errors = sum(1 for i in range(729) if T_recon[i] != T[i])
    return errors

def main():
    print("="*70)
    print("analysis: Finding cyclic rank-23 F_2 decomposition with (f,m)=(11,4)")
    print("="*70)
    
    f, m = 11, 4
    total_rank = f + 3*m
    print(f"Skeleton: (f,m) = ({f},{m}), total rank = {total_rank}")
    
    cnf_path = str(OUT / f'cyclic_r{total_rank}_f{f}_m{m}.cnf')
    
    t0 = time.time()
    info = encode_cyclic_rank_r(f, m, cnf_path)
    t_encode = time.time() - t0
    
    print(f"Encoding: {info['n_vars']} vars, {info['n_clauses']} clauses, {info['n_xor']} XOR ({t_encode:.2f}s)")
    print(f"Primary vars: {info['n_primary']} ({f*9} cube + {m*27} orbit)")
    
    # Run CryptoMiniSat
    solver = '/usr/bin/cryptominisat5'
    cmd = [solver, '--verb', '0', '--maxtime', '300', cnf_path]
    print(f"\nRunning CMS on rank-{total_rank} ({f},{m})...")
    t0 = time.time()
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=360)
    t_solve = time.time() - t0
    
    if proc.returncode == 10:
        print(f"SAT! ({t_solve:.1f}s)")
        
        # Parse solution
        vals = {}
        for line in proc.stdout.split('\n'):
            if line.startswith('v '):
                for tok in line[2:].split():
                    lit = int(tok)
                    if lit != 0:
                        vals[abs(lit)] = (lit > 0)
        
        cubes, orbits = decode_solution(vals, info, f, m)
        
        # Verify
        errors = verify_cyclic_decomp(cubes, orbits)
        print(f"Brent verification: {errors}/729 errors")
        
        if errors == 0:
            print("\nVERIFIED cyclic rank-23 (11,4) decomposition!")
            
            # Count nonzero cubes and orbits
            nz_cubes = sum(1 for c in cubes if any(c))
            nz_orbits = sum(1 for o in orbits if any(any(v) for v in o))
            print(f"Nonzero cubes: {nz_cubes}/{f}")
            print(f"Nonzero orbits: {nz_orbits}/{m}")
            
            # Save
            result = {
                'f': f, 'm': m, 'rank': total_rank,
                'field': 'F_2',
                'brent_errors': errors,
                'solve_sec': t_solve,
                'cubes': cubes,
                'orbits': [{'U': o[0], 'V': o[1], 'W': o[2]} for o in orbits],
                'nonzero_cubes': nz_cubes,
                'nonzero_orbits': nz_orbits,
            }
            out = OUT / f'cyclic_r{total_rank}_f{f}_m{m}_solution.json'
            out.write_text(json.dumps(result, indent=2) + '\n')
            print(f"Saved {out}")
        else:
            print(f"FAILED verification: {errors} errors")
    
    elif proc.returncode == 20:
        print(f"UNSAT ({t_solve:.1f}s)")
    else:
        print(f"TIMEOUT or error ({t_solve:.1f}s, rc={proc.returncode})")

if __name__ == '__main__':
    main()
