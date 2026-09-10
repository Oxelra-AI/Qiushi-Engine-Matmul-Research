#!/usr/bin/env python3
"""SAT encoder for rank-r decomposition of a tensor over F2.

Encodes the problem: does the 8×9×9 E11 restricted core of T<3,3,3>
have a rank-r decomposition over F2?

If SAT for r=19: R_F2(core_E11) ≤ 19, hence R_F2(T<3,3,3>) ≤ 22.
If UNSAT for r=19: R_F2(core_E11) ≥ 20, hence R_F2(T<3,3,3>) ≥ 21.

Encoding:
  base variables:  u[t][a], v[t][b], w[t][c]  (rank-1 factors)
  pair variables:  p[t][a][b] = u[t][a] AND v[t][b]
  cube variables:  q[t][a][b][c] = p[t][a][b] AND w[t][c]
  XOR chain:       XOR_t q[t][a][b][c] = core[a][b][c]  for each (a,b,c)
"""

import numpy as np
import json, sys, time
from pathlib import Path

def build_matmul_tensor_f2():
    T = np.zeros((9,9,9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T

def apply_constraint_f2(T, mask):
    result = T.copy()
    pivot = mask.bit_length() - 1
    free_bits = mask ^ (1 << pivot)
    for i in range(T.shape[0]):
        if (free_bits >> i) & 1:
            result[i] = (result[i] + result[pivot]) % 2
    result[pivot] = 0
    indices = [j for j in range(T.shape[0]) if j != pivot]
    return result[indices]

class SATEncoder:
    def __init__(self, core, rank):
        self.core = core  # na x nb x nc uint8 array over F2
        self.na, self.nb, self.nc = core.shape
        self.rank = rank
        self.next_var = 1
        self.clauses = []
        self.var_map = {}
        
    def new_var(self):
        v = self.next_var
        self.next_var += 1
        return v
    
    def u_var(self, t, a):
        key = ('u', t, a)
        if key not in self.var_map:
            self.var_map[key] = self.new_var()
        return self.var_map[key]
    
    def v_var(self, t, b):
        key = ('v', t, b)
        if key not in self.var_map:
            self.var_map[key] = self.new_var()
        return self.var_map[key]
    
    def w_var(self, t, c):
        key = ('w', t, c)
        if key not in self.var_map:
            self.var_map[key] = self.new_var()
        return self.var_map[key]
    
    def add_clause(self, lits):
        self.clauses.append(lits)
    
    def encode_and(self, a, b):
        """Encode p = a AND b. Returns p variable."""
        p = self.new_var()
        # p <-> a AND b
        self.add_clause([-a, -b, p])   # a AND b -> p
        self.add_clause([a, -p])       # p -> a
        self.add_clause([b, -p])       # p -> b
        return p
    
    def encode_xor_chain(self, vars_list, target):
        """Encode XOR(vars_list) = target using a binary chain.
        target: 0 or 1."""
        n = len(vars_list)
        if n == 0:
            if target == 1:
                self.add_clause([])  # empty clause = UNSAT
            return
        if n == 1:
            if target == 1:
                self.add_clause([vars_list[0]])
            else:
                self.add_clause([-vars_list[0]])
            return
        
        # Chain: z[0] = v[0] XOR v[1]
        #        z[i] = z[i-1] XOR v[i+1]
        #        z[n-2] = target
        prev = vars_list[0]
        for i in range(1, n):
            curr = vars_list[i]
            if i < n - 1:
                z = self.new_var()
                # z = prev XOR curr
                self.add_clause([-prev, -curr, -z])
                self.add_clause([prev, curr, -z])
                self.add_clause([prev, -curr, z])
                self.add_clause([-prev, curr, z])
                prev = z
            else:
                # Final ARTIFACT: prev XOR curr = target
                if target == 1:
                    self.add_clause([-prev, -curr])
                    self.add_clause([prev, curr])
                else:
                    self.add_clause([-prev, curr])
                    self.add_clause([prev, -curr])
    
    def encode(self):
        """Build the full SAT encoding."""
        r = self.rank
        
        # Allocate all base variables
        for t in range(r):
            for a in range(self.na):
                self.u_var(t, a)
            for b in range(self.nb):
                self.v_var(t, b)
            for c in range(self.nc):
                self.w_var(t, c)
        
        print(f"Base variables: {self.next_var - 1}")
        
        # Build pair variables: p[t][a][b] = u[t][a] AND v[t][b]
        pair_vars = {}
        for t in range(r):
            for a in range(self.na):
                for b in range(self.nb):
                    pair_vars[(t, a, b)] = self.encode_and(
                        self.u_var(t, a), self.v_var(t, b))
        
        print(f"After pairs: {self.next_var - 1} vars, {len(self.clauses)} clauses")
        
        # For each Brent equation, build cube variables and XOR constraint
        for a in range(self.na):
            for b in range(self.nb):
                for c in range(self.nc):
                    target = int(self.core[a, b, c])
                    # Build cube variables for each term
                    cube_vars = []
                    for t in range(r):
                        q = self.encode_and(pair_vars[(t, a, b)],
                                          self.w_var(t, c))
                        cube_vars.append(q)
                    # XOR chain
                    self.encode_xor_chain(cube_vars, target)
        
        print(f"After cubes+XOR: {self.next_var - 1} vars, {len(self.clauses)} clauses")
        
        # Optional: symmetry breaking - order first few u-vectors
        # lexicographically by their binary representation
        # u[0] < u[1] (in binary value, with bit 0 = MSB)
        # This uses a simple lexicographic comparator
        self._add_lex_order(0, 1)
        
        print(f"After symmetry break: {self.next_var - 1} vars, {len(self.clauses)} clauses")
    
    def _add_lex_order(self, t1, t2):
        """Add constraint u[t1] <_lex u[t2] (strict, binary value)."""
        # u[t1][0..na-1] < u[t2][0..na-1] lexicographically
        # Encoding: there exists a position k such that:
        #   u[t1][j] = u[t2][j] for j < k
        #   u[t1][k] = 0, u[t2][k] = 1
        # We use a chain of "equal up to here" auxiliary variables
        na = self.na
        eq = []  # eq[j] = (u[t1][0..j] == u[t2][0..j])
        for j in range(na):
            e = self.new_var()
            u1 = self.u_var(t1, j)
            u2 = self.u_var(t2, j)
            # e <-> (u1 == u2) AND (prev_eq or j==0)
            # Simplified: just enforce that at the first difference, t1 < t2
            eq.append(e)
        
        # Alternative simpler encoding: just require u[t1] ≤ u[t2] in binary
        # This is sufficient for symmetry breaking between any two terms
        # Use the standard lex comparator
        # prev = True (all equal so far)
        # For each bit j from MSB to LSB:
        #   if u[t1][j]=0, u[t2][j]=1 -> definitely <, done
        #   if u[t1][j]=1, u[t2][j]=0 -> definitely >, forbidden (add clause)
        #   if equal -> continue
        # Encoding with auxiliary "decided" variables
        prev_undecided = None  # None means "not yet decided, all equal so far"
        for j in range(na):
            u1 = self.u_var(t1, j)
            u2 = self.u_var(t2, j)
            # "undecided_j" means all bits 0..j are equal
            undecided = self.new_var()
            
            if j == 0:
                # undecided_0 <-> (u1 == u2)
                # u1=0,u2=0: undecided=1
                # u1=1,u2=1: undecided=1
                # u1=0,u2=1: undecided=0, and this is fine (t1 < t2)
                # u1=1,u2=0: undecided=0, and this is BAD
                # Forbid u1=1,u2=0 when still deciding
                self.add_clause([-u1, u2])  # at position 0: u1 <= u2
                # undecided <-> (u1 XNOR u2)
                self.add_clause([-u1, -u2, undecided])
                self.add_clause([u1, u2, undecided])
                self.add_clause([u1, -u2, -undecided])
                self.add_clause([-u1, u2, -undecided])
            else:
                # If prev_undecided and u1=1 and u2=0: forbidden
                self.add_clause([-prev_undecided, -u1, u2])
                # undecided <-> prev_undecided AND (u1 XNOR u2)
                xnor = self.new_var()
                self.add_clause([-u1, -u2, xnor])
                self.add_clause([u1, u2, xnor])
                self.add_clause([u1, -u2, -xnor])
                self.add_clause([-u1, u2, -xnor])
                # undecided <-> prev_undecided AND xnor
                self.add_clause([-prev_undecided, -xnor, undecided])
                self.add_clause([prev_undecided, -undecided])
                self.add_clause([xnor, -undecided])
            
            prev_undecided = undecided
        
        # After all bits: if still undecided, they're equal.
        # For strict <, forbid equality: add clause [-prev_undecided]
        self.add_clause([-prev_undecided])
    
    def write_dimacs(self, path):
        nvars = self.next_var - 1
        nclauses = len(self.clauses)
        with open(path, 'w') as f:
            f.write(f'c Rank-{self.rank} decomposition of {self.na}x{self.nb}x{self.nc} tensor over F2\n')
            f.write(f'c Generated by research_record analysis\n')
            f.write(f'p cnf {nvars} {nclauses}\n')
            for cl in self.clauses:
                f.write(' '.join(map(str, cl)) + ' 0\n')
        return nvars, nclauses

def main():
    outdir = Path('data/restricted_cores')
    
    # Build E11 core
    T = build_matmul_tensor_f2()
    core_e11 = apply_constraint_f2(T, 1)  # mask=1, E11
    print(f"E11 core: shape {core_e11.shape}, nnz {np.sum(core_e11)}")
    
    # Target ranks to test
    for target_rank in [19, 20]:
        print(f"\n{'='*60}")
        print(f"Encoding rank-{target_rank} decomposition of E11 core (8x9x9)")
        print(f"{'='*60}")
        
        enc = SATEncoder(core_e11, target_rank)
        enc.encode()
        
        cnf_path = outdir / f'core_e11_rank{target_rank}.cnf'
        nvars, nclauses = enc.write_dimacs(cnf_path)
        print(f"Written: {cnf_path}")
        print(f"Variables: {nvars}, Clauses: {nclauses}")
        print(f"File size: {cnf_path.stat().st_size} bytes")
    
    # Also write a layout/metadata file
    meta = {
        'core': 'E11',
        'mask': 1,
        'core_shape': [8, 9, 9],
        'core_nnz': int(np.sum(core_e11)),
        'encodings': {},
    }
    for r in [19, 20]:
        cnf_path = outdir / f'core_e11_rank{r}.cnf'
        meta['encodings'][f'rank_{r}'] = {
            'file': str(cnf_path),
            'rank': r,
            'base_vars': r * (8 + 9 + 9),
            'total_brent_eqs': 8 * 9 * 9,
            'nonzero_eqs': int(np.sum(core_e11)),
            'zero_eqs': 8*9*9 - int(np.sum(core_e11)),
        }
    with open(outdir / 'sat_encoding_meta.json', 'w') as f:
        json.dump(meta, f, indent=2)
    
    print(f"\nMetadata saved to {outdir}/sat_encoding_meta.json")
    print(f"\nTo solve: cadical {outdir}/core_e11_rank19.cnf")

if __name__ == '__main__':
    main()
