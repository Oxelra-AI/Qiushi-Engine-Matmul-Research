#!/usr/bin/env python3
"""Quick test: SAT-test the greedy multiset as fixed-U with free B/C."""
import subprocess, json, tempfile, time, sys
from pathlib import Path
import numpy as np

# The greedy 19 vectors from cap1 structure analysis
greedy = [1, 2, 3, 4, 8, 9, 12, 13, 16, 18, 20, 22, 24, 27, 28, 31, 32, 36, 42]

# Load core tensor
core = np.load("data/restricted_cores/mask_001_E11_core.npy")
nU, nV, nW = core.shape
print(f"E11 core shape: {core.shape}")
print(f"Testing greedy A-multiset: {greedy} (support={len(greedy)})")

# The core uses 8-bit A-factors representing the quotient F2^8
# Each A-factor is a bit vector indexing the 8 A-coordinates
rank = len(greedy)

# Build SAT encoding: fix A-factors, variables are B and C factors
# For each term t: B_t is 9-bit, C_t is 9-bit
# Brent equation: for each (a,b,c), sum_t A_t[a]*B_t[b]*C_t[c] = T[a,b,c] mod 2

# Variables: p_{t,b,c} = B_t[b] * C_t[c] for each t,b,c
# But we use separate B and C variables
# v_t_b for B_t[b], w_t_c for C_t[c]
# p_t_bc = v_t_b AND w_t_c (Tseytin encoding)

nvar = 0
var_v = {}  # var_v[(t,b)] = variable number for B_t[b]
var_w = {}  # var_w[(t,c)] = variable number for C_t[c]

for t in range(rank):
    for b in range(nV):
        nvar += 1
        var_v[(t,b)] = nvar
    for c in range(nW):
        nvar += 1
        var_w[(t,c)] = nvar

# Tseytin variables for products
var_p = {}
for t in range(rank):
    for b in range(nV):
        for c in range(nW):
            nvar += 1
            var_p[(t,b,c)] = nvar

clauses = []

# Tseytin: p = v AND w
for t in range(rank):
    for b in range(nV):
        for c in range(nW):
            p = var_p[(t,b,c)]
            v = var_v[(t,b)]
            w = var_w[(t,c)]
            # p => v, p => w, (v AND w) => p
            clauses.append([-p, v])
            clauses.append([-p, w])
            clauses.append([p, -v, -w])

# Brent equations: for each (a,b,c), XOR over active terms = T[a,b,c]
for a in range(nU):
    for b in range(nV):
        for c in range(nW):
            target = int(core[a, b, c])
            # Active terms: those with A_t[a] = 1
            active_products = []
            for t in range(rank):
                u_val = greedy[t]
                if (u_val >> a) & 1:
                    active_products.append(var_p[(t,b,c)])
            # XOR constraint: sum of active products = target mod 2
            # Encode with sequential XOR
            if not active_products:
                if target == 1:
                    clauses.append([])  # UNSAT
                continue
            # Build XOR chain
            # x1 XOR x2 XOR ... XOR xn = target
            # Use auxiliary variables
            if len(active_products) == 1:
                if target:
                    clauses.append([active_products[0]])
                else:
                    clauses.append([-active_products[0]])
            else:
                # Sequential XOR with auxiliary vars
                prev = active_products[0]
                for i in range(1, len(active_products)):
                    nvar += 1
                    aux = nvar
                    x = active_products[i]
                    # aux = prev XOR x
                    clauses.append([-aux, -prev, -x])
                    clauses.append([-aux, prev, x])
                    clauses.append([aux, -prev, x])
                    clauses.append([aux, prev, -x])
                    prev = aux
                # Final: prev = target
                if target:
                    clauses.append([prev])
                else:
                    clauses.append([-prev])

print(f"SAT encoding: {nvar} variables, {len(clauses)} clauses")

# Write CNF
cnf_path = Path("data/e11_complete_capacity/greedy_sat.cnf")
cnf_path.parent.mkdir(parents=True, exist_ok=True)
with open(cnf_path, 'w') as f:
    f.write(f"p cnf {nvar} {len(clauses)}\n")
    for cl in clauses:
        f.write(' '.join(str(l) for l in cl) + ' 0\n')
print(f"Wrote {cnf_path} ({cnf_path.stat().st_size} bytes)")

# Run kissat
t0 = time.time()
result = subprocess.run(['kissat', str(cnf_path)], capture_output=True, text=True, timeout=120)
elapsed = time.time() - t0

status = 'UNKNOWN'
if result.returncode == 10:
    status = 'SAT'
elif result.returncode == 20:
    status = 'UNSAT'

print(f"\nResult: {status} in {elapsed:.2f}s (exit code {result.returncode})")
if status == 'SAT':
    print("*** FOUND RANK-19 E11 CORE DECOMPOSITION! ***")
    # Extract solution
    model = []
    for line in result.stdout.split('\n'):
        if line.startswith('v '):
            model.extend(int(x) for x in line[2:].split() if x != '0')
    print(f"  Model size: {len(model)}")

out = {
    'status': status, 'elapsed_sec': elapsed,
    'greedy_vectors': greedy, 'rank': rank,
    'variables': nvar, 'clauses': len(clauses),
}
json_path = cnf_path.with_suffix('.json')
json_path.write_text(json.dumps(out, indent=2) + '\n')
print(f"Saved {json_path}")
