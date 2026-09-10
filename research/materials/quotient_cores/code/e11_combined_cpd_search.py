#!/usr/bin/env python3
"""Combined Wang capacity + Brent CPD search for E11 rank-19 over F2.

Instead of: enumerate admissible A-multisets -> SAT-test each,
this model directly searches for (A,B,C) factors simultaneously.

CP-SAT variables:
  u_t: integer 1..255 for each term's A-factor (19 terms)
  a_{t,k}: Boolean for bit k of u_t (8 bits per term)
  v_{t,b}: Boolean for B-factor bit b (9 bits per term)
  w_{t,c}: Boolean for C-factor bit c (9 bits per term)
  
Constraints:
  - Linking: u_t = sum_k a_{t,k} * 2^k
  - Symmetry breaking: u_0 <= u_1 <= ... <= u_18
  - Products: p_{t,b,c} = v_{t,b} AND w_{t,c}
  - Contributions: q_{t,k,b,c} = a_{t,k} AND p_{t,b,c}
  - Brent equations: XOR_t q_{t,a,b,c} = T[a,b,c] for each (a,b,c)
  - Wang cap=1 constraints: for each subspace Psi with cap=1,
    at most 1 term has u_t in Psi
"""
import argparse, json, pickle, sys, time
from pathlib import Path
import numpy as np

SCRIPTS = Path("scripts")
sys.path.insert(0, str(SCRIPTS))
from core_capacity_from_wang_lut import CoreQuotient, PIVOTS
from wang_capacity_lazy import (
    pack_basis, unpack_basis, rref_basis,
    subspace_points_from_basis,
)

def load_lut(path):
    with open(path, 'rb') as f:
        d = pickle.load(f)
    return d['lut'], d.get('meta', {})

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lut', type=Path,
                    default=Path('data/wang_f2_lb20/wang_subspace_lut.pkl'))
    ap.add_argument('--rank', type=int, default=19)
    ap.add_argument('--time-limit', type=float, default=3600)
    ap.add_argument('--max-cap', type=int, default=2,
                    help='Include Wang constraints with cap <= this value')
    ap.add_argument('--json-out', type=Path,
                    default=Path('data/combined_cpd/result.json'))
    args = ap.parse_args()

    from ortools.sat.python import cp_model

    # Load core tensor
    core = np.load("data/restricted_cores/mask_001_E11_core.npy")
    nU, nV, nW = core.shape
    rank = args.rank
    print(f"E11 core: {core.shape}, target rank: {rank}")

    # Load Wang constraints
    print("Loading Wang LUT...")
    lut, meta = load_lut(args.lut)
    cq = CoreQuotient(PIVOTS['E11'])
    s = rank

    # Collect cap-restricted subspace constraints
    print(f"Computing dim-1 and dim-2 capacity constraints (max_cap={args.max_cap})...")
    wang_constraints = []  # (points_set, cap)
    
    # Dim-1: each vector q
    for q in range(1, 256):
        key8 = pack_basis((q,))
        key9 = cq.key9_from_key8(key8)
        L = lut[key9]
        cap = s - L
        if cap <= args.max_cap:
            wang_constraints.append(({q}, cap))
    
    # Dim-2: pairs 
    from itertools import combinations
    seen = set()
    for a, b in combinations(range(1, 256), 2):
        c = a ^ b
        triple = frozenset((a, b, c))
        if triple in seen:
            continue
        seen.add(triple)
        key8 = pack_basis(rref_basis((a, b), n=8))
        key9 = cq.key9_from_key8(key8)
        L = lut[key9]
        cap = s - L
        if cap <= args.max_cap:
            wang_constraints.append((set(triple), cap))

    print(f"Wang constraints with cap <= {args.max_cap}: {len(wang_constraints)}")
    cap_dist = {}
    for _, cap in wang_constraints:
        cap_dist[cap] = cap_dist.get(cap, 0) + 1
    print(f"  Distribution: {cap_dist}")

    # Build CP-SAT model
    print("Building CP-SAT model...")
    model = cp_model.CpModel()

    # A-factor variables: u_t integer, a_{t,k} Boolean
    u = [model.new_int_var(1, 255, f'u_{t}') for t in range(rank)]
    a_bits = [[model.new_bool_var(f'a_{t}_{k}') for k in range(nU)] for t in range(rank)]
    
    # Link u_t to bits
    for t in range(rank):
        model.add(u[t] == sum(a_bits[t][k] * (1 << k) for k in range(nU)))

    # Symmetry breaking: sorted order
    for t in range(rank - 1):
        model.add(u[t] <= u[t + 1])

    # B/C factor variables
    v = [[model.new_bool_var(f'v_{t}_{b}') for b in range(nV)] for t in range(rank)]
    w = [[model.new_bool_var(f'w_{t}_{c}') for c in range(nW)] for t in range(rank)]

    # Product variables: p_{t,b,c} = v_{t,b} AND w_{t,c}
    p = {}
    for t in range(rank):
        for b in range(nV):
            for c in range(nW):
                p[(t,b,c)] = model.new_bool_var(f'p_{t}_{b}_{c}')
                model.add_multiplication_equality(p[(t,b,c)], [v[t][b], w[t][c]])

    # Contribution variables: q_{t,a,b,c} = a_{t,a} AND p_{t,b,c}
    q = {}
    for t in range(rank):
        for aa in range(nU):
            for b in range(nV):
                for c in range(nW):
                    q[(t,aa,b,c)] = model.new_bool_var(f'q_{t}_{aa}_{b}_{c}')
                    model.add_multiplication_equality(q[(t,aa,b,c)], [a_bits[t][aa], p[(t,b,c)]])

    # Brent XOR equations
    brent_count = 0
    for aa in range(nU):
        for b in range(nV):
            for c in range(nW):
                target = int(core[aa, b, c])
                contrib_vars = [q[(t, aa, b, c)] for t in range(rank)]
                # XOR of contrib_vars should equal target
                if target == 1:
                    model.add_bool_xor(contrib_vars)
                else:
                    # XOR should be 0: negate one variable to flip parity
                    lits = [contrib_vars[0].negated()] + contrib_vars[1:]
                    model.add_bool_xor(lits)
                brent_count += 1
    print(f"Brent equations: {brent_count}")

    # Wang capacity constraints
    for pts, cap in wang_constraints:
        pts_list = sorted(pts)
        if cap == 0:
            # No term can be in this subspace (should be vacuous)
            for t in range(rank):
                for pt in pts_list:
                    model.add(u[t] != pt)
        elif cap == 1:
            # At most 1 term in this subspace
            indicators = []
            for t in range(rank):
                ind = model.new_bool_var(f'in_{id(pts)}_{t}')
                # ind = 1 iff u_t is in pts_list
                model.add_allowed_assignments([u[t], ind], 
                    [(pt, 1) for pt in pts_list] + 
                    [(v, 0) for v in range(1, 256) if v not in pts])
                indicators.append(ind)
            model.add(sum(indicators) <= cap)
        elif cap == 2:
            indicators = []
            for t in range(rank):
                ind = model.new_bool_var(f'in_{id(pts)}_{t}')
                model.add_allowed_assignments([u[t], ind],
                    [(pt, 1) for pt in pts_list] + 
                    [(v, 0) for v in range(1, 256) if v not in pts])
                indicators.append(ind)
            model.add(sum(indicators) <= cap)

    num_vars = model.num_variables
    num_constraints = model.num_constraints
    print(f"Model: {num_vars} variables, {num_constraints} constraints")

    # Solve
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.time_limit
    solver.parameters.num_workers = 8
    solver.parameters.log_search_progress = True

    print(f"\nSolving (time_limit={args.time_limit}s)...")
    t0 = time.time()
    status = solver.solve(model)
    elapsed = time.time() - t0

    status_name = {
        cp_model.OPTIMAL: 'OPTIMAL',
        cp_model.FEASIBLE: 'FEASIBLE',
        cp_model.INFEASIBLE: 'INFEASIBLE',
        cp_model.MODEL_INVALID: 'MODEL_INVALID',
        cp_model.UNKNOWN: 'UNKNOWN',
    }.get(status, f'status_{status}')

    print(f"\nResult: {status_name} in {elapsed:.1f}s")

    solution = None
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        a_factors = [solver.value(u[t]) for t in range(rank)]
        b_factors = [[solver.value(v[t][b]) for b in range(nV)] for t in range(rank)]
        c_factors = [[solver.value(w[t][c]) for c in range(nW)] for t in range(rank)]
        solution = {
            'a_factors': a_factors,
            'b_factors': b_factors,
            'c_factors': c_factors,
        }
        print(f"*** FOUND RANK-{rank} E11 CORE DECOMPOSITION! ***")
        print(f"A-factors: {a_factors}")
        
        # Verify: reconstruct tensor
        recon = np.zeros_like(core)
        for t in range(rank):
            for aa in range(nU):
                if (a_factors[t] >> aa) & 1:
                    for b in range(nV):
                        for c in range(nW):
                            recon[aa, b, c] ^= (b_factors[t][b] & c_factors[t][c])
        diff = np.sum(recon != core)
        print(f"Verification: {diff} differences")
        solution['verified'] = int(diff) == 0

    result = {
        'problem': 'E11 combined capacity + Brent CPD search',
        'field': 'F2',
        'core_shape': list(core.shape),
        'rank': rank,
        'status': status_name,
        'elapsed_sec': elapsed,
        'wang_constraints': len(wang_constraints),
        'cap_distribution': cap_dist,
        'model_variables': num_vars,
        'model_constraints': num_constraints,
        'solution': solution,
    }

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(result, indent=2, default=str) + '\n')
    print(f"\nSaved {args.json_out}")


if __name__ == '__main__':
    main()
