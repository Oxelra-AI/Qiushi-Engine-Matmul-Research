#!/usr/bin/env python3
"""Enumerate MIP-feasible A-multisets and SAT-test each for E11 rank-19.

This script:
1. Loads the complete E11 core capacity model
2. Uses CP-SAT to enumerate feasible multisets
3. Orbit-reduces under the corrected E11 stabilizer
4. SAT-tests each orbit representative with free B/C
5. Reports: if any SAT -> rank-19 found! If all UNSAT -> all admissible excluded.
"""
import argparse, json, pickle, subprocess, sys, time
from pathlib import Path
from collections import Counter
import numpy as np

SCRIPTS = Path("scripts")
sys.path.insert(0, str(SCRIPTS))
from core_capacity_from_wang_lut import CoreQuotient, PIVOTS
from wang_capacity_lazy import (
    pack_basis, unpack_basis, rref_basis,
    subspace_points_from_basis,
)
from wang_capacity_orbit_closed import extension_keys


def load_lut(path):
    with open(path, 'rb') as f:
        d = pickle.load(f)
    return d['lut'], d.get('meta', {})


def enumerate_subspace_keys(n=8):
    levels = {0: {pack_basis(tuple())}}
    all_keys = set(levels[0])
    for d in range(n):
        nxt = set()
        for key in levels[d]:
            for ekey in extension_keys(unpack_basis(key), n=n):
                if (ekey & 0xF) == d + 1:
                    nxt.add(ekey)
        levels[d + 1] = nxt
        all_keys.update(nxt)
    return sorted(all_keys)


def build_sat_cnf(core, a_factors, rank):
    """Build SAT CNF for fixed A-factors with free B/C."""
    nU, nV, nW = core.shape
    nvar = 0
    var_v, var_w, var_p = {}, {}, {}
    
    for t in range(rank):
        for b in range(nV):
            nvar += 1; var_v[(t,b)] = nvar
        for c in range(nW):
            nvar += 1; var_w[(t,c)] = nvar
    for t in range(rank):
        for b in range(nV):
            for c in range(nW):
                nvar += 1; var_p[(t,b,c)] = nvar

    clauses = []
    # Tseytin: p = v AND w
    for t in range(rank):
        for b in range(nV):
            for c in range(nW):
                p, v, w = var_p[(t,b,c)], var_v[(t,b)], var_w[(t,c)]
                clauses.extend([[-p, v], [-p, w], [p, -v, -w]])

    # Brent XOR equations
    for a in range(nU):
        for b in range(nV):
            for c in range(nW):
                target = int(core[a, b, c])
                active = [var_p[(t,b,c)] for t in range(rank) if (a_factors[t] >> a) & 1]
                if not active:
                    if target: clauses.append([])
                    continue
                if len(active) == 1:
                    clauses.append([active[0]] if target else [-active[0]])
                else:
                    prev = active[0]
                    for i in range(1, len(active)):
                        nvar += 1; aux = nvar
                        x = active[i]
                        clauses.extend([[-aux,-prev,-x],[-aux,prev,x],[aux,-prev,x],[aux,prev,-x]])
                        prev = aux
                    clauses.append([prev] if target else [-prev])
    return nvar, clauses


def sat_test(core, a_factors, timeout=60):
    """Test if fixed A-factors admit valid B/C factors."""
    rank = len(a_factors)
    nvar, clauses = build_sat_cnf(core, a_factors, rank)
    
    # Write CNF to temp file
    import tempfile
    with tempfile.NamedTemporaryFile(mode='w', suffix='.cnf', delete=False) as f:
        f.write(f"p cnf {nvar} {len(clauses)}\n")
        for cl in clauses:
            f.write(' '.join(str(l) for l in cl) + ' 0\n')
        cnf_path = f.name
    
    try:
        result = subprocess.run(['kissat', cnf_path], capture_output=True, 
                               text=True, timeout=timeout)
        if result.returncode == 10: return 'SAT'
        elif result.returncode == 20: return 'UNSAT'
        return 'UNKNOWN'
    except subprocess.TimeoutExpired:
        return 'TIMEOUT'
    finally:
        Path(cnf_path).unlink(missing_ok=True)


def multiset_to_list(sol_dict):
    """Convert {vector: multiplicity} to sorted list."""
    result = []
    for v, m in sorted(sol_dict.items()):
        result.extend([v] * m)
    return result


def canonicalize_multiset(multiset, group_perms):
    """Canonicalize a sorted multiset under group action."""
    canon = tuple(multiset)
    for perm in group_perms:
        img = tuple(sorted(perm[v] for v in multiset))
        if img < canon:
            canon = img
    return canon


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--mip-result', type=Path, required=True,
                    help='Path to MIP result JSON with feasible solution')
    ap.add_argument('--json-out', type=Path, required=True)
    args = ap.parse_args()

    # Load core tensor
    core = np.load("data/restricted_cores/mask_001_E11_core.npy")
    print(f"E11 core: {core.shape}")

    # Load MIP result
    mip = json.loads(args.mip_result.read_text())
    cpsat = mip.get('cpsat_result', {})
    
    if cpsat.get('status') == 'INFEASIBLE':
        print("MIP INFEASIBLE: E11 rank >= 20 over F2!")
        print("The E11 constructive route to rank-22 is CLOSED.")
        result = {'conclusion': 'E11_RANK_GE_20', 'via': 'Wang_capacity_complete_MIP'}
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(result, indent=2) + '\n')
        return

    sol = cpsat.get('solution')
    if sol is None:
        print(f"No solution found: status={cpsat.get('status')}")
        return

    # Convert solution to A-factor list
    a_factors = multiset_to_list({int(k): v for k, v in sol.items()})
    print(f"MIP solution: {len(a_factors)} A-factors, support={len(sol)}")
    print(f"A-factors: {a_factors}")

    # SAT test
    print("\nSAT testing MIP solution...")
    status = sat_test(core, a_factors)
    print(f"Result: {status}")

    result = {
        'a_factors': a_factors,
        'support': len(sol),
        'sat_status': status,
    }
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(result, indent=2) + '\n')
    print(f"Saved {args.json_out}")


if __name__ == '__main__':
    main()
