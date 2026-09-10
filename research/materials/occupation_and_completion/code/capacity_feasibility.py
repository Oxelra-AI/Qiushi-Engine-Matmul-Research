#!/usr/bin/env python3
"""Capacity-feasibility test for the E11 restricted core of T<3,3,3> over F2.

The Wang certificate gives lower bounds L(V) for every restriction subspace V of T.
For the E11 core (a11=0, 8x9x9 tensor), any rank-r decomposition has r A-factors
in F2^8. For each subspace S of F2^8 corresponding to a Wang restriction [E11, ...],
the number of A-factors in S must be >= L(S).

Equivalently, for each linear functional f on F2^8 with Wang lower bound L_f for the
codim-1 restriction [E11, f], at most r - L_f of the r A-factors can have f(u)=1.

This script:
1. Generates GL(3,2) and the stabilizer Stab(E11).
2. Computes Stab(E11) orbits on the 255 nonzero functionals on F2^8.
3. Maps orbits to Wang lower bounds using the 6 known dim-2 representatives.
4. Sets up capacity-feasibility ILP with OR-Tools CP-SAT.
5. Solves for r=19 (decisive) and r=20.

If r=19 is INFEASIBLE: R_F2(core_E11) >= 20, hence R_F2(T) >= 21.
If r=19 is FEASIBLE: occupation constraints alone don't prevent rank 19.
"""
import json
import numpy as np
from pathlib import Path
from itertools import product
from collections import defaultdict

# ============================================================
# F2 matrix arithmetic
# ============================================================

def mat_mul_f2(A, B):
    """Multiply 3x3 F2 matrices."""
    n = A.shape[0]
    C = np.zeros((n, n), dtype=np.uint8)
    for i in range(n):
        for j in range(n):
            C[i, j] = sum(A[i, k] * B[k, j] for k in range(n)) % 2
    return C

def mat_inv_f2(M):
    """Invert a 3x3 F2 matrix using augmented matrix."""
    n = M.shape[0]
    aug = np.hstack([M.copy(), np.eye(n, dtype=np.uint8)])
    for col in range(n):
        pivot = None
        for row in range(col, n):
            if aug[row, col]:
                pivot = row
                break
        assert pivot is not None, "Matrix not invertible"
        if pivot != col:
            aug[[col, pivot]] = aug[[pivot, col]]
        for row in range(n):
            if row != col and aug[row, col]:
                aug[row] = (aug[row] + aug[col]) % 2
    return aug[:, n:]

def mat_to_mask(M):
    """3x3 F2 matrix -> 9-bit integer (bit i = M[i//3][i%3])."""
    v = 0
    for i in range(3):
        for j in range(3):
            if M[i, j]:
                v |= 1 << (3 * i + j)
    return v

def mask_to_mat(v):
    """9-bit integer -> 3x3 F2 matrix."""
    M = np.zeros((3, 3), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            if v & (1 << (3 * i + j)):
                M[i, j] = 1
    return M

def mat_rank_f2(M):
    """Rank of a matrix over F2."""
    A = M.copy()
    n, m = A.shape
    rank = 0
    for col in range(m):
        pivot = None
        for row in range(rank, n):
            if A[row, col]:
                pivot = row
                break
        if pivot is None:
            continue
        if pivot != rank:
            A[[rank, pivot]] = A[[pivot, rank]]
        for row in range(n):
            if row != rank and A[row, col]:
                A[row] = (A[row] + A[rank]) % 2
        rank += 1
    return rank

# ============================================================
# Generate GL(3,2) and Stab(E11)
# ============================================================

def generate_gl3_f2():
    """Generate all invertible 3x3 matrices over F2."""
    matrices = []
    for bits in range(512):  # 2^9 possible 3x3 F2 matrices
        M = mask_to_mat(bits)
        if mat_rank_f2(M) == 3:
            matrices.append(M)
    return matrices

def generate_stab_e1(gl_matrices):
    """Matrices in GL(3,2) that fix e1 = (1,0,0)."""
    return [M for M in gl_matrices if M[0, 0] == 1 and M[1, 0] == 0 and M[2, 0] == 0]

# ============================================================
# Stab(E11) action on functionals
# ============================================================

def act_on_functional_9bit(L_inv_t, R_inv_t, transpose_flag, f_mask):
    """Apply Stab(E11) element to a 9-bit functional mask.
    
    Direct action on A: g.A = L . tau^t(A) . R
    Dual action on functional f: g.f = L^{-T} . tau^t(f) . R^{-T}
    
    Here L_inv_t = (L^{-1})^T and R_inv_t = (R^{-1})^T.
    """
    F = mask_to_mat(f_mask)
    if transpose_flag:
        F = F.T
    result = mat_mul_f2(mat_mul_f2(L_inv_t, F), R_inv_t)
    return mat_to_mask(result)

def compute_functional_orbits(stab_L, stab_R):
    """Compute orbits of Stab(E11) on the 255 nonzero functionals with bit0=0.
    
    Functionals on F2^8 = ker(E11) correspond to 9-bit masks with bit 0 = 0.
    These are even values from 2 to 510.
    """
    # Precompute (L^{-1})^T and (R^{-1})^T for each stabilizer element
    group_elements = []
    for L in stab_L:
        L_inv = mat_inv_f2(L)
        L_inv_t = L_inv.T.copy()
        for R in stab_R:
            R_inv = mat_inv_f2(R)
            R_inv_t = R_inv.T.copy()
            group_elements.append((L_inv_t, R_inv_t, 0))
            group_elements.append((L_inv_t, R_inv_t, 1))  # with transpose
    
    # All 255 nonzero functionals with bit0=0
    functionals = set()
    for v in range(2, 512, 2):  # even values 2..510
        # Check it's a valid 8-bit functional (bits 1-8)
        if v > 0 and (v & 1) == 0:
            functionals.add(v)
    assert len(functionals) == 255, f"Expected 255, got {len(functionals)}"
    
    # Compute orbits
    visited = set()
    orbits = []
    for f in sorted(functionals):
        if f in visited:
            continue
        orbit = set()
        queue = [f]
        while queue:
            current = queue.pop()
            if current in orbit:
                continue
            orbit.add(current)
            for (L_inv_t, R_inv_t, t) in group_elements:
                img = act_on_functional_9bit(L_inv_t, R_inv_t, t, current)
                if img in functionals and img not in orbit:
                    queue.append(img)
        visited.update(orbit)
        orbits.append(frozenset(orbit))
    
    return orbits

# ============================================================
# Match orbits to Wang lower bounds
# ============================================================

# Wang dim-2 orbit representatives containing E11 (constraint 1):
# Format: second_constraint_9bit -> Wang_lower_bound
WANG_DIM2_E11 = {
    2: 17,    # [1, 2]  E12
    10: 18,   # [1, 10] E12+E21
    16: 18,   # [1, 16] E22
    20: 18,   # [1, 20] E13+E22
    84: 18,   # [1, 84] E13+E22+E31
    160: 18,  # [1, 160] E23+E32
}

def match_orbits_to_wang(orbits):
    """Match each Stab(E11) orbit to a Wang dim-2 orbit and get its lower bound."""
    matched = {}
    for orbit in orbits:
        lb = None
        matched_rep = None
        for rep_9bit, wang_lb in WANG_DIM2_E11.items():
            if rep_9bit in orbit:
                lb = wang_lb
                matched_rep = rep_9bit
                break
        if lb is None:
            # Try if the orbit representative, when extended to 9-bit, matches
            # any of the Wang representatives through the full group action
            print(f"WARNING: orbit {sorted(orbit)[:5]}... not matched to Wang dim-2")
            lb = 0  # No constraint
        matched[orbit] = (lb, matched_rep)
    return matched

# ============================================================
# Build and solve capacity ILP
# ============================================================

def solve_capacity_ilp(orbits_with_lb, target_rank, verbose=True):
    """Solve: can we place target_rank points in P(F2^8) satisfying all capacity constraints?
    
    Variables: x_p for each projective point p in {1,...,255}, x_p >= 0 integer.
    Constraint: sum_p x_p = target_rank.
    For each functional f with lower bound L_f:
        sum_{p: f(p)=1} x_p <= target_rank - L_f.
    (Equivalently: sum_{p: f(p)=0, p!=0} x_p >= L_f.)
    """
    from ortools.sat.python import cp_model
    
    model = cp_model.CpModel()
    
    # 255 projective points in P(F2^8): integers 1..255
    points = list(range(1, 256))
    x = {}
    for p in points:
        x[p] = model.NewIntVar(0, target_rank, f'x_{p}')
    
    # Total points = target_rank
    model.Add(sum(x[p] for p in points) == target_rank)
    
    # Capacity constraints from each functional
    constraint_count = 0
    constraints_by_lb = defaultdict(int)
    
    # All 255 nonzero 8-bit functionals
    for f_8bit in range(1, 256):
        # Convert to 9-bit (shift left by 1 since bit 0 is a11=0)
        # Wait: 8-bit representation uses bits 0-7 for coordinates a12,a13,...,a33
        # which are bits 1-8 of the 9-bit mask. So f_9bit = f_8bit << 1.
        # Actually NO: the 8-bit coordinate i (0-indexed) maps to 9-bit coordinate i+1.
        # An 8-bit functional value f_8bit has bit j set if the functional uses
        # the j-th coordinate of F2^8. Coordinate j of F2^8 = coordinate (j+1) of F2^9.
        # So the 9-bit mask of f is: for each bit j in f_8bit, set bit (j+1) in f_9bit.
        f_9bit = f_8bit << 1  # This shifts all bits left by 1
        
        # Find which Wang orbit this functional belongs to
        lb = None
        for orbit, (wang_lb, _) in orbits_with_lb.items():
            if f_9bit in orbit:
                lb = wang_lb
                break
        
        if lb is None or lb <= 0:
            continue
        
        capacity = target_rank - lb
        if capacity < 0:
            if verbose:
                print(f"  IMPOSSIBLE: functional {f_8bit} (9bit: {f_9bit}) has LB={lb} > rank={target_rank}")
            return "INFEASIBLE", None, f"LB {lb} > rank {target_rank} for functional {f_8bit}"
        
        # Points where f evaluates to 1
        violators = []
        for p in points:
            # f(p) = dot product of f_8bit and p over F2
            dot = bin(f_8bit & p).count('1') % 2
            if dot == 1:
                violators.append(p)
        
        model.Add(sum(x[p] for p in violators) <= capacity)
        constraint_count += 1
        constraints_by_lb[lb] += 1
    
    if verbose:
        print(f"  Total hyperplane constraints: {constraint_count}")
        print(f"  Constraints by LB: {dict(sorted(constraints_by_lb.items()))}")
    
    # Solve
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 60
    status = solver.Solve(model)
    
    status_name = {
        cp_model.OPTIMAL: "FEASIBLE",
        cp_model.FEASIBLE: "FEASIBLE",
        cp_model.INFEASIBLE: "INFEASIBLE",
        cp_model.MODEL_INVALID: "INVALID",
        cp_model.UNKNOWN: "UNKNOWN",
    }.get(status, f"STATUS_{status}")
    
    solution = None
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        solution = {p: solver.Value(x[p]) for p in points if solver.Value(x[p]) > 0}
    
    return status_name, solution, None

# ============================================================
# Also build explicit SAT encoding for cross-check
# ============================================================

def solve_capacity_sat(orbits_with_lb, target_rank, verbose=True):
    """SAT-based cross-check using PySAT."""
    from pysat.solvers import Cadical153
    from pysat.card import CardEnc, EncType
    
    points = list(range(1, 256))
    # Variables: x_{p,t} for point p, slot t (1-indexed)
    # x_{p,t} = 1 means the t-th A-factor is point p
    
    # Actually, a simpler encoding: for each point p, a variable count_p
    # encoded in unary: y_{p,1}, ..., y_{p,R} where y_{p,k} = 1 iff x_p >= k
    
    # Even simpler for small R: use assignment variables.
    # For each term t (1..R) and point p (1..255): a_{t,p} = 1 iff term t has A-factor p
    # Exactly one p per term: exactly-one constraint
    # For each functional f: sum over t of (a_{t,p} where f(p)=1) <= capacity
    
    # This has R * 255 = 19 * 255 = 4845 variables (for R=19)
    # Plus cardinality constraints
    
    R = target_rank
    n_vars = 0
    var_map = {}  # (t, p) -> var_id
    
    for t in range(R):
        for p in points:
            n_vars += 1
            var_map[(t, p)] = n_vars
    
    clauses = []
    
    # Exactly one point per term
    for t in range(R):
        term_vars = [var_map[(t, p)] for p in points]
        # At least one
        clauses.append(term_vars)
        # At most one (pairwise)
        for i in range(len(term_vars)):
            for j in range(i + 1, len(term_vars)):
                clauses.append([-term_vars[i], -term_vars[j]])
    
    if verbose:
        print(f"  SAT: {n_vars} vars, {len(clauses)} clauses after exactly-one")
    
    # Capacity constraints
    cap_constraints = 0
    for f_8bit in range(1, 256):
        f_9bit = f_8bit << 1
        
        lb = None
        for orbit, (wang_lb, _) in orbits_with_lb.items():
            if f_9bit in orbit:
                lb = wang_lb
                break
        
        if lb is None or lb <= 0:
            continue
        
        capacity = R - lb
        if capacity < 0:
            return "INFEASIBLE", None
        
        # For each term t, the indicator that f(A-factor of t) = 1
        # is: OR over p with f(p)=1 of a_{t,p}
        # Since exactly one a_{t,p} is true, the indicator is simply
        # a_{t,p*} for the unique p* chosen for term t, iff f(p*)=1.
        # The sum of these indicators over t is at most capacity.
        
        # Violating points for this functional
        violators = set()
        for p in points:
            if bin(f_8bit & p).count('1') % 2 == 1:
                violators.add(p)
        
        # For each term t, define indicator z_{t,f} = OR_{p in violators} a_{t,p}
        # Since exactly one a_{t,p} is true, z_{t,f} = 1 iff chosen p is in violators.
        # z_{t,f} = sum_{p in violators} a_{t,p}
        
        # The z variables are implicit from the assignment.
        # Constraint: at most capacity of the z_{t,f} can be 1.
        # z_{t,f} <=> OR_{p in violators} a_{t,p}
        # But with exactly-one, z_{t,f} = sum_{p in violators} a_{t,p} is 0 or 1.
        
        indicator_vars = []
        for t in range(R):
            # z_{t,f}: auxiliary var
            n_vars += 1
            z = n_vars
            indicator_vars.append(z)
            
            viol_vars = [var_map[(t, p)] for p in violators if (t, p) in var_map]
            
            # z = 1 => at least one violator is chosen
            # z = 0 => no violator is chosen
            # Since exactly one p is chosen, z = 1 iff the chosen p is a violator.
            
            # z => OR viol_vars: already implied by exactly-one + z definition
            # OR viol_vars => z: for each v in viol_vars: v => z
            for v in viol_vars:
                clauses.append([-v, z])
            # z => OR viol_vars
            clauses.append([-z] + viol_vars)
        
        # At most capacity of the indicators can be true
        if capacity == 0:
            for z in indicator_vars:
                clauses.append([-z])
        else:
            enc = CardEnc.atmost(indicator_vars, bound=capacity, top_id=n_vars,
                                 encoding=EncType.totalizer)
            if enc.nv > n_vars:
                n_vars = enc.nv
            clauses.extend(enc.clauses)
        
        cap_constraints += 1
    
    if verbose:
        print(f"  SAT: {n_vars} total vars, {len(clauses)} total clauses, {cap_constraints} capacity constraints")
    
    # Solve
    solver = Cadical153()
    for cl in clauses:
        solver.add_clause(cl)
    
    result = solver.solve_limited(expect=60)
    
    if result is True:
        model = solver.get_model()
        solution = {}
        for t in range(R):
            for p in points:
                if model[var_map[(t, p)] - 1] > 0:
                    solution[t] = p
                    break
        solver.delete()
        return "FEASIBLE", solution
    elif result is False:
        solver.delete()
        return "INFEASIBLE", None
    else:
        solver.delete()
        return "UNKNOWN", None

# ============================================================
# Main
# ============================================================

def main():
    outdir = Path("data/restricted_cores")
    outdir.mkdir(parents=True, exist_ok=True)
    
    print("=" * 70)
    print("CAPACITY FEASIBILITY TEST FOR E11 CORE")
    print("=" * 70)
    
    # analysis: Generate GL(3,2) and stabilizers
    print("\n1. Generating GL(3,2)...")
    gl = generate_gl3_f2()
    print(f"   |GL(3,2)| = {len(gl)}")
    
    stab_L = generate_stab_e1(gl)
    stab_R = generate_stab_e1(gl)
    print(f"   |Stab_L(e1)| = {len(stab_L)}")
    print(f"   |Stab_R(e1)| = {len(stab_R)}")
    print(f"   |Stab(E11)| = {len(stab_L) * len(stab_R) * 2} (with transpose)")
    
    # analysis: Compute orbits on functionals
    print("\n2. Computing Stab(E11) orbits on 255 functionals...")
    orbits = compute_functional_orbits(stab_L, stab_R)
    print(f"   Found {len(orbits)} orbits")
    total = sum(len(o) for o in orbits)
    print(f"   Total functionals covered: {total}")
    assert total == 255, f"Expected 255, got {total}"
    
    for i, orb in enumerate(orbits):
        rep = min(orb)
        rep_mat = mask_to_mat(rep)
        rank = mat_rank_f2(rep_mat)
        print(f"   Orbit {i}: size {len(orb)}, representative 9bit={rep}, rank={rank}")
    
    # analysis: Match to Wang lower bounds
    print("\n3. Matching orbits to Wang dim-2 lower bounds...")
    matched = match_orbits_to_wang(orbits)
    
    for orbit, (lb, rep) in matched.items():
        orb_rep = min(orbit)
        print(f"   Orbit rep={orb_rep}: Wang LB={lb}, matched to Wang rep={rep}, size={len(orbit)}")
    
    # Summary: how many functionals at each LB
    lb_counts = defaultdict(int)
    for orbit, (lb, _) in matched.items():
        lb_counts[lb] += len(orbit)
    print(f"\n   Functionals by Wang LB: {dict(sorted(lb_counts.items()))}")
    
    # analysis: Solve capacity ILP
    for r in [19, 20]:
        print(f"\n{'=' * 70}")
        print(f"SOLVING CAPACITY ILP FOR rank = {r}")
        print(f"{'=' * 70}")
        
        status, solution, msg = solve_capacity_ilp(matched, r, verbose=True)
        print(f"\n  ILP STATUS: {status}")
        if msg:
            print(f"  Message: {msg}")
        if solution:
            print(f"  Solution ({len(solution)} distinct points):")
            for p, count in sorted(solution.items()):
                p_mat = mask_to_mat(p << 1)  # Convert 8-bit point to 9-bit for display
                bits = bin(p)[2:].zfill(8)
                print(f"    point {p} (0b{bits}): count={count}")
            
            # Verify the solution
            print("\n  Verifying solution against all constraints...")
            all_ok = True
            for f_8bit in range(1, 256):
                f_9bit = f_8bit << 1
                lb = None
                for orbit, (wang_lb, _) in matched.items():
                    if f_9bit in orbit:
                        lb = wang_lb
                        break
                if lb is None or lb <= 0:
                    continue
                capacity = r - lb
                violator_count = 0
                for p, cnt in solution.items():
                    if bin(f_8bit & p).count('1') % 2 == 1:
                        violator_count += cnt
                if violator_count > capacity:
                    print(f"    VIOLATION: f={f_8bit}, LB={lb}, cap={capacity}, actual={violator_count}")
                    all_ok = False
            if all_ok:
                print("    All constraints satisfied. ✓")
    
    # analysis: Save results
    results = {
        "gl3_f2_size": len(gl),
        "stab_e11_size": len(stab_L) * len(stab_R) * 2,
        "num_orbits": len(orbits),
        "orbits": [],
        "wang_dim2_bounds": WANG_DIM2_E11,
    }
    
    for orbit, (lb, rep) in matched.items():
        results["orbits"].append({
            "representative_9bit": min(orbit),
            "size": len(orbit),
            "wang_lb": lb,
            "wang_representative": rep,
            "members_9bit": sorted(orbit),
        })
    
    outpath = outdir / "capacity_feasibility.json"
    with open(outpath, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {outpath}")

if __name__ == '__main__':
    main()
