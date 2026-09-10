#!/usr/bin/env python3
"""analysis: Orbit-averaged SDP (LP + Moment PSD) for E11 distinct-support branch.

Tests whether the orbit-averaged Wang RLT relaxation, strengthened with the
moment-matrix PSD constraint M(x,y) ⪰ 0, can exclude integer count vectors.

Flow:
  1. Build orbit infrastructure
  2. Build coefficient matrices for the 256×256 moment matrix
  3. Solve continuous SDP (LP + PSD) - should be feasible (uniform point)
  4. For each of the four analysis witnesses, fix n_a and check SDP feasibility
  5. Scan count vectors: fix n_a and check SDP feasibility
"""
from __future__ import annotations
import numpy as np, json, time, sys
from pathlib import Path
from itertools import product as iproduct
from scipy import sparse as sp

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

OUT = ROOT / "workspace/data/orbit_sdp"
OUT.mkdir(parents=True, exist_ok=True)

# ── F2 helpers (from analysis) ─────────────────────────────────────────

def _int_to_mat(p):
    M = np.zeros((3,3), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            k = 3*i+j
            if k == 0: continue
            M[i,j] = (p >> (k-1)) & 1
    return M

_MATS = [_int_to_mat(p) for p in range(256)]

def _mat_to_int(M):
    p = 0
    for i in range(3):
        for j in range(3):
            k = 3*i+j
            if k == 0: continue
            if int(M[i,j]) % 2: p |= 1 << (k-1)
    return p

def _gl3f2_stab_e1():
    res = []
    for entries in iproduct(range(2), repeat=9):
        M = np.array(entries, dtype=np.uint8).reshape(3,3)
        if M[0,0]!=1 or M[1,0]!=0 or M[2,0]!=0: continue
        if int(round(np.linalg.det(M.astype(float)))) % 2 != 1: continue
        res.append(M)
    return res

def build_stabilizer():
    stab = _gl3f2_stab_e1()
    all_perms = set()
    for P in stab:
        for Q in stab:
            pd = [0]*256; pt = [0]*256
            for p in range(256):
                M = _MATS[p]
                Md = (P.astype(int) @ M.astype(int) @ Q.T.astype(int)) % 2; Md[0,0]=0
                pd[p] = _mat_to_int(Md)
                Mt = (Q.astype(int) @ M.T.astype(int) @ P.T.astype(int)) % 2; Mt[0,0]=0
                pt[p] = _mat_to_int(Mt)
            all_perms.add(tuple(pd)); all_perms.add(tuple(pt))
    return np.array(list(all_perms), dtype=np.uint16)

def compute_point_orbits(perms):
    par = list(range(256))
    def find(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    def union(a,b):
        a,b=find(a),find(b)
        if a!=b: par[max(a,b)]=min(a,b)
    for perm in perms:
        for p in range(1,256): union(p, int(perm[p]))
    omap={}; orbits=[]
    pt_orb=[0]*256
    for p in range(1,256):
        r=find(p)
        if r not in omap: omap[r]=len(orbits); orbits.append([])
        idx=omap[r]; orbits[idx].append(p); pt_orb[p]=idx
    return pt_orb, orbits

def compute_pair_orbits(perms, pt_orb):
    pp=[]; qq=[]
    for p in range(1,256):
        for q in range(p+1,256):
            pp.append(p); qq.append(q)
    pp=np.array(pp,dtype=np.uint16); qq=np.array(qq,dtype=np.uint16)
    ip = perms[:, pp]; iq = perms[:, qq]
    pmin = np.minimum(ip,iq); pmax = np.maximum(ip,iq)
    keys = pmin.astype(np.uint32)*256 + pmax.astype(np.uint32)
    canon = keys.min(axis=0)
    ukeys = np.unique(canon)
    k2id = {int(k):i for i,k in enumerate(ukeys)}
    M = len(ukeys)
    pair_orb = {}; pair_sizes = [0]*M; pair_ep = [None]*M
    for idx in range(len(pp)):
        p,q = int(pp[idx]),int(qq[idx])
        oid = k2id[int(canon[idx])]
        pair_orb[(p,q)] = oid
        pair_sizes[oid] += 1
        if pair_ep[oid] is None:
            a,b = pt_orb[p], pt_orb[q]
            pair_ep[oid] = (min(a,b), max(a,b))
    return pair_orb, pair_sizes, pair_ep, M

# ── Build SDP coefficient matrices ──────────────────────────────────────

def build_coefficient_matrices(K, orbits, pair_orb, pair_sizes, pt_orb, M_p):
    """Build coefficient matrices for M = A_0 + Σ_a x_a A_a + Σ_j y_j A_j.
    
    Returns A_0 and list of (variable_index, matrix) for each of 103 variables.
    Variable indices: 0..K-1 are x_a, K..K+M_p-1 are y_j.
    """
    n = 256
    sizes = [len(o) for o in orbits]
    
    # A_0: constant matrix, only A_0[0,0] = 1
    A_0 = np.zeros((n, n))
    A_0[0, 0] = 1.0
    
    # A_a for each point orbit a: contributes to M[0,p], M[p,0], M[p,p]
    A_list = []  # list of (var_idx, dense_matrix)
    
    for a in range(K):
        Aa = np.zeros((n, n))
        for p in orbits[a]:
            Aa[0, p] = 1.0
            Aa[p, 0] = 1.0
            Aa[p, p] = 1.0
        A_list.append((a, Aa))
    
    # A_j for each pair orbit j: contributes to M[p,q], M[q,p]
    for j in range(M_p):
        Aj = np.zeros((n, n))
        for p in range(1, 256):
            for q in range(p+1, 256):
                key = (p, q)
                if pair_orb.get(key) == j:
                    Aj[p, q] = 1.0
                    Aj[q, p] = 1.0
        A_list.append((K + j, Aj))
    
    return A_0, A_list

def build_lp_constraints(records, pt_orb, orbits, pair_orb, n_pair_orbs, pair_ep, pair_sizes):
    """Build orbit-averaged Wang RLT constraints. Returns A_eq, b_eq, A_ub, b_ub."""
    K = len(orbits); M_p = n_pair_orbs; N = K + M_p
    reps = [orb[0] for orb in orbits]
    sizes = [len(o) for o in orbits]
    
    # Pair-cardinality coefficients
    n_aj = [[0]*M_p for _ in range(K)]
    for a in range(K):
        p = reps[a]
        for q in range(1,256):
            if q==p: continue
            key = (min(p,q),max(p,q))
            n_aj[a][pair_orb[key]] += 1
    
    eq_rows=[]; eq_b=[]
    ub_rows=[]; ub_b=[]
    
    # Cardinality
    row=[0.0]*N
    for a in range(K): row[a]=float(sizes[a])
    eq_rows.append(row); eq_b.append(19.0)
    
    # Pair cardinality
    for a in range(K):
        row=[0.0]*N; row[a]=-18.0
        for j in range(M_p): row[K+j]=float(n_aj[a][j])
        eq_rows.append(row); eq_b.append(0.0)
    
    # Pair upper bounds
    for j in range(M_p):
        al,be = pair_ep[j]
        r1=[0.0]*N; r1[K+j]=1.0; r1[al]=-1.0; ub_rows.append(r1); ub_b.append(0.0)
        if be!=al:
            r2=[0.0]*N; r2[K+j]=1.0; r2[be]=-1.0; ub_rows.append(r2); ub_b.append(0.0)
    
    # McCormick
    for j in range(M_p):
        al,be = pair_ep[j]
        r=[0.0]*N; r[al]+=1.0; r[be]+=1.0; r[K+j]=-1.0
        ub_rows.append(r); ub_b.append(1.0)
    
    # Wang first-order + RLT
    seen = set()
    for ri, rec in enumerate(records):
        bs = int(rec["point_bitset"])
        L = int(rec["L"])
        cap = 19 - L
        if cap <= 0: continue
        
        pts = []
        tmp = bs
        while tmp:
            bit = tmp & -tmp; pts.append(bit.bit_length()-1); tmp ^= bit
        
        # orbit coefficient
        occ = [0]*K
        for p in pts:
            if 1 <= p <= 255:
                occ[pt_orb[p]] += 1
        
        # First order
        coef = tuple(occ[a]/sizes[a] for a in range(K))
        key = (coef, float(cap))
        if key not in seen:
            seen.add(key)
            row = [0.0]*N
            for a in range(K): row[a] = occ[a] / sizes[a]
            ub_rows.append(row); ub_b.append(float(cap))
        
        # RLT: multiply by x_a and (1-x_a) for each orbit rep
        for a in range(K):
            rep = reps[a]
            if rep in pts:
                # x_rep is in subspace: Σ_{q in S} y_{rep,q} <= cap * x_rep
                rlt_occ_y = [0]*M_p
                for q in pts:
                    if 1<=q<=255 and q!=rep:
                        key2 = (min(rep,q),max(rep,q))
                        rlt_occ_y[pair_orb[key2]] += 1
                coef_rlt = [0.0]*N
                coef_rlt[a] = -float(cap)
                for j in range(M_p):
                    coef_rlt[K+j] = rlt_occ_y[j] / pair_sizes[j]
                tup = (tuple(coef_rlt), 0.0)
                if tup not in seen:
                    seen.add(tup)
                    ub_rows.append(coef_rlt); ub_b.append(0.0)
            else:
                # x_rep not in subspace: Σ_{q in S}(x_q - y_{rep,q}) <= cap*(1-x_rep)
                rlt_occ = [0.0]*N
                for q in pts:
                    if 1<=q<=255:
                        rlt_occ[pt_orb[q]] += 1.0/sizes[pt_orb[q]]
                        key2 = (min(rep,q),max(rep,q))
                        rlt_occ[K+pair_orb[key2]] -= 1.0/pair_sizes[pair_orb[key2]]
                rlt_occ[a] += float(cap)
                tup = (tuple(rlt_occ), float(cap))
                if tup not in seen:
                    seen.add(tup)
                    ub_rows.append(list(rlt_occ)); ub_b.append(float(cap))
    
    return (np.array(eq_rows), np.array(eq_b),
            np.array(ub_rows), np.array(ub_b))

# ── Main ────────────────────────────────────────────────────────────────

def main():
    import pickle
    t0 = time.time()
    print("analysis: Orbit-averaged SDP for E11 distinct-support branch")
    
    # 1. Build orbit infrastructure
    print("  1. Building stabilizer...")
    perms = build_stabilizer()
    G = perms.shape[0]
    print(f"     |G| = {G} ({time.time()-t0:.1f}s)")
    
    pt_orb, orbits = compute_point_orbits(perms)
    K = len(orbits)
    sizes = [len(o) for o in orbits]
    reps = [o[0] for o in orbits]
    print(f"     Point orbits: {K}, sizes {sizes}, reps {reps}")
    
    pair_orb, pair_sizes, pair_ep, M_p = compute_pair_orbits(perms, pt_orb)
    print(f"     {M_p} pair orbits ({time.time()-t0:.1f}s)")
    
    # 2. Load Wang table
    print("  2. Loading Wang table...")
    LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
    from core_capacity_from_wang_lut import CoreQuotient, load_lut
    from complete_core_and_transversal import build_core_constraints
    lut, _meta = load_lut(LUT_PATH)
    core = CoreQuotient(pivot=1)
    records, stats = build_core_constraints(core, lut)
    print(f"     {len(records)} records ({time.time()-t0:.1f}s)")
    
    # 3. Build LP constraints
    print("  3. Building LP constraints...")
    A_eq, b_eq, A_ub, b_ub = build_lp_constraints(
        records, pt_orb, orbits, pair_orb, M_p, pair_ep, pair_sizes)
    N = K + M_p
    print(f"     {A_eq.shape[0]} eq, {A_ub.shape[0]} ub constraints ({time.time()-t0:.1f}s)")
    
    # 4. Build coefficient matrices for 256×256 moment matrix
    print("  4. Building moment matrix coefficients...")
    # More efficient: build point and pair lookup arrays
    # pt_orb_arr[p] = orbit index for p ∈ {1,...,255}
    pt_orb_arr = np.array([pt_orb[p] for p in range(256)])
    
    # pair_orb_arr[(p,q)] already available as pair_orb dict
    # We'll construct M on the fly during SDP
    
    print(f"     Ready ({time.time()-t0:.1f}s)")
    
    # 5. Solve continuous SDP using cvxpy
    print("  5. Formulating and solving continuous SDP...")
    import cvxpy as cp
    
    z = cp.Variable(N)  # z = (x_0,...,x_{K-1}, y_0,...,y_{M_p-1})
    
    # Build moment matrix M as function of z
    # M is 256×256, with M[i,j] linear in z
    # Efficient construction: build A_0 and A_k for each variable k
    
    # A_0 = constant part
    A0_dense = np.zeros((256, 256))
    A0_dense[0, 0] = 1.0
    
    # For each point orbit a: x_a contributes to M[0,p], M[p,0], M[p,p]
    # For each pair orbit j: y_j contributes to M[p,q], M[q,p]
    # Total: K + M_p = 103 coefficient matrices
    
    # Build as: M_expr = A0 + sum_k z[k] * Ak
    # This is expensive in cvxpy but works for 256×256
    
    # Alternative: build M element by element using indexing
    # M_expr[0,0] = 1
    # M_expr[0,p] = z[pt_orb[p]]
    # M_expr[p,p] = z[pt_orb[p]]  
    # M_expr[p,q] = z[K + pair_orb[(p,q)]]
    
    # Use the coefficient matrix approach
    Ak_list = []  # (var_idx, dense_matrix)
    
    for a in range(K):
        Aa = np.zeros((256, 256))
        for p in orbits[a]:
            Aa[0, p] = 1.0
            Aa[p, 0] = 1.0
            Aa[p, p] = 1.0
        Ak_list.append((a, Aa))
    
    print(f"     Building pair coefficient matrices...")
    t_pair = time.time()
    # Single pass: build all pair matrices simultaneously
    pair_mats = [np.zeros((256, 256)) for _ in range(M_p)]
    for p in range(1, 256):
        for q in range(p+1, 256):
            j = pair_orb[(p,q)]
            pair_mats[j][p, q] = 1.0
            pair_mats[j][q, p] = 1.0
    for j in range(M_p):
        Ak_list.append((K + j, pair_mats[j]))
    del pair_mats
    print(f"     Pair matrices built ({time.time()-t_pair:.1f}s)")
    
    # Build M expression using vectorized matrix sum
    # Stack all coefficient matrices into a 3D array: coef_stack[k] = Ak
    # M = A0 + sum(z[k] * coef_stack[k])
    n_vars = len(Ak_list)
    coef_stack = np.zeros((n_vars, 256, 256))
    var_indices = []
    for idx, (var_idx, Ak) in enumerate(Ak_list):
        coef_stack[idx] = Ak
        var_indices.append(var_idx)
    
    # Reshape for vectorized multiplication: M = A0 + z_mapped @ coef_flat
    # coef_flat: (N, 256*256), z_mapped: (N,)
    coef_flat = coef_stack.reshape(n_vars, 256*256)  # (103, 65536)
    
    # z_mapped[idx] = z[var_indices[idx]]
    # Build a mapping matrix: z_mapped = P @ z where P is n_vars × N
    P = np.zeros((n_vars, N))
    for idx, vi in enumerate(var_indices):
        P[idx, vi] = 1.0
    
    # M_flat = A0_flat + (P @ z) @ coef_flat
    A0_flat = A0_dense.reshape(256*256)
    
    # cvxpy expression
    z_mapped = P @ z  # (n_vars,)
    M_flat_expr = cp.Constant(A0_flat) + coef_flat.T @ z_mapped  # (65536,)
    M_expr = cp.reshape(M_flat_expr, (256, 256))
    
    print(f"     M expression built ({time.time()-t0:.1f}s)")
    
    # Constraints
    constraints = [
        M_expr >> 0,  # PSD
        z >= 0,
        z <= 1,
        A_eq @ z == b_eq,   # equalities (vectorized)
        A_ub @ z <= b_ub,   # inequalities (vectorized)
    ]
    
    # Solve for feasibility first
    prob = cp.Problem(cp.Minimize(0), constraints)
    print(f"     Solving with CLARABEL...")
    t_solve = time.time()
    prob.solve(solver='CLARABEL', verbose=True, max_iter=500)
    solve_time = time.time() - t_solve
    print(f"     Status: {prob.status} ({solve_time:.1f}s)")
    
    sdp_result = {
        "continuous_sdp_status": prob.status,
        "continuous_sdp_solve_sec": solve_time,
    }
    
    if prob.status in ('optimal', 'optimal_inaccurate'):
        z_val = z.value
        x_val = z_val[:K]
        y_val = z_val[K:]
        n_mass = [float(x_val[a] * sizes[a]) for a in range(K)]
        
        # Check moment matrix eigenvalues at solution
        M_val = A0_dense.copy()
        for var_idx, Ak in Ak_list:
            M_val += z_val[var_idx] * Ak
        eigs = np.linalg.eigvalsh(M_val)
        
        sdp_result["continuous_sdp_n_mass"] = n_mass
        sdp_result["continuous_sdp_x"] = [float(v) for v in x_val]
        sdp_result["continuous_sdp_min_eig"] = float(eigs[0])
        sdp_result["continuous_sdp_total"] = float(sum(n_mass))
        print(f"     n_mass = {[f'{v:.4f}' for v in n_mass]}")
        print(f"     total = {sum(n_mass):.6f}")
        print(f"     min eigenvalue = {eigs[0]:.8f}")
    
    # 6. Test specific integer count vectors from analysis
    print("\n  6. Testing integer count vectors with SDP...")
    test_vectors = [
        ("feasibility_lex", [3, 0, 0, 3, 0, 13]),
        ("max_omitted", [6, 0, 11, 2, 0, 0]),
        ("min_omitted", [0, 0, 0, 0, 2, 17]),
        ("force_zero_omitted", [0, 0, 0, 0, 2, 17]),
        ("near", [0, 0, 0, 0, 3, 16]),
        ("all_orbit5", [0, 0, 0, 0, 0, 19]),
    ]
    
    int_results = []
    for label, n_vec in test_vectors:
        if sum(n_vec) != 19:
            continue
        # Check orbit size compatibility
        ok = all(n_vec[a] <= sizes[a] for a in range(K))
        if not ok:
            int_results.append({"label": label, "n": n_vec, "status": "orbit_overflow"})
            continue
        
        # Fix x_a = n_a / |O_a|
        z_int = cp.Variable(N)
        constraints_int = [
            z_int >= 0,
            z_int <= 1,
        ]
        for a in range(K):
            constraints_int.append(z_int[a] == n_vec[a] / sizes[a])
        
        # LP constraints (vectorized)
        constraints_int.append(A_eq @ z_int == b_eq)
        constraints_int.append(A_ub @ z_int <= b_ub)
        
        # PSD
        z_int_mapped = P @ z_int
        M_int_flat = cp.Constant(A0_flat) + coef_flat.T @ z_int_mapped
        M_int_expr = cp.reshape(M_int_flat, (256, 256))
        constraints_int.append(M_int_expr >> 0)
        
        prob_int = cp.Problem(cp.Minimize(0), constraints_int)
        t_int = time.time()
        prob_int.solve(solver='CLARABEL', verbose=False, max_iter=500)
        int_time = time.time() - t_int
        
        res = {
            "label": label,
            "n": n_vec,
            "status": prob_int.status,
            "solve_sec": round(int_time, 3),
        }
        
        if prob_int.status in ('optimal', 'optimal_inaccurate'):
            zv = z_int.value
            Mv = A0_dense.copy()
            for idx_k, (vi, Ak) in enumerate(Ak_list):
                Mv += zv[vi] * Ak
            eigs = np.linalg.eigvalsh(Mv)
            res["min_eig"] = float(eigs[0])
            res["m_total"] = float(sum(zv[K:] * np.array(pair_sizes)))
            print(f"     {label} n={n_vec}: FEASIBLE, min_eig={eigs[0]:.6f}, m={res['m_total']:.1f} ({int_time:.1f}s)")
        else:
            print(f"     {label} n={n_vec}: {prob_int.status} ({int_time:.1f}s)")
        
        int_results.append(res)
    
    sdp_result["integer_count_tests"] = int_results
    
    # 7. Save results
    sdp_result["elapsed_sec"] = time.time() - t0
    sdp_result["schema"] = "orbit_sdp_v1"
    sdp_result["point_orbit_sizes"] = sizes
    sdp_result["point_orbit_reps"] = reps
    sdp_result["n_pair_orbits"] = M_p
    
    out_path = OUT / "orbit_sdp_result.json"
    out_path.write_text(json.dumps(sdp_result, indent=2) + "\n")
    print(f"\n  Saved: {out_path}")
    print(f"  Total elapsed: {time.time()-t0:.1f}s")

if __name__ == "__main__":
    main()
