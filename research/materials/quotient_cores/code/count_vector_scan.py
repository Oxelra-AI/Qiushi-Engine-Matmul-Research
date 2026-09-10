#!/usr/bin/env python3
"""analysis: Comprehensive LP scan of all 34,335 integer count vectors.

For each (n_0,...,n_5) with Σn_a=19, n_a≤|O_a|, fix x_a=n_a/|O_a| 
and test whether the 97-variable LP for pair values y_j is feasible
under all Wang RLT constraints.

Then for LP-feasible vectors, construct the 256×256 moment matrix and
check PSD (via eigenvalues). This is a fast proxy for the full SDP:
the LP-optimal y_j may not be PSD-optimal, but if the LP optimum 
already violates PSD, it's informative.
"""
from __future__ import annotations
import numpy as np, json, time, sys
from pathlib import Path
from itertools import product as iproduct
from scipy.optimize import linprog

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

OUT = ROOT / "workspace/data/count_vector_scan"
OUT.mkdir(parents=True, exist_ok=True)

# ── F2 helpers (shared) ─────────────────────────────────────────────────

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

# ── Build LP in y-only form for fixed n ─────────────────────────────────

def build_fixed_n_lp(n_vec, sizes, orbits, pair_orb, pair_sizes, pair_ep, 
                     M_p, records, pt_orb):
    """Build LP: min 0 s.t. Wang RLT constraints, with x_a = n_a/|O_a| fixed.
    
    Returns A_ub, b_ub, A_eq, b_eq, bounds for scipy.linprog in 97 y variables.
    """
    K = len(orbits)
    reps = [o[0] for o in orbits]
    x_fixed = [n_vec[a] / sizes[a] if sizes[a] > 0 else 0.0 for a in range(K)]
    
    # Pair-cardinality coefficients
    n_aj = [[0]*M_p for _ in range(K)]
    for a in range(K):
        p = reps[a]
        for q in range(1,256):
            if q==p: continue
            key = (min(p,q),max(p,q))
            n_aj[a][pair_orb[key]] += 1
    
    eq_rows = []; eq_b = []
    ub_rows = []; ub_b = []
    
    # Pair cardinality: Σ_j n_aj y_j = 18 x_a for each a
    for a in range(K):
        row = [0.0]*M_p
        for j in range(M_p):
            row[j] = float(n_aj[a][j])
        eq_rows.append(row)
        eq_b.append(18.0 * x_fixed[a])
    
    # Pair upper bounds: y_j ≤ x_a, y_j ≤ x_b
    for j in range(M_p):
        al, be = pair_ep[j]
        r1 = [0.0]*M_p; r1[j] = 1.0
        ub_rows.append(r1); ub_b.append(x_fixed[al])
        if be != al:
            r2 = [0.0]*M_p; r2[j] = 1.0
            ub_rows.append(r2); ub_b.append(x_fixed[be])
    
    # McCormick: y_j ≥ x_a + x_b - 1, i.e., -y_j ≤ 1 - x_a - x_b
    for j in range(M_p):
        al, be = pair_ep[j]
        r = [0.0]*M_p; r[j] = -1.0
        ub_rows.append(r); ub_b.append(1.0 - x_fixed[al] - x_fixed[be])
    
    # Wang RLT constraints (dedup)
    seen = set()
    for rec in records:
        bs = int(rec["point_bitset"])
        L = int(rec["L"])
        cap = 19 - L
        if cap <= 0: continue
        
        pts = []
        tmp = bs
        while tmp:
            bit = tmp & -tmp; pts.append(bit.bit_length()-1); tmp ^= bit
        
        occ = [0]*K
        for p in pts:
            if 1 <= p <= 255:
                occ[pt_orb[p]] += 1
        
        # First-order: Σ occ[a]/|O_a| * |O_a| * x_a ≤ cap
        # With x_a fixed, this becomes: Σ occ[a] * x_a ≤ cap
        # This is a constraint on x only, not y, so it either holds or not
        lhs_first = sum(occ[a] * x_fixed[a] for a in range(K))
        if lhs_first > cap + 1e-10:
            # Infeasible regardless of y
            return None, None, None, None, None  # INFEASIBLE
        
        # RLT with x_p (representative for each orbit)
        for a in range(K):
            rep = reps[a]
            if rep in pts:
                # Σ_{q in S} y_{rep,q} ≤ cap * x_a
                rlt_y = [0.0]*M_p
                for q in pts:
                    if 1<=q<=255 and q!=rep:
                        key2 = (min(rep,q),max(rep,q))
                        rlt_y[pair_orb[key2]] += 1.0 / pair_sizes[pair_orb[key2]]
                rhs = cap * x_fixed[a]
                tup = (tuple(rlt_y), rhs)
                if tup not in seen:
                    seen.add(tup)
                    ub_rows.append(rlt_y); ub_b.append(rhs)
            else:
                # Σ_{q in S}(x_q - y_{rep,q}) ≤ cap*(1-x_a)
                # i.e., Σ occ[b]*x_b - Σ y_{rep,q_in_S} ≤ cap - cap*x_a
                # i.e., -Σ y terms ≤ cap - cap*x_a - Σ occ*x
                rlt_y = [0.0]*M_p
                for q in pts:
                    if 1<=q<=255:
                        key2 = (min(rep,q),max(rep,q))
                        rlt_y[pair_orb[key2]] -= 1.0 / pair_sizes[pair_orb[key2]]
                rhs = cap * (1.0 - x_fixed[a]) - lhs_first
                tup = (tuple(rlt_y), rhs)
                if tup not in seen:
                    seen.add(tup)
                    ub_rows.append(rlt_y); ub_b.append(rhs)
    
    bounds = [(0.0, 1.0)]*M_p
    
    return (np.array(ub_rows) if ub_rows else np.empty((0,M_p)),
            np.array(ub_b) if ub_b else np.empty(0),
            np.array(eq_rows) if eq_rows else np.empty((0,M_p)),
            np.array(eq_b) if eq_b else np.empty(0),
            bounds)

def check_moment_psd(n_vec, y_vals, sizes, orbits, pair_orb, pair_sizes, pt_orb, M_p):
    """Construct 256×256 moment matrix and check eigenvalues."""
    K = len(orbits)
    x_vals = np.zeros(256)
    for a in range(K):
        val = n_vec[a] / sizes[a] if sizes[a] > 0 else 0.0
        for p in orbits[a]:
            x_vals[p] = val
    
    M = np.zeros((256, 256))
    M[0, 0] = 1.0
    for p in range(1, 256):
        M[0, p] = x_vals[p]
        M[p, 0] = x_vals[p]
        M[p, p] = x_vals[p]
    
    for p in range(1, 256):
        for q in range(p+1, 256):
            j = pair_orb[(p, q)]
            y_val = y_vals[j] if y_vals[j] is not None else 0.0
            M[p, q] = y_val
            M[q, p] = y_val
    
    eigs = np.linalg.eigvalsh(M)
    return float(eigs[0]), int(np.sum(eigs < -1e-10))

def main():
    t0 = time.time()
    print("analysis: Comprehensive LP + PSD count-vector scan")
    
    # 1. Build infrastructure
    print("  1. Building stabilizer...")
    perms = build_stabilizer()
    print(f"     |G| = {perms.shape[0]} ({time.time()-t0:.1f}s)")
    
    pt_orb, orbits = compute_point_orbits(perms)
    K = len(orbits)
    sizes = [len(o) for o in orbits]
    reps = [o[0] for o in orbits]
    print(f"     Point orbits: {K}, sizes {sizes}")
    
    pair_orb, pair_sizes, pair_ep, M_p = compute_pair_orbits(perms, pt_orb)
    print(f"     {M_p} pair orbits ({time.time()-t0:.1f}s)")
    
    # 2. Load Wang table
    print("  2. Loading Wang table...")
    import pickle
    LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
    from core_capacity_from_wang_lut import CoreQuotient, load_lut
    from complete_core_and_transversal import build_core_constraints
    lut, _meta = load_lut(LUT_PATH)
    core = CoreQuotient(pivot=1)
    records, stats = build_core_constraints(core, lut)
    print(f"     {len(records)} records ({time.time()-t0:.1f}s)")
    
    # 3. Enumerate count vectors
    print("  3. Enumerating count vectors...")
    count_vectors = []
    for n0 in range(min(sizes[0], 19)+1):
        for n1 in range(min(sizes[1], 19-n0)+1):
            for n2 in range(min(sizes[2], 19-n0-n1)+1):
                for n3 in range(min(sizes[3], 19-n0-n1-n2)+1):
                    rem = 19-n0-n1-n2-n3
                    for n4 in range(min(sizes[4], rem)+1):
                        n5 = rem - n4
                        if 0 <= n5 <= sizes[5]:
                            count_vectors.append((n0,n1,n2,n3,n4,n5))
    print(f"     {len(count_vectors)} count vectors")
    
    # 4. LP scan
    print("  4. LP feasibility scan...")
    lp_feasible = []
    lp_infeasible_first_order = 0
    lp_infeasible_rlt = 0
    
    for ci, nvec in enumerate(count_vectors):
        if ci % 5000 == 0 and ci > 0:
            print(f"     {ci}/{len(count_vectors)}, LP feasible so far: {len(lp_feasible)}")
        
        n_list = list(nvec)
        result = build_fixed_n_lp(n_list, sizes, orbits, pair_orb, pair_sizes,
                                  pair_ep, M_p, records, pt_orb)
        if result[0] is None:
            lp_infeasible_first_order += 1
            continue
        
        A_ub, b_ub, A_eq, b_eq, bounds = result
        
        # Solve LP
        c = np.zeros(M_p)  # feasibility only
        res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                     bounds=bounds, method='highs')
        
        if res.success:
            lp_feasible.append((n_list, res.x.tolist()))
        else:
            lp_infeasible_rlt += 1
    
    print(f"     LP scan complete: {len(lp_feasible)} feasible, "
          f"{lp_infeasible_first_order} first-order infeasible, "
          f"{lp_infeasible_rlt} RLT infeasible ({time.time()-t0:.1f}s)")
    
    # 5. PSD check for LP-feasible vectors
    print(f"  5. PSD check for {len(lp_feasible)} LP-feasible vectors...")
    psd_ok = []
    psd_violated = []
    
    for fi, (n_list, y_vals) in enumerate(lp_feasible):
        if fi % 100 == 0 and fi > 0:
            print(f"     {fi}/{len(lp_feasible)}, PSD ok: {len(psd_ok)}, violated: {len(psd_violated)}")
        
        min_eig, n_neg = check_moment_psd(n_list, y_vals, sizes, orbits,
                                          pair_orb, pair_sizes, pt_orb, M_p)
        
        if min_eig >= -1e-8:
            psd_ok.append({"n": n_list, "min_eig": min_eig, "n_neg": n_neg})
        else:
            psd_violated.append({"n": n_list, "min_eig": min_eig, "n_neg": n_neg})
    
    print(f"     PSD check complete: {len(psd_ok)} ok, {len(psd_violated)} violated ({time.time()-t0:.1f}s)")
    
    # Note: PSD check on LP-optimal y doesn't prove the count vector is PSD-infeasible
    # because a different y might satisfy both LP and PSD.
    # But PSD-ok with LP-optimal y IS a genuine feasible point for LP+PSD.
    
    # 6. Save results
    payload = {
        "schema": "count_vector_scan_v1",
        "elapsed_sec": time.time() - t0,
        "total_count_vectors": len(count_vectors),
        "lp_feasible": len(lp_feasible),
        "lp_infeasible_first_order": lp_infeasible_first_order,
        "lp_infeasible_rlt": lp_infeasible_rlt,
        "psd_ok_with_lp_y": len(psd_ok),
        "psd_violated_with_lp_y": len(psd_violated),
        "note": "PSD check uses LP-optimal y, not SDP-optimal y. "
                "psd_violated means LP y violates PSD, not that no PSD-feasible y exists. "
                "psd_ok means LP y is also PSD-feasible, so this count vector survives LP+PSD.",
        "psd_ok_vectors": psd_ok[:50],  # first 50
        "psd_violated_examples": psd_violated[:20],  # first 20
        "psd_ok_n_distribution": {},
    }
    
    # Distribution of PSD-ok vectors by orbit usage
    if psd_ok:
        for rec in psd_ok:
            key = str(rec["n"])
            payload["psd_ok_n_distribution"][key] = payload["psd_ok_n_distribution"].get(key, 0) + 1
    
    out_path = OUT / "count_vector_scan.json"
    out_path.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"\n  Saved: {out_path}")
    print(f"  Total: {time.time()-t0:.1f}s")
    
    # Summary
    print(f"\n  === SUMMARY ===")
    print(f"  Total count vectors: {len(count_vectors)}")
    print(f"  LP feasible:         {len(lp_feasible)}")
    print(f"  LP+PSD feasible:     {len(psd_ok)} (lower bound; more might survive with SDP-optimal y)")
    print(f"  LP+PSD unclear:      {len(psd_violated)} (LP y violates PSD, need SDP to check)")

if __name__ == "__main__":
    main()
