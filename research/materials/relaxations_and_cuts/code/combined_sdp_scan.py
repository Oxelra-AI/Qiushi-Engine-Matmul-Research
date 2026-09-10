#!/usr/bin/env python3
"""analysis: Orbit-averaged SDP + count-vector scan, matching analysis LP exactly.

Uses raw integer orbit/pair counts as coefficients (not normalized by sizes),
which deduplicates to ~183K constraints like analysis.
"""
from __future__ import annotations
import numpy as np, json, time, sys, pickle
from pathlib import Path
from itertools import product as iproduct

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

OUT_SDP = ROOT / "workspace/data/orbit_sdp"
OUT_SCAN = ROOT / "workspace/data/count_vector_scan"
OUT_SDP.mkdir(parents=True, exist_ok=True)
OUT_SCAN.mkdir(parents=True, exist_ok=True)

# ── F2 / stabilizer / orbits (from analysis) ─────────────────────────────

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

def build_stabilizer():
    stab = []
    for entries in iproduct(range(2), repeat=9):
        M = np.array(entries, dtype=np.uint8).reshape(3,3)
        if M[0,0]!=1 or M[1,0]!=0 or M[2,0]!=0: continue
        if int(round(np.linalg.det(M.astype(float)))) % 2 != 1: continue
        stab.append(M)
    all_perms = set()
    for P in stab:
        for Q in stab:
            pd = [0]*256; pt = [0]*256
            for p in range(256):
                M = _MATS[p]
                Md = (P.astype(int)@M.astype(int)@Q.T.astype(int))%2; Md[0,0]=0
                pd[p] = _mat_to_int(Md)
                Mt = (Q.astype(int)@M.T.astype(int)@P.T.astype(int))%2; Mt[0,0]=0
                pt[p] = _mat_to_int(Mt)
            all_perms.add(tuple(pd)); all_perms.add(tuple(pt))
    return np.array(list(all_perms), dtype=np.uint16)

def compute_point_orbits(perms):
    par = list(range(256))
    def find(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    def union(a,b):
        a,b=find(a),find(b); 
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
        pair_orb[(p,q)] = oid; pair_sizes[oid] += 1
        if pair_ep[oid] is None:
            a,b = pt_orb[p], pt_orb[q]
            pair_ep[oid] = (min(a,b), max(a,b))
    return pair_orb, pair_sizes, pair_ep, M

# ── LP builder matching analysis EXACTLY ──────────────────────────────────

def build_lp(records, pt_orb, orbits, pair_orb, pair_sizes, pair_ep, M_p):
    """Build orbit-averaged LP with RAW integer coefficients (analysis style)."""
    K = len(orbits); N = K + M_p
    reps = [orb[0] for orb in orbits]
    sizes = [len(o) for o in orbits]
    
    # Pair-cardinality
    n_aj = [[0]*M_p for _ in range(K)]
    for a in range(K):
        p = reps[a]
        for q in range(1,256):
            if q==p: continue
            n_aj[a][pair_orb[(min(p,q),max(p,q))]] += 1
    
    eq_A=[]; eq_b=[]; ub_A=[]; ub_b=[]
    
    # Cardinality Σ|O_a|x_a = 19
    row=[0.0]*N
    for a in range(K): row[a]=float(sizes[a])
    eq_A.append(row); eq_b.append(19.0)
    
    # Pair cardinality: Σ n_aj y_j - 18 x_a = 0
    for a in range(K):
        row=[0.0]*N; row[a]=-18.0
        for j in range(M_p): row[K+j]=float(n_aj[a][j])
        eq_A.append(row); eq_b.append(0.0)
    
    # Pair bounds y_j ≤ x_a, y_j ≤ x_b
    for j in range(M_p):
        al,be = pair_ep[j]
        r1=[0.0]*N; r1[K+j]=1.0; r1[al]=-1.0; ub_A.append(r1); ub_b.append(0.0)
        if be!=al:
            r2=[0.0]*N; r2[K+j]=1.0; r2[be]=-1.0; ub_A.append(r2); ub_b.append(0.0)
    
    # McCormick: x_a + x_b - y_j ≤ 1
    for j in range(M_p):
        al,be = pair_ep[j]
        r=[0.0]*N; r[al]+=1.0; r[be]+=1.0; r[K+j]=-1.0
        ub_A.append(r); ub_b.append(1.0)
    
    # Wang + RLT — matching analysis lines 164-229 EXACTLY
    seen = set()
    wang_ct = 0
    for ri, rec in enumerate(records):
        bs = int(rec["point_bitset"]); L = int(rec["L"])
        cap = 19 - L
        if cap <= 0: continue
        pts = []
        tmp = bs
        while tmp:
            bit = tmp & -tmp; pts.append(bit.bit_length()); tmp ^= bit  # 1-indexed
        
        n_orb = [0]*K
        for p in pts: n_orb[pt_orb[p]] += 1
        
        # First-order: Σ n_orb[a] x_a ≤ cap  (RAW integer coefficients)
        coef_fo = tuple([float(n_orb[a]) for a in range(K)] + [0.0]*M_p)
        key = (coef_fo, float(cap))
        if key not in seen:
            seen.add(key); ub_A.append(list(coef_fo)); ub_b.append(float(cap))
            wang_ct += 1
        
        # RLT for each orbit rep
        for a in range(K):
            pa = reps[a]
            in_S = (bs >> (pa - 1)) & 1
            c_eff = cap - in_S
            
            mj = [0]*M_p
            for q in pts:
                if q == pa: continue
                mj[pair_orb[(min(pa,q),max(pa,q))]] += 1
            
            # x_p side: Σ mj y_j - c_eff x_a ≤ 0
            coef_xp = [0.0]*N; coef_xp[a] = -float(c_eff)
            for j in range(M_p):
                if mj[j]: coef_xp[K+j] = float(mj[j])
            key_xp = (tuple(coef_xp), 0.0)
            if key_xp not in seen:
                seen.add(key_xp); ub_A.append(coef_xp); ub_b.append(0.0)
                wang_ct += 1
            
            # (1-x_p) side: Σ(n_orb+c_eff δ)x - Σ mj y ≤ cap
            coef_1xp = [0.0]*N
            for i in range(K): coef_1xp[i] = float(n_orb[i])
            coef_1xp[a] += float(c_eff)
            for j in range(M_p):
                if mj[j]: coef_1xp[K+j] = -float(mj[j])
            key_1xp = (tuple(coef_1xp), float(cap))
            if key_1xp not in seen:
                seen.add(key_1xp); ub_A.append(coef_1xp); ub_b.append(float(cap))
                wang_ct += 1
        
        if ri > 0 and ri % 100000 == 0:
            print(f"      processed {ri}/{len(records)}, {wang_ct} unique Wang", flush=True)
    
    print(f"    Wang constraints: {wang_ct} unique", flush=True)
    A_eq = np.array(eq_A); b_eq_arr = np.array(eq_b)
    A_ub = np.array(ub_A); b_ub_arr = np.array(ub_b)
    print(f"    Total: {A_eq.shape[0]} eq + {A_ub.shape[0]} ub", flush=True)
    return A_eq, b_eq_arr, A_ub, b_ub_arr, K, N

# ── Moment matrix PSD ───────────────────────────────────────────────────

def check_moment_psd(n_vec, y_vals, sizes, orbits, pair_orb, pair_sizes, M_p):
    K = len(orbits)
    x_vals = np.zeros(256)
    for a in range(K):
        for p in orbits[a]: x_vals[p] = n_vec[a] / sizes[a] if sizes[a] else 0.0
    M = np.zeros((256, 256))
    M[0, 0] = 1.0
    for p in range(1, 256):
        M[0, p] = M[p, 0] = M[p, p] = x_vals[p]
    for p in range(1, 256):
        for q in range(p+1, 256):
            v = y_vals[pair_orb[(p, q)]]
            M[p, q] = M[q, p] = v
    eigs = np.linalg.eigvalsh(M)
    return float(eigs[0]), int(np.sum(eigs < -1e-10))

# ── Main ─────────────────────────────────────────────────────────────────

def main():
    from scipy.optimize import linprog
    t0 = time.time()
    print("analysis: Combined SDP + count-vector scan (analysis-matched LP)", flush=True)
    
    # 1. Infrastructure
    print("  1. Building stabilizer...", flush=True)
    perms = build_stabilizer()
    pt_orb, orbits = compute_point_orbits(perms)
    K = len(orbits); sizes = [len(o) for o in orbits]
    reps = [o[0] for o in orbits]
    pair_orb, pair_sizes, pair_ep, M_p = compute_pair_orbits(perms, pt_orb)
    print(f"     |G|={perms.shape[0]}, K={K}, sizes={sizes}, M_p={M_p} ({time.time()-t0:.1f}s)", flush=True)
    
    # 2. Wang table
    print("  2. Loading Wang table...", flush=True)
    from core_capacity_from_wang_lut import CoreQuotient, load_lut
    from complete_core_and_transversal import build_core_constraints
    LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
    lut, _ = load_lut(LUT_PATH)
    core = CoreQuotient(pivot=1)
    records, stats = build_core_constraints(core, lut)
    print(f"     {len(records)} records ({time.time()-t0:.1f}s)", flush=True)
    
    # 3. Build LP (analysis style)
    print("  3. Building LP (analysis style)...", flush=True)
    A_eq, b_eq, A_ub, b_ub, K, N = build_lp(
        records, pt_orb, orbits, pair_orb, pair_sizes, pair_ep, M_p)
    print(f"     ({time.time()-t0:.1f}s)", flush=True)
    
    # 4. Split for count-vector scan
    A_eq_x = A_eq[:, :K]; A_eq_y = A_eq[:, K:]
    A_ub_x = A_ub[:, :K]; A_ub_y = A_ub[:, K:]
    
    # 5. Scan all count vectors
    print("  5. Scanning count vectors...", flush=True)
    lp_feasible = []; lp_infeasible = 0; total = 0
    t_scan = time.time()
    
    for n0 in range(min(sizes[0], 19)+1):
      for n1 in range(min(sizes[1], 19-n0)+1):
        for n2 in range(min(sizes[2], 19-n0-n1)+1):
          for n3 in range(min(sizes[3], 19-n0-n1-n2)+1):
            rem = 19-n0-n1-n2-n3
            for n4 in range(min(sizes[4], rem)+1):
              n5 = rem - n4
              if n5 < 0 or n5 > sizes[5]: continue
              total += 1
              nvec = [n0,n1,n2,n3,n4,n5]
              x_fixed = np.array([nvec[a]/sizes[a] for a in range(K)])
              beq_adj = b_eq - A_eq_x @ x_fixed
              bub_adj = b_ub - A_ub_x @ x_fixed
              res = linprog(np.zeros(M_p), A_ub=A_ub_y, b_ub=bub_adj,
                           A_eq=A_eq_y, b_eq=beq_adj,
                           bounds=[(0,1)]*M_p, method='highs')
              if res.success:
                  lp_feasible.append((nvec, res.x))
              else:
                  lp_infeasible += 1
      if total % 5000 < 200 and total > 200:
          print(f"     {total} tested, {len(lp_feasible)} feasible ({time.time()-t_scan:.1f}s)", flush=True)
    
    print(f"     DONE: {total} vectors, {len(lp_feasible)} LP-feasible, {lp_infeasible} infeasible ({time.time()-t0:.1f}s)", flush=True)
    
    # 6. PSD check for LP-feasible vectors
    print(f"  6. PSD check for {len(lp_feasible)} LP-feasible vectors...", flush=True)
    psd_ok = []; psd_violated = []
    for fi, (nvec, y_vals) in enumerate(lp_feasible):
        min_eig, n_neg = check_moment_psd(nvec, y_vals, sizes, orbits, pair_orb, pair_sizes, M_p)
        entry = {"n": nvec, "min_eig": min_eig, "n_neg": n_neg}
        if min_eig >= -1e-8:
            psd_ok.append(entry)
        else:
            psd_violated.append(entry)
        if fi % 500 == 0 and fi > 0:
            print(f"     {fi}/{len(lp_feasible)}, ok={len(psd_ok)}, viol={len(psd_violated)}", flush=True)
    
    print(f"     PSD: {len(psd_ok)} ok, {len(psd_violated)} violated ({time.time()-t0:.1f}s)", flush=True)
    
    # 7. SDP for selected PSD-violated vectors (test if SDP-feasible y exists)
    sdp_results = []
    if psd_violated and len(psd_violated) <= 50:
        print(f"  7. SDP check for {len(psd_violated)} PSD-violated vectors...", flush=True)
        try:
            import cvxpy as cp
            # Build coefficient matrices for 256×256 moment matrix
            coef_mats = []
            for a in range(K):
                Aa = np.zeros((256, 256))
                for p in orbits[a]:
                    Aa[0,p] = Aa[p,0] = Aa[p,p] = 1.0
                coef_mats.append((a, Aa))
            pair_mat_list = [np.zeros((256, 256)) for _ in range(M_p)]
            for p in range(1, 256):
                for q in range(p+1, 256):
                    j = pair_orb[(p, q)]
                    pair_mat_list[j][p,q] = pair_mat_list[j][q,p] = 1.0
            for j in range(M_p):
                coef_mats.append((K+j, pair_mat_list[j]))
            del pair_mat_list
            
            A0 = np.zeros((256,256)); A0[0,0] = 1.0
            n_cm = len(coef_mats)
            coef_stack = np.zeros((n_cm, 256*256))
            for idx, (vi, Ak) in enumerate(coef_mats):
                coef_stack[idx] = Ak.ravel()
            
            for vi_rec in psd_violated[:20]:
                nvec = vi_rec["n"]
                x_fixed = np.array([nvec[a]/sizes[a] for a in range(K)])
                
                z = cp.Variable(N)
                # Fix x variables
                constraints = [z >= 0, z <= 1]
                for a in range(K):
                    constraints.append(z[a] == x_fixed[a])
                constraints.append(A_eq @ z == b_eq)
                constraints.append(A_ub @ z <= b_ub)
                
                # PSD
                z_full = z  # length N=103
                M_flat = cp.Constant(A0.ravel()) + coef_stack.T @ z_full
                M_expr = cp.reshape(M_flat, (256, 256), order='C')
                constraints.append(M_expr >> 0)
                
                prob = cp.Problem(cp.Minimize(0), constraints)
                t_sdp = time.time()
                prob.solve(solver='CLARABEL', verbose=False, max_iter=200)
                sdp_time = time.time() - t_sdp
                
                sdp_results.append({
                    "n": nvec, "sdp_status": prob.status, "sdp_sec": round(sdp_time, 2)
                })
                print(f"     n={nvec}: SDP {prob.status} ({sdp_time:.1f}s)", flush=True)
        except Exception as e:
            print(f"     SDP error: {e}", flush=True)
    
    # 8. Save
    payload = {
        "schema": "combined_scan_v1",
        "elapsed_sec": time.time() - t0,
        "total_count_vectors": total,
        "lp_feasible_count": len(lp_feasible),
        "lp_infeasible_count": lp_infeasible,
        "n_eq_constraints": int(A_eq.shape[0]),
        "n_ub_constraints": int(A_ub.shape[0]),
        "psd_ok_count": len(psd_ok),
        "psd_violated_count": len(psd_violated),
        "psd_ok_vectors": [r["n"] for r in psd_ok[:100]],
        "psd_ok_min_eigs": [r["min_eig"] for r in psd_ok[:100]],
        "psd_violated_vectors": [{"n":r["n"], "min_eig":r["min_eig"]} for r in psd_violated[:100]],
        "sdp_results": sdp_results,
    }
    out_path = OUT_SCAN / "combined_scan.json"
    out_path.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"\n  Saved: {out_path}", flush=True)
    print(f"\n  === SUMMARY ===", flush=True)
    print(f"  Count vectors:    {total}", flush=True)
    print(f"  LP feasible:      {len(lp_feasible)}", flush=True)
    print(f"  LP+PSD(LP y) ok:  {len(psd_ok)}", flush=True)
    print(f"  LP+PSD unclear:   {len(psd_violated)}", flush=True)
    print(f"  SDP tested:       {len(sdp_results)}", flush=True)

if __name__ == "__main__":
    main()
