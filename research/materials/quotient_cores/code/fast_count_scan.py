#!/usr/bin/env python3
"""analysis: FAST comprehensive LP + PSD count-vector scan.

Build the orbit-averaged LP constraint matrix ONCE, then for each of the 
34,335 count vectors, fix x_a and solve the 97-variable y-only LP.
If LP-feasible, check moment matrix PSD.
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

# ── Reuse analysis infrastructure ─────────────────────────────────────────

def _int_to_mat(p):
    M = np.zeros((3,3), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            k = 3*i+j; 
            if k == 0: continue
            M[i,j] = (p >> (k-1)) & 1
    return M

_MATS = [_int_to_mat(p) for p in range(256)]

def _mat_to_int(M):
    p = 0
    for i in range(3):
        for j in range(3):
            k = 3*i+j; 
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

# ── Build FULL orbit-averaged LP (reuse analysis approach) ───────────────

def build_full_lp(records, pt_orb, orbits, pair_orb, pair_sizes, pair_ep, M_p):
    """Build the full 103-variable orbit-averaged LP. Returns A_eq,b_eq,A_ub,b_ub."""
    K = len(orbits); N = K + M_p
    reps = [orb[0] for orb in orbits]
    sizes = [len(o) for o in orbits]

    n_aj = [[0]*M_p for _ in range(K)]
    for a in range(K):
        p = reps[a]
        for q in range(1,256):
            if q==p: continue
            key = (min(p,q),max(p,q))
            n_aj[a][pair_orb[key]] += 1

    eq_A=[]; eq_b=[]
    ub_A=[]; ub_b=[]

    # Cardinality
    row=[0.0]*N
    for a in range(K): row[a]=float(sizes[a])
    eq_A.append(row); eq_b.append(19.0)

    # Pair cardinality
    for a in range(K):
        row=[0.0]*N; row[a]=-18.0
        for j in range(M_p): row[K+j]=float(n_aj[a][j])
        eq_A.append(row); eq_b.append(0.0)

    # Pair bounds
    for j in range(M_p):
        al,be = pair_ep[j]
        r1=[0.0]*N; r1[K+j]=1.0; r1[al]=-1.0; ub_A.append(r1); ub_b.append(0.0)
        if be!=al:
            r2=[0.0]*N; r2[K+j]=1.0; r2[be]=-1.0; ub_A.append(r2); ub_b.append(0.0)

    # McCormick
    for j in range(M_p):
        al,be = pair_ep[j]
        r=[0.0]*N; r[al]+=1.0; r[be]+=1.0; r[K+j]=-1.0
        ub_A.append(r); ub_b.append(1.0)

    # Wang first-order + RLT
    seen = set()
    for rec in records:
        bs = int(rec["point_bitset"]); L = int(rec["L"])
        cap = 19 - L
        if cap <= 0: continue
        pts = []
        tmp = bs
        while tmp:
            bit = tmp & -tmp; pts.append(bit.bit_length()-1); tmp ^= bit
        occ = [0]*K
        for p in pts:
            if 1<=p<=255: occ[pt_orb[p]] += 1

        # First order
        coef = [occ[a]/sizes[a] for a in range(K)]
        key_fo = (tuple(coef), float(cap))
        if key_fo not in seen:
            seen.add(key_fo)
            row = [0.0]*N
            for a in range(K): row[a] = occ[a]/sizes[a]
            ub_A.append(row); ub_b.append(float(cap))

        # RLT
        for a in range(K):
            rep = reps[a]
            if rep in pts:
                rlt_y = [0]*M_p
                for q in pts:
                    if 1<=q<=255 and q!=rep:
                        key2 = (min(rep,q),max(rep,q))
                        rlt_y[pair_orb[key2]] += 1
                coef_rlt = [0.0]*N
                coef_rlt[a] = -float(cap)
                for j in range(M_p):
                    coef_rlt[K+j] = rlt_y[j] / pair_sizes[j]
                tup = (tuple(coef_rlt), 0.0)
                if tup not in seen:
                    seen.add(tup); ub_A.append(coef_rlt); ub_b.append(0.0)
            else:
                rlt_occ = [0.0]*N
                for q in pts:
                    if 1<=q<=255:
                        rlt_occ[pt_orb[q]] += 1.0/sizes[pt_orb[q]]
                        key2 = (min(rep,q),max(rep,q))
                        rlt_occ[K+pair_orb[key2]] -= 1.0/pair_sizes[pair_orb[key2]]
                rlt_occ[a] += float(cap)
                tup = (tuple(rlt_occ), float(cap))
                if tup not in seen:
                    seen.add(tup); ub_A.append(list(rlt_occ)); ub_b.append(float(cap))

    return (np.array(eq_A), np.array(eq_b),
            np.array(ub_A), np.array(ub_b))

# ── Moment matrix PSD check ─────────────────────────────────────────────

def check_moment_psd(n_vec, y_vals, sizes, orbits, pair_orb, pair_sizes, pt_orb, M_p):
    K = len(orbits)
    x_vals = np.zeros(256)
    for a in range(K):
        val = n_vec[a] / sizes[a] if sizes[a] > 0 else 0.0
        for p in orbits[a]: x_vals[p] = val
    
    M = np.zeros((256, 256))
    M[0, 0] = 1.0
    for p in range(1, 256):
        M[0, p] = x_vals[p]; M[p, 0] = x_vals[p]; M[p, p] = x_vals[p]
    for p in range(1, 256):
        for q in range(p+1, 256):
            j = pair_orb[(p, q)]
            M[p, q] = y_vals[j]; M[q, p] = y_vals[j]
    eigs = np.linalg.eigvalsh(M)
    return float(eigs[0]), int(np.sum(eigs < -1e-10))

# ── Main ─────────────────────────────────────────────────────────────────

def main():
    t0 = time.time()
    print("analysis: FAST LP + PSD count-vector scan", flush=True)

    # 1. Build infrastructure
    print("  1. Building stabilizer...", flush=True)
    perms = build_stabilizer()
    pt_orb, orbits = compute_point_orbits(perms)
    K = len(orbits); sizes = [len(o) for o in orbits]
    pair_orb, pair_sizes, pair_ep, M_p = compute_pair_orbits(perms, pt_orb)
    print(f"     |G|={perms.shape[0]}, orbits={K}, sizes={sizes}, pairs={M_p} ({time.time()-t0:.1f}s)", flush=True)

    # 2. Load Wang table and build FULL LP
    print("  2. Loading Wang table...", flush=True)
    from core_capacity_from_wang_lut import CoreQuotient, load_lut
    from complete_core_and_transversal import build_core_constraints
    LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
    lut, _ = load_lut(LUT_PATH)
    core = CoreQuotient(pivot=1)
    records, stats = build_core_constraints(core, lut)
    print(f"     {len(records)} records ({time.time()-t0:.1f}s)", flush=True)

    print("  3. Building full LP...", flush=True)
    A_eq, b_eq, A_ub, b_ub = build_full_lp(
        records, pt_orb, orbits, pair_orb, pair_sizes, pair_ep, M_p)
    N = K + M_p
    n_eq = A_eq.shape[0]; n_ub = A_ub.shape[0]
    print(f"     {n_eq} eq, {n_ub} ub constraints ({time.time()-t0:.1f}s)", flush=True)

    # 3. Split into x-part and y-part
    # A_eq @ z = b_eq  →  A_eq_x @ x + A_eq_y @ y = b_eq
    # A_ub @ z <= b_ub  →  A_ub_y @ y <= b_ub - A_ub_x @ x
    A_eq_x = A_eq[:, :K]; A_eq_y = A_eq[:, K:]
    A_ub_x = A_ub[:, :K]; A_ub_y = A_ub[:, K:]

    # 4. Enumerate and test count vectors
    print("  4. Enumerating and testing count vectors...", flush=True)
    lp_feasible = []; lp_infeasible = 0; first_order_fail = 0
    total = 0

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
                        
                        # Adjust equality: A_eq_y @ y = b_eq - A_eq_x @ x
                        beq_adj = b_eq - A_eq_x @ x_fixed
                        # Adjust inequality: A_ub_y @ y <= b_ub - A_ub_x @ x
                        bub_adj = b_ub - A_ub_x @ x_fixed
                        
                        # Quick check: any adjusted bound negative with no y contribution?
                        # (first-order constraints have zero y-columns)
                        
                        # Solve 97-variable LP
                        c = np.zeros(M_p)
                        res = linprog(c, A_ub=A_ub_y, b_ub=bub_adj,
                                     A_eq=A_eq_y, b_eq=beq_adj,
                                     bounds=[(0.0, 1.0)]*M_p, method='highs')
                        
                        if res.success:
                            lp_feasible.append((nvec, res.x))
                        else:
                            lp_infeasible += 1

            if total % 5000 < 100 and total > 100:
                print(f"     tested {total}, LP feasible: {len(lp_feasible)}, infeasible: {lp_infeasible}", flush=True)

    print(f"     Total: {total}, LP feasible: {len(lp_feasible)}, LP infeasible: {lp_infeasible} ({time.time()-t0:.1f}s)", flush=True)

    # 5. PSD check for LP-feasible vectors
    print(f"  5. PSD check for {len(lp_feasible)} LP-feasible vectors...", flush=True)
    psd_ok = []; psd_violated = []

    for fi, (nvec, y_vals) in enumerate(lp_feasible):
        if fi % 200 == 0 and fi > 0:
            print(f"     {fi}/{len(lp_feasible)}, ok: {len(psd_ok)}, violated: {len(psd_violated)}", flush=True)
        min_eig, n_neg = check_moment_psd(nvec, y_vals, sizes, orbits,
                                          pair_orb, pair_sizes, pt_orb, M_p)
        entry = {"n": nvec, "min_eig": min_eig, "n_neg": n_neg}
        if min_eig >= -1e-8:
            psd_ok.append(entry)
        else:
            psd_violated.append(entry)

    print(f"     PSD: {len(psd_ok)} ok, {len(psd_violated)} violated ({time.time()-t0:.1f}s)", flush=True)

    # 6. Save
    payload = {
        "schema": "fast_count_scan_v1",
        "elapsed_sec": time.time() - t0,
        "total_count_vectors": total,
        "lp_feasible_count": len(lp_feasible),
        "lp_infeasible_count": lp_infeasible,
        "psd_ok_count": len(psd_ok),
        "psd_violated_count": len(psd_violated),
        "note": "PSD uses LP-optimal y. psd_ok means LP+PSD feasible at this n. "
                "psd_violated means LP y violates PSD; SDP needed to determine if other y works.",
        "psd_ok_vectors": [r["n"] for r in psd_ok[:100]],
        "psd_ok_min_eigs": [r["min_eig"] for r in psd_ok[:100]],
        "psd_violated_examples": [{"n": r["n"], "min_eig": r["min_eig"]} for r in psd_violated[:50]],
    }
    out_path = OUT / "fast_count_scan.json"
    out_path.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"\n  Saved: {out_path}", flush=True)
    print(f"\n  === SUMMARY ===", flush=True)
    print(f"  Count vectors:     {total}", flush=True)
    print(f"  LP feasible:       {len(lp_feasible)}", flush=True)
    print(f"  LP+PSD (LP y) ok:  {len(psd_ok)}", flush=True)
    print(f"  LP+PSD unclear:    {len(psd_violated)}", flush=True)

if __name__ == "__main__":
    main()
