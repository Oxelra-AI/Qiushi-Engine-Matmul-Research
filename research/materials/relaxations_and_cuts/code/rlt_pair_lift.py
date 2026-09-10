#!/usr/bin/env python3
"""analysis: Sherali-Adams / RLT pair-correlation lift for E11 Wang system.

Introduces pair variables y_{pq} relaxing x_p*x_q for binary indicators x_p.
Wang occupation rows, multiplied by x_p and (1-x_p), give constraints on y.
Orbit averaging under the 1152-element E11 stabilizer keeps the LP small.

If the orbit-averaged LP is infeasible, no distinct 19-point Wang-admissible
E11 quotient A-support exists, establishing R_{F2}(E11 core) >= 20.
"""
from __future__ import annotations
import numpy as np, json, time, sys, pickle
from pathlib import Path
from itertools import product as iproduct
from collections import Counter

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent          # research/research_record
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut
from complete_core_and_transversal import build_core_constraints

LUT_PATH  = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
OUT       = ROOT / "workspace/data/rlt_lift"

# ── F2 helpers ──────────────────────────────────────────────────────────

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

# ── Stabilizer ──────────────────────────────────────────────────────────

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

# ── Orbits ──────────────────────────────────────────────────────────────

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
    G = perms.shape[0]
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

# ── LP construction ─────────────────────────────────────────────────────

def build_lp(records, pt_orb, orbits, pair_orb, n_pair_orbs, pair_ep):
    K = len(orbits); M_p = n_pair_orbs; N = K + M_p
    reps = [orb[0] for orb in orbits]
    print(f"    vars: {K} pt-orbits + {M_p} pair-orbits = {N}")

    # Pair-cardinality coefficients: n_aj[a][j]
    n_aj = [[0]*M_p for _ in range(K)]
    for a in range(K):
        p = reps[a]
        for q in range(1,256):
            if q==p: continue
            key = (min(p,q),max(p,q))
            n_aj[a][pair_orb[key]] += 1

    eq_A=[]; eq_b=[]
    ub_A=[]; ub_b=[]

    # 1. Cardinality Σ|O_a|x_a = 19
    row=[0.0]*N
    for a in range(K): row[a]=float(len(orbits[a]))
    eq_A.append(row); eq_b.append(19.0)

    # 2. Pair cardinality: Σ_j n_aj y_j - 18 x_a = 0
    for a in range(K):
        row=[0.0]*N; row[a]=-18.0
        for j in range(M_p): row[K+j]=float(n_aj[a][j])
        eq_A.append(row); eq_b.append(0.0)

    # 3. Pair upper bounds y_j <= x_alpha, y_j <= x_beta
    for j in range(M_p):
        al,be = pair_ep[j]
        r1=[0.0]*N; r1[K+j]=1.0; r1[al]=-1.0; ub_A.append(r1); ub_b.append(0.0)
        if be!=al:
            r2=[0.0]*N; r2[K+j]=1.0; r2[be]=-1.0; ub_A.append(r2); ub_b.append(0.0)

    # 4. McCormick: x_alpha + x_beta - y_j <= 1
    for j in range(M_p):
        al,be = pair_ep[j]
        r=[0.0]*N; r[al]+=1.0; r[be]+=1.0; r[K+j]=-1.0
        ub_A.append(r); ub_b.append(1.0)

    # 5-7. Wang first-order + RLT
    seen = set()
    def add_ub(coef_tup, rhs):
        key = (coef_tup, rhs)
        if key not in seen:
            seen.add(key)
            ub_A.append(list(coef_tup)); ub_b.append(rhs)
            return True
        return False

    wang_ct = 0
    for ri, rec in enumerate(records):
        bs  = int(rec["point_bitset"])
        L   = int(rec["L"])
        cap = 19 - L
        if cap <= 0: continue

        # Point set from bitset (1-indexed)
        pts = []
        tmp = bs
        while tmp:
            bit = tmp & -tmp
            pts.append(bit.bit_length())   # 1-indexed point
            tmp ^= bit

        # Orbit intersections n_i
        n_orb = [0]*K
        for p in pts: n_orb[pt_orb[p]] += 1

        # First-order: Σ n_a x_a <= cap
        coef_fo = tuple([float(n_orb[a]) for a in range(K)] + [0.0]*M_p)
        if add_ub(coef_fo, float(cap)):
            wang_ct += 1

        # RLT for each orbit representative
        for a in range(K):
            pa = reps[a]
            in_S = (bs >> (pa - 1)) & 1
            c_eff = cap - in_S  # cap-1 if pa∈S, cap otherwise

            # Pair-orbit counts m_j
            mj = [0]*M_p
            for q in pts:
                if q == pa: continue
                mj[pair_orb[(min(pa,q),max(pa,q))]] += 1

            # x_p side: Σ m_j y_j - c_eff x_a <= 0
            coef_xp = [0.0]*N
            coef_xp[a] = -float(c_eff)
            for j in range(M_p):
                if mj[j]: coef_xp[K+j] = float(mj[j])
            if add_ub(tuple(coef_xp), 0.0): wang_ct += 1

            # (1-x_p) side: Σ [n_i + c_eff δ_ia] x_i - Σ m_j y_j <= cap
            coef_1xp = [0.0]*N
            for i in range(K): coef_1xp[i] = float(n_orb[i])
            coef_1xp[a] += float(c_eff)
            for j in range(M_p):
                if mj[j]: coef_1xp[K+j] = -float(mj[j])
            if add_ub(tuple(coef_1xp), float(cap)): wang_ct += 1

        if ri > 0 and ri % 50000 == 0:
            print(f"      processed {ri}/{len(records)} records, {wang_ct} unique Wang constraints")

    print(f"    Wang constraints (dedup): {wang_ct}")
    print(f"    Total: {len(eq_A)} eq + {len(ub_A)} ub")
    return eq_A, eq_b, ub_A, ub_b, K, M_p, N, n_aj

# ── LP solver ───────────────────────────────────────────────────────────

def solve_lp(eq_A, eq_b, ub_A, ub_b, N):
    from scipy.optimize import linprog
    A_ub = np.array(ub_A) if ub_A else None
    b_ub = np.array(ub_b) if ub_b else None
    A_eq = np.array(eq_A) if eq_A else None
    b_eq = np.array(eq_b) if eq_b else None
    bounds = [(0.0, 1.0)] * N
    c_obj  = [0.0] * N
    res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=bounds, method='highs')
    return res

# ── Cap-1 diagnostic ───────────────────────────────────────────────────

def cap1_diagnostic(records, pair_orb, pt_orb, orbits, n_pair_orbs, pair_ep):
    """Count cap-1 forced-zero pairs per orbit representative."""
    reps = [orb[0] for orb in orbits]
    K = len(orbits)
    forced_zero = [set() for _ in range(K)]  # pair orbits forced to zero

    for rec in records:
        cap = 19 - int(rec["L"])
        if cap != 1: continue
        bs = int(rec["point_bitset"])
        pts = []
        tmp = bs
        while tmp:
            bit = tmp & -tmp; pts.append(bit.bit_length()); tmp ^= bit

        for a in range(K):
            pa = reps[a]
            if not ((bs >> (pa-1)) & 1): continue
            # pa is in this cap-1 subspace; force all cross-pairs to zero
            for q in pts:
                if q == pa: continue
                j = pair_orb[(min(pa,q), max(pa,q))]
                forced_zero[a].add(j)

    result = {}
    for a in range(K):
        pa = reps[a]
        total_partners = 254
        forbidden_count = sum(1 for q in range(1,256) if q!=pa and
                              pair_orb[(min(pa,q),max(pa,q))] in forced_zero[a])
        result[f"orbit_{a}_rep_{pa}"] = {
            "orbit_size": len(orbits[a]),
            "forced_zero_pair_orbits": len(forced_zero[a]),
            "forbidden_partners": forbidden_count,
            "available_partners": total_partners - forbidden_count,
            "needed_partner_weight": "18 * x_a (continuous) or 18 integer partners",
        }
    return result

# ── main ────────────────────────────────────────────────────────────────

def main():
    t0 = time.time()
    OUT.mkdir(parents=True, exist_ok=True)
    print("analysis: SA/RLT pair-correlation lift for E11 Wang system")

    # 1. Stabilizer
    t1=time.time(); print("  1. Building stabilizer...")
    perms = build_stabilizer()
    print(f"     |G| = {len(perms)} ({time.time()-t1:.1f}s)")

    # 2. Point orbits
    t1=time.time()
    pt_orb, orbits = compute_point_orbits(perms)
    K = len(orbits)
    print(f"  2. Point orbits: {K}, sizes {[len(o) for o in orbits]} ({time.time()-t1:.1f}s)")

    # 3. Pair orbits
    t1=time.time(); print("  3. Computing pair orbits...")
    pair_orb, pair_sizes, pair_ep, M_p = compute_pair_orbits(perms, pt_orb)
    print(f"     {M_p} pair orbits ({time.time()-t1:.1f}s)")

    # 4. Load Wang table
    t1=time.time(); print("  4. Loading Wang table...")
    lut, _ = load_lut(LUT_PATH)
    records, wmeta = build_core_constraints(CoreQuotient(1), lut)
    print(f"     {len(records)} records ({time.time()-t1:.1f}s)")

    # 5. Cap-1 diagnostic
    t1=time.time(); print("  5. Cap-1 diagnostic...")
    cap1_info = cap1_diagnostic(records, pair_orb, pt_orb, orbits, M_p, pair_ep)
    for k,v in cap1_info.items():
        print(f"     {k}: forbidden={v['forbidden_partners']}, available={v['available_partners']}")

    # 6. Build LP
    t1=time.time(); print("  6. Building LP constraints...")
    eq_A, eq_b, ub_A, ub_b, K, M_p, N, n_aj = build_lp(
        records, pt_orb, orbits, pair_orb, M_p, pair_ep)
    print(f"     LP built ({time.time()-t1:.1f}s)")

    # 7. Solve LP
    t1=time.time(); print("  7. Solving LP...")
    res = solve_lp(eq_A, eq_b, ub_A, ub_b, N)
    status = "infeasible" if res.status==2 else ("feasible" if res.status==0 else f"status_{res.status}")
    print(f"     LP result: {status} ({res.message}) ({time.time()-t1:.1f}s)")

    # 8. Output
    result = {
        "schema": "rlt_lift_v1",
        "lp_status": status,
        "lp_status_code": int(res.status),
        "lp_message": str(res.message),
        "n_point_orbits": K,
        "n_pair_orbits": M_p,
        "n_variables": N,
        "n_eq_constraints": len(eq_A),
        "n_ub_constraints": len(ub_A),
        "point_orbit_sizes": [len(o) for o in orbits],
        "point_orbit_reps": [o[0] for o in orbits],
        "pair_orbit_size_histogram": dict(Counter(pair_sizes)),
        "cap1_diagnostic": cap1_info,
        "elapsed_sec": round(time.time()-t0, 3),
    }

    if res.status == 0 and res.x is not None:
        x_sol = {a: float(res.x[a]) for a in range(K)}
        result["x_solution"] = {f"orb{a}_rep{orbits[a][0]}_size{len(orbits[a])}": round(v,10)
                                 for a,v in x_sol.items()}
        result["x_total_check"] = round(sum(len(orbits[a])*x_sol[a] for a in range(K)),10)
        # Pair cardinality check
        pc = {}
        for a in range(K):
            s = sum(n_aj[a][j]*float(res.x[K+j]) for j in range(M_p))
            pc[f"orb{a}"] = round(s,10)
        result["pair_cardinality_check"] = pc
        # Check which pair orbits have nonzero y
        nz_y = sum(1 for j in range(M_p) if float(res.x[K+j]) > 1e-10)
        result["nonzero_pair_orbits"] = nz_y
        # Check uniform point: x_a = 19/255 for all a
        result["uniform_x_value"] = round(19.0/255, 10)

    out_path = OUT / "rlt_lift_result.json"
    out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"  saved: {out_path}")
    print(json.dumps({k:v for k,v in result.items()
                      if k not in ('x_solution','cap1_diagnostic','pair_orbit_size_histogram')},
                     indent=2))

if __name__ == "__main__":
    main()
