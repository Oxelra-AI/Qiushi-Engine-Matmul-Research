#!/usr/bin/env python3
"""analysis: Moment-matrix PSD check for E11 Wang orbit-averaged witnesses.

For binary x_p ∈ {0,1}, define the lifted moment vector χ = (1, x_1, ..., x_{255}).
The moment matrix M = E[χ χ^T] satisfies M ⪰ 0 for any genuine support.
Under orbit averaging: x_p = n_a / |O_a|, y_{pq} = m_j / |P_j|.

M is 256×256:
  M[0,0] = 1
  M[0,p] = M[p,0] = x_p
  M[p,p] = x_p   (binary: x_p^2 = x_p)
  M[p,q] = y_{pq}  for p ≠ q

Check eigenvalues.  If min eigenvalue < 0, extract v^T M v ≥ 0 as a linear cut
in the 103 orbit variables (6 point + 97 pair).
"""
from __future__ import annotations
import numpy as np, json, time, sys
from pathlib import Path
from fractions import Fraction
from itertools import product as iproduct

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

OUT = ROOT / "workspace/data/moment_psd"
OUT.mkdir(parents=True, exist_ok=True)

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

# ── Moment matrix construction ──────────────────────────────────────────

def build_moment_matrix(n_vec, m_vec, orbits, pair_orb, pair_sizes, pt_orb):
    """Build 256×256 moment matrix from orbit-averaged witness."""
    K = len(orbits)
    sizes = [len(o) for o in orbits]
    
    # Point values: x_p = n_a / |O_a|
    x_vals = np.zeros(256)
    for a in range(K):
        val = n_vec[a] / sizes[a] if sizes[a] > 0 else 0.0
        for p in orbits[a]:
            x_vals[p] = val
    
    # Build M
    M = np.zeros((256, 256))
    M[0, 0] = 1.0
    for p in range(1, 256):
        M[0, p] = x_vals[p]
        M[p, 0] = x_vals[p]
        M[p, p] = x_vals[p]  # binary: x_p^2 = x_p
    
    # Off-diagonal pair values
    for p in range(1, 256):
        for q in range(p+1, 256):
            key = (p, q)
            j = pair_orb[key]
            y_val = m_vec[j] / pair_sizes[j] if pair_sizes[j] > 0 else 0.0
            M[p, q] = y_val
            M[q, p] = y_val
    
    return M

def extract_orbit_cut(v, orbits, pair_orb, pair_sizes, K, M_p):
    """Express v^T M v as linear function of orbit variables.
    
    v^T M v = v_0^2 + 2 v_0 Σ_a (Σ_{p∈O_a} v_p) x_a
              + Σ_a (Σ_{p∈O_a} v_p^2) x_a
              + 2 Σ_j (Σ_{{p,q}∈P_j} v_p v_q) y_j
    
    This is a linear function of (x_a, y_j).
    """
    sizes = [len(o) for o in orbits]
    
    # Constant part
    const = v[0]**2
    
    # x coefficients
    x_coef = np.zeros(K)
    for a in range(K):
        s1 = sum(v[p] for p in orbits[a])
        s2 = sum(v[p]**2 for p in orbits[a])
        x_coef[a] = 2 * v[0] * s1 / sizes[a] + s2 / sizes[a]
    
    # y coefficients  
    y_coef = np.zeros(M_p)
    for p in range(1, 256):
        for q in range(p+1, 256):
            j = pair_orb[(p, q)]
            y_coef[j] += 2 * v[p] * v[q] / pair_sizes[j]
    
    return const, x_coef, y_coef

def main():
    t0 = time.time()
    print("analysis: Moment-matrix PSD check")
    
    # 1. Build stabilizer and orbits
    print("  1. Building stabilizer...")
    perms = build_stabilizer()
    print(f"     |G| = {perms.shape[0]} ({time.time()-t0:.1f}s)")
    
    pt_orb, orbits = compute_point_orbits(perms)
    K = len(orbits)
    sizes = [len(o) for o in orbits]
    reps = [o[0] for o in orbits]
    print(f"  2. Point orbits: {K}, sizes {sizes}, reps {reps}")
    
    print("  3. Computing pair orbits...")
    pair_orb, pair_sizes, pair_ep, M_p = compute_pair_orbits(perms, pt_orb)
    print(f"     {M_p} pair orbits ({time.time()-t0:.1f}s)")
    
    # 2. Load witnesses
    wit_path = ROOT / "workspace/data/invariant_pair_block/pair_block_triangles.json"
    with open(wit_path) as f:
        wit_data = json.load(f)
    
    # Also load LP witnesses from analysis
    rlt_path = ROOT / "workspace/data/rlt_lift/rlt_lift_result.json"
    rlt_data = json.load(open(rlt_path)) if rlt_path.exists() else None
    
    tri_path = ROOT / "workspace/data/rlt_triangle_integrality/rlt_triangle_integrality_result.json"
    tri_data = json.load(open(tri_path)) if tri_path.exists() else None
    
    results = []
    
    # 3. Check each block-count witness
    for rec in wit_data['results']:
        label = rec['label']
        n_vec = rec['n_by_point_orbit']
        m_vec = rec['m_by_pair_orbit']
        
        print(f"\n  Checking witness '{label}': n={n_vec}, m_total={rec['m_total']}")
        
        M = build_moment_matrix(n_vec, m_vec, orbits, pair_orb, pair_sizes, pt_orb)
        
        # Check symmetry
        asym = np.max(np.abs(M - M.T))
        print(f"    Matrix asymmetry: {asym:.2e}")
        
        # Eigenvalues
        eigs = np.linalg.eigvalsh(M)
        min_eig = float(eigs[0])
        max_eig = float(eigs[-1])
        n_neg = int(np.sum(eigs < -1e-10))
        
        print(f"    Eigenvalues: min={min_eig:.8f}, max={max_eig:.8f}, negative={n_neg}")
        
        # Extract cut if negative
        cut_info = None
        if min_eig < -1e-10:
            evals, evecs = np.linalg.eigh(M)
            v = evecs[:, 0]  # eigenvector for smallest eigenvalue
            const, x_coef, y_coef = extract_orbit_cut(v, orbits, pair_orb, pair_sizes, K, M_p)
            
            # Verify: const + x_coef · x + y_coef · y should equal min_eig
            x_vals_check = np.array([n_vec[a]/sizes[a] for a in range(K)])
            y_vals_check = np.array([m_vec[j]/pair_sizes[j] for j in range(M_p)])
            reconstructed = const + x_coef @ x_vals_check + y_coef @ y_vals_check
            
            print(f"    Cut reconstruction check: {reconstructed:.10f} vs eigenvalue {min_eig:.10f}")
            
            # Also compute rank of null space
            n_near_zero = int(np.sum(np.abs(eigs) < 1e-8))
            
            cut_info = {
                "min_eigenvalue": min_eig,
                "reconstruction_check": float(reconstructed),
                "constant_term": float(const),
                "x_coefficients": [float(c) for c in x_coef],
                "n_near_zero_eigenvalues": n_near_zero,
                "n_negative_eigenvalues": n_neg,
                "nonzero_y_coef_count": int(np.sum(np.abs(y_coef) > 1e-12)),
            }
        
        entry = {
            "label": label,
            "n": n_vec,
            "m_total": rec['m_total'],
            "min_eigenvalue": min_eig,
            "max_eigenvalue": max_eig,
            "n_negative": n_neg,
            "psd_violated": min_eig < -1e-10,
            "cut_info": cut_info,
        }
        results.append(entry)
    
    # 4. Check LP fractional witnesses if available
    lp_results = []
    
    if tri_data:
        # Check the base and triangle LP witnesses
        for lp_rec in tri_data.get('base_lp_results', []) + tri_data.get('triangle_lp_results', []):
            label = lp_rec.get('label', 'unknown')
            if not lp_rec.get('success', False):
                continue
            
            n_mass = lp_rec.get('n_mass')
            m_mass = lp_rec.get('m_mass_by_pair_orbit')
            if n_mass is None or m_mass is None:
                continue
            
            # Convert from orbit mass to orbit count representation
            # n_mass[a] = n_a (total points in orbit a selected) = x_a * |O_a|
            # m_mass[j] = m_j (total pairs in pair orbit j) = y_j * |P_j|
            n_vec_lp = n_mass
            m_vec_lp = m_mass
            
            M_mat = build_moment_matrix(n_vec_lp, m_vec_lp, orbits, pair_orb, pair_sizes, pt_orb)
            eigs = np.linalg.eigvalsh(M_mat)
            min_eig = float(eigs[0])
            n_neg = int(np.sum(eigs < -1e-10))
            
            lp_entry = {
                "label": label,
                "n_mass": [float(x) for x in n_mass],
                "min_eigenvalue": min_eig,
                "n_negative": n_neg,
                "psd_violated": min_eig < -1e-10,
            }
            lp_results.append(lp_entry)
            
            if n_neg > 0:
                print(f"\n  LP witness '{label}': PSD VIOLATED, min_eig={min_eig:.8f}")
            else:
                print(f"\n  LP witness '{label}': PSD ok, min_eig={min_eig:.8f}")
    
    # 5. Also check the uniform point x=19/255
    uniform_n = [sizes[a] * 19.0 / 255.0 for a in range(K)]
    # For uniform: y_{pq} = (19/255) * (18/254) for any distinct pair
    # Because for uniform binary, P(x_p=1, x_q=1) = 19*18/(255*254)
    uniform_y = 19.0 * 18.0 / (255.0 * 254.0)
    uniform_m = [pair_sizes[j] * uniform_y for j in range(M_p)]
    
    M_unif = build_moment_matrix(uniform_n, uniform_m, orbits, pair_orb, pair_sizes, pt_orb)
    eigs_unif = np.linalg.eigvalsh(M_unif)
    min_eig_unif = float(eigs_unif[0])
    print(f"\n  Uniform point: min_eig={min_eig_unif:.8f}, negative={np.sum(eigs_unif < -1e-10)}")
    
    payload = {
        "schema": "moment_psd_v1",
        "elapsed_sec": time.time() - t0,
        "point_orbit_sizes": sizes,
        "point_orbit_reps": reps,
        "n_pair_orbits": M_p,
        "block_count_witnesses": results,
        "lp_fractional_witnesses": lp_results,
        "uniform_point": {
            "min_eigenvalue": min_eig_unif,
            "psd_ok": min_eig_unif >= -1e-10,
        },
        "any_psd_violation": any(r["psd_violated"] for r in results) or any(r["psd_violated"] for r in lp_results),
    }
    
    out_path = OUT / "moment_psd_check.json"
    out_path.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"\n  Saved: {out_path}")
    print(f"  Total elapsed: {time.time()-t0:.1f}s")
    print(json.dumps({k: v for k, v in payload.items() 
                       if k not in ('lp_fractional_witnesses',)}, indent=2))

if __name__ == "__main__":
    main()
