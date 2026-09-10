#!/usr/bin/env python3
"""S_min cover analysis for all 620 E11 V-orbit representatives (optimized).

Uses LP relaxation for fast cover feasibility checking.
"""
import json, sys, time
from collections import Counter
from pathlib import Path
import numpy as np
from scipy.optimize import linprog, milp, LinearConstraint, Bounds

def build_e11_core():
    T = np.zeros((9,9,9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T[1:,:,:]

def gf2_rank_int(vecs):
    basis = {}
    for v in vecs:
        x = int(v)
        while x:
            p = x.bit_length()-1
            if p in basis: x ^= basis[p]
            else: basis[p]=x; break
    return len(basis)

def annihilator_basis(prefix, n=8):
    d = gf2_rank_int(prefix)
    out = []
    for l in range(1, 1<<n):
        if all(bin(l&v).count('1')%2==0 for v in prefix):
            if gf2_rank_int(out+[l]) > len(out):
                out.append(l)
                if len(out) == n-d: return out
    raise RuntimeError

def find_phi_vectors(prefix, n=8):
    d = len(prefix)
    M = np.zeros((d,n), dtype=np.uint8)
    for k,m in enumerate(prefix):
        for b in range(n): M[k,b] = (m>>b)&1
    phis = []
    for i in range(d):
        tgt = np.zeros(d, dtype=np.uint8); tgt[i]=1
        aug = np.hstack([M.copy(), tgt.reshape(-1,1)])
        row=0; pivots=[]
        for col in range(n):
            piv=None
            for r in range(row,d):
                if aug[r,col]: piv=r; break
            if piv is None: continue
            aug[[row,piv]] = aug[[piv,row]]
            for r in range(d):
                if r!=row and aug[r,col]: aug[r]^=aug[row]
            pivots.append((row,col)); row+=1
        x = np.zeros(n, dtype=np.uint8)
        for r,c in pivots: x[c]=aug[r,n]
        phis.append(sum(int(x[b])<<b for b in range(n)))
    return phis

def quotient_core(core, ann):
    q = np.zeros((len(ann), core.shape[1], core.shape[2]), dtype=np.uint8)
    for i,l in enumerate(ann):
        for a in range(core.shape[0]):
            if (l>>a)&1: q[i] ^= core[a]
    return q

def mat_to_81(M):
    v=0
    for b in range(9):
        for c in range(9):
            if int(M[b,c])&1: v|=1<<(9*b+c)
    return v

def i81_to_rows(v):
    rows=[]
    for b in range(9):
        val=0
        for c in range(9):
            if (v>>(9*b+c))&1: val|=1<<c
        rows.append(val)
    return rows

def gf2_basis_81(vecs):
    basis = {}
    for v in vecs:
        x = int(v)
        while x:
            p = x.bit_length()-1
            if p in basis: x ^= basis[p]
            else: basis[p]=x; break
    return sorted(basis.values(), reverse=True)

def gf2_rank_rows(rows):
    basis = {}
    for r in rows:
        x = int(r)
        while x:
            p = x.bit_length()-1
            if p in basis: x ^= basis[p]
            else: basis[p]=x; break
    return len(basis)

def min_rank_coset(target_rows, basis_81):
    d = len(basis_81)
    br = [i81_to_rows(b) for b in basis_81]
    cur = list(target_rows)
    best = gf2_rank_rows(cur)
    for gray in range(1, 1<<d):
        j = (gray & -gray).bit_length()-1
        for b in range(9): cur[b] ^= br[j][b]
        r = gf2_rank_rows(cur)
        if r < best: best = r
    return best

# Precompute the F2^4 incidence matrix: A[phi-1, v-1] = parity(phi & v)
INCIDENCE = np.zeros((15, 15), dtype=np.float64)
for phi in range(1, 16):
    for v in range(1, 16):
        INCIDENCE[phi-1, v-1] = 1.0 if bin(phi & v).count('1') % 2 == 1 else 0.0

def cover_min_lp(m_phi_dict):
    """LP relaxation: minimize sum n_v subject to incidence @ n >= m, n >= 0."""
    b = np.array([m_phi_dict.get(phi, 0) for phi in range(1, 16)], dtype=np.float64)
    c = np.ones(15, dtype=np.float64)
    res = linprog(c, A_ub=-INCIDENCE, b_ub=-b, bounds=[(0, None)]*15, method='highs')
    if res.success:
        return res.fun
    return float('inf')


def cover_min_int(m_phi_dict):
    """Exact integer cover optimum for the 15 nonzero vectors of F2^4."""
    b = np.array([m_phi_dict.get(phi, 0) for phi in range(1, 16)], dtype=np.float64)
    lc = LinearConstraint(INCIDENCE, lb=b, ub=np.full(15, np.inf))
    res = milp(
        c=np.ones(15),
        integrality=np.ones(15),
        bounds=Bounds(np.zeros(15), np.full(15, 19)),
        constraints=lc,
        options={'time_limit': 10.0, 'mip_rel_gap': 0.0},
    )
    if res.success:
        return int(round(float(res.fun)))
    return None

def analyze_one(core, prefix):
    ann = annihilator_basis(prefix, 8)
    Q = quotient_core(core, ann)
    phis = find_phi_vectors(prefix, 8)
    
    slices_81 = [mat_to_81(Q[k]) for k in range(4)]
    smin_basis = gf2_basis_81(slices_81)
    dim_smin = len(smin_basis)
    
    # GF2 flattening ranks
    flat_A = dim_smin
    B_vecs = []
    for b in range(9):
        v = 0
        for a in range(4):
            for c in range(9):
                if int(Q[a,b,c])&1: v |= 1<<(4*c+a)
        B_vecs.append(v)
    flat_B = gf2_rank_int(B_vecs)
    C_vecs = []
    for c in range(9):
        v = 0
        for a in range(4):
            for b in range(9):
                if int(Q[a,b,c])&1: v |= 1<<(4*b+a)
        C_vecs.append(v)
    flat_C = gf2_rank_int(C_vecs)
    flat_lb = max(flat_A, flat_B, flat_C)
    
    R = np.zeros((4,9,9), dtype=np.uint8)
    for k,phi in enumerate(phis):
        for a in range(8):
            if (phi>>a)&1: R[k] ^= core[a]
    
    m_phi = {}
    for pm in range(1,16):
        tgt = np.zeros((9,9), dtype=np.uint8)
        for k in range(4):
            if (pm>>k)&1: tgt ^= R[k]
        tgt_rows = []
        for b in range(9):
            val=0
            for c in range(9):
                if int(tgt[b,c])&1: val|=1<<c
            tgt_rows.append(val)
        m_phi[pm] = min_rank_coset(tgt_rows, smin_basis)
    
    sum_m = sum(m_phi.values())
    s_max = 19 - flat_lb
    
    # LP is only a lower bound; use the exact integer cover optimum for conclusions.
    lp_min = cover_min_lp(m_phi)
    int_min = cover_min_int(m_phi)
    best_s = int_min if (int_min is not None and int_min <= s_max) else None
    
    return {
        'prefix': prefix,
        'dim_smin': dim_smin,
        'flat_lb': flat_lb,
        'flat_A': flat_A, 'flat_B': flat_B, 'flat_C': flat_C,
        'sum_m': sum_m,
        's_max': s_max,
        'lp_min_cost': round(lp_min, 6) if lp_min < float('inf') else None,
        'int_min_cover_s': int_min,
        'best_feasible_s': best_s,
        'promising': best_s is not None,
        'm_phi': {int(k): int(v) for k,v in m_phi.items()},
    }

def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--orbits', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--max-orbits', type=int, default=0)
    args = ap.parse_args()
    
    t0 = time.time()
    data = json.loads(args.orbits.read_text())
    all_reps = data.get('high_Wang_cap_low_qnnz_head',
                        data.get('low_qnnz_representatives_head', []))
    if not all_reps:
        print("ERROR: no orbit records"); sys.exit(1)
    
    if args.max_orbits > 0:
        all_reps = all_reps[:args.max_orbits]
    
    core = build_e11_core()
    records = []
    promising = []
    
    for i, rep in enumerate(all_reps):
        prefix = rep['basis']
        rec = analyze_one(core, prefix)
        rec['orbit_id'] = rep.get('orbit_id', i)
        rec['orbit_size'] = rep.get('orbit_size', 0)
        rec['q_nnz'] = rep.get('quotient_nnz', 0)
        records.append(rec)
        
        if rec['promising']:
            promising.append(rec)
        
        if i < 5 or rec['promising'] or i % 100 == 0:
            tag = f"PROMISING s={rec['best_feasible_s']}" if rec['promising'] else "blocked"
            print(f"{i}/{len(all_reps)} orbit={rec['orbit_id']} prefix={prefix} "
                  f"dim={rec['dim_smin']} sum_m={rec['sum_m']} flat_lb={rec['flat_lb']} "
                  f"lp={rec['lp_min_cost']} int_s={rec['int_min_cover_s']} s_max={rec['s_max']} [{tag}]")
    
    # Summary
    print(f"\n=== Summary ===")
    print(f"Orbits: {len(records)}, Promising: {len(promising)}")
    
    dim_dist = Counter(r['dim_smin'] for r in records)
    flat_dist = Counter(r['flat_lb'] for r in records)
    sum_m_vals = [r['sum_m'] for r in records]
    lp_vals = [r['lp_min_cost'] for r in records if r['lp_min_cost'] is not None]
    
    print(f"dim_S_min: {dict(sorted(dim_dist.items()))}")
    print(f"flat_lb: {dict(sorted(flat_dist.items()))}")
    print(f"sum_m: [{min(sum_m_vals)}, {max(sum_m_vals)}]")
    if lp_vals:
        print(f"lp_min: [{min(lp_vals):.2f}, {max(lp_vals):.2f}]")
    
    # Distribution of best_feasible_s
    s_dist = Counter(r['best_feasible_s'] for r in records if r['promising'])
    blocked = sum(1 for r in records if not r['promising'])
    print(f"blocked (no feasible s <= s_max): {blocked}")
    print(f"best_feasible_s distribution: {dict(sorted(s_dist.items()))}")
    
    if promising:
        # Show most promising (lowest s)
        promising.sort(key=lambda p: (p['best_feasible_s'], p['sum_m']))
        print(f"\nTop 20 most promising:")
        for p in promising[:20]:
            print(f"  orbit={p['orbit_id']} prefix={p['prefix']} s={p['best_feasible_s']} "
                  f"sum_m={p['sum_m']} flat_lb={p['flat_lb']} lp={p['lp_min_cost']}")
    
    result = {
        'purpose': 'S_min cover analysis across all E11 V-orbit representatives',
        'field': 'F2',
        'orbits_scanned': len(records),
        'promising_count': len(promising),
        'blocked_count': blocked,
        'best_s_distribution': dict(sorted((int(k),int(v)) for k,v in s_dist.items())),
        'dim_S_min_distribution': dict(sorted((int(k),int(v)) for k,v in dim_dist.items())),
        'sum_m_stats': {'min': int(min(sum_m_vals)), 'max': int(max(sum_m_vals))},
        'flattening_lb_distribution': dict(sorted((int(k),int(v)) for k,v in flat_dist.items())),
        'promising_orbits': [{'orbit_id': p['orbit_id'], 'prefix': p['prefix'],
                              'best_feasible_s': p['best_feasible_s'], 'int_min_cover_s': p['int_min_cover_s'], 'sum_m': p['sum_m'],
                              'flat_lb': p['flat_lb'], 'lp_min': p['lp_min_cost'],
                              'orbit_size': p.get('orbit_size',0),
                              'm_phi': p['m_phi']} for p in promising],
        'elapsed_sec': time.time()-t0,
        'records': records,
    }
    
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True, default=int)+'\n')
    print(f"\nElapsed: {time.time()-t0:.1f}s")
    print(f"wrote {args.out}")

if __name__ == '__main__':
    main()
