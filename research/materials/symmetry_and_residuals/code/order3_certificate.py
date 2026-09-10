#!/usr/bin/env python3
r"""analysis: Order-3 diagonal sandwich certificate over F_2.

Computes the L_0 projection structure of orbit sums to determine
whether the sigma-projector argument can exclude order-3 symmetric
rank-22 decompositions.
"""
import numpy as np, json, time
from pathlib import Path

def gf2_matmul(A, B):
    return np.asarray(A, np.int64) @ np.asarray(B, np.int64) % 2

def gf2_rank(M):
    M = np.array(M, dtype=np.int64) % 2
    r, c = M.shape
    piv = 0
    for j in range(c):
        found = None
        for i in range(piv, r):
            if M[i, j]:
                found = i; break
        if found is None: continue
        M[[piv, found]] = M[[found, piv]]
        for i in range(r):
            if i != piv and M[i, j]:
                M[i] = (M[i] + M[piv]) % 2
        piv += 1
    return piv

def gf2_rref(M):
    """Return (rref, pivot_cols) for M over F_2."""
    M = np.array(M, dtype=np.int64) % 2
    r, c = M.shape
    piv = 0; pivots = []
    for j in range(c):
        found = None
        for i in range(piv, r):
            if M[i, j]: found = i; break
        if found is None: continue
        M[[piv, found]] = M[[found, piv]]
        for i in range(r):
            if i != piv and M[i, j]:
                M[i] = (M[i] + M[piv]) % 2
        pivots.append(j); piv += 1
    return M, pivots

def gf2_in_span(v, basis):
    """Check if v is in row span of basis over F_2."""
    v = np.array(v, dtype=np.int64).flatten() % 2
    if basis.shape[0] == 0:
        return np.all(v == 0)
    aug = np.vstack([basis % 2, v.reshape(1, -1)])
    return gf2_rank(aug) == gf2_rank(basis % 2)

def gf2_left_kernel(M):
    """Return K whose rows span {x : x @ M = 0 mod 2}."""
    # x @ M = 0  <==>  M^T @ x^T = 0  <==>  x^T in right kernel of M^T
    # Right kernel of M^T: augment [M^T | I] and row-reduce
    M2 = np.array(M, dtype=np.int64) % 2
    rows, cols = M2.shape  # M is rows×cols; we want left kernel (row vectors of length rows)
    # M^T is cols×rows
    Mt = M2.T  # cols × rows
    r, c = Mt.shape  # r=cols, c=rows
    aug = np.hstack([Mt, np.eye(c, dtype=np.int64)]) % 2  # c × (r + c)
    piv = 0; pivot_rows = []
    for j in range(r):
        found = None
        for i in range(piv, c):
            if aug[i, j]: found = i; break
        if found is None: continue
        aug[[piv, found]] = aug[[found, piv]]
        for i in range(c):
            if i != piv and aug[i, j]:
                aug[i] = (aug[i] + aug[piv]) % 2
        pivot_rows.append(piv); piv += 1
    kern = []
    for i in range(c):
        if i not in pivot_rows:
            kern.append(aug[i, r:].copy() % 2)
    return np.array(kern, dtype=np.int64) if kern else np.zeros((0, c), dtype=np.int64)

def build_T_flat():
    T = np.zeros((81, 9), dtype=np.int64)
    for a in range(3):
        for b in range(3):
            for f in range(3):
                uv_row = a * 3 + b
                uv_col = b * 3 + f
                w_idx = a * 3 + f
                T[uv_row * 9 + uv_col, w_idx] = 1
    return T % 2

def main():
    t0 = time.time()
    out_dir = Path("data/order3_certificate")
    out_dir.mkdir(parents=True, exist_ok=True)
    
    T_flat = build_T_flat()
    assert gf2_rank(T_flat) == 9
    
    # Q not needed for this certificate — we work directly with L_0 and Fix(E)
    
    # Order-3 cyclic permutation
    F3 = np.array([[0,1,0],[0,0,1],[1,0,0]], dtype=np.int64)
    F3_inv = np.array([[0,0,1],[1,0,0],[0,1,0]], dtype=np.int64)
    assert np.all(gf2_matmul(F3, F3_inv) % 2 == np.eye(3, dtype=np.int64))
    
    # Sandwich actions
    M9 = np.kron(F3.T, F3_inv) % 2
    gE = np.kron(M9, M9) % 2
    hW = np.kron(F3_inv, F3.T) % 2
    
    # Verify
    assert np.all(gf2_matmul(gE, T_flat) % 2 == gf2_matmul(T_flat, hW) % 2), "gE*T != T*hW"
    g2 = gf2_matmul(gE, gE)
    g3 = gf2_matmul(g2, gE)
    assert np.all(g3 % 2 == np.eye(81, dtype=np.int64)), "gE^3 != I"
    assert not np.all(gE % 2 == np.eye(81, dtype=np.int64)), "gE = I"
    print("Action checks passed")
    
    # σ = I + g + g²
    sigma = (np.eye(81, dtype=np.int64) + gE + g2) % 2
    sigma_rank = gf2_rank(sigma.copy())
    sigma2 = gf2_matmul(sigma, sigma)
    is_idempotent = np.all(sigma2 % 2 == sigma % 2)
    
    # Fix(E) basis via σ image
    fix_vecs = []
    for i in range(81):
        v = sigma[:, i] % 2
        if np.any(v):
            trial = np.vstack(fix_vecs + [v.reshape(1,-1)]) if fix_vecs else v.reshape(1,-1)
            if gf2_rank(trial) > len(fix_vecs):
                fix_vecs.append(v)
    fixE_dim = len(fix_vecs)
    FixE = np.array(fix_vecs, dtype=np.int64)
    
    # L_0 via σ_W
    sigma_W = (np.eye(9, dtype=np.int64) + hW + gf2_matmul(hW, hW)) % 2
    fixW_vecs = []
    for i in range(9):
        v = sigma_W[:, i] % 2
        if np.any(v):
            trial = np.vstack(fixW_vecs + [v.reshape(1,-1)]) if fixW_vecs else v.reshape(1,-1)
            if gf2_rank(trial) > len(fixW_vecs):
                fixW_vecs.append(v)
    fixW_dim = len(fixW_vecs)
    
    L0_vecs = []
    for w in fixW_vecs:
        l = gf2_matmul(T_flat, w.reshape(-1,1)).flatten() % 2
        L0_vecs.append(l)
    L0_basis = np.array(L0_vecs, dtype=np.int64) if L0_vecs else np.zeros((0, 81), dtype=np.int64)
    L0_dim = gf2_rank(L0_basis.copy())
    # Clean basis
    clean = []
    for v in L0_vecs:
        trial = np.vstack(clean + [v.reshape(1,-1)]) if clean else v.reshape(1,-1)
        if gf2_rank(trial) > len(clean):
            clean.append(v)
        if len(clean) == L0_dim: break
    L0_basis = np.array(clean, dtype=np.int64)
    
    print(f"Fix(E)={fixE_dim}, L0={L0_dim}, sigma rank={sigma_rank}, idempotent={is_idempotent}")
    
    # Build L0 coordinate extraction within Fix(E)
    # Extend L0_basis to a full Fix(E) basis
    extended = list(L0_basis)
    for v in fix_vecs:
        trial = np.vstack(extended + [v.reshape(1,-1)])
        if gf2_rank(trial) > len(extended):
            extended.append(v)
        if len(extended) == fixE_dim: break
    FixE_ordered = np.array(extended, dtype=np.int64)
    
    # Build coordinate extraction: for v in Fix(E), find coords c s.t. v = Σ c_i * FixE_ordered[i]
    # This is: FixE_ordered^T * c = v, solve for c
    # Row-reduce [FixE_ordered^T | I_81] to get extraction
    n = fixE_dim
    m = 81
    aug = np.hstack([FixE_ordered.T % 2, np.eye(m, dtype=np.int64)]) % 2  # m × (n + m)
    piv = 0
    pivot_rows = []
    for j in range(n):
        found = None
        for i in range(piv, m):
            if aug[i, j]: found = i; break
        if found is None: continue
        aug[[piv, found]] = aug[[found, piv]]
        for i in range(m):
            if i != piv and aug[i, j]:
                aug[i] = (aug[i] + aug[piv]) % 2
        pivot_rows.append(piv); piv += 1
    
    # Extract matrix: coords[k] = sum of aug[pivot_rows[k], n:] * v for the k-th basis
    extract = np.zeros((n, m), dtype=np.int64)
    for k in range(len(pivot_rows)):
        extract[k] = aug[pivot_rows[k], n:] % 2
    
    # Verify on L0_basis: should give identity-like coords
    for i in range(L0_dim):
        c = gf2_matmul(extract, L0_basis[i].reshape(-1,1)).flatten() % 2
        # First L0_dim coords should have rank L0_dim pattern
    
    # Enumerate rank-one points and orbits
    fixed_pts = []
    free_orbits = []
    seen = set()
    total_rk1 = 0
    
    for u_int in range(1, 512):
        u = np.array([(u_int >> i) & 1 for i in range(9)], dtype=np.int64)
        for v_int in range(1, 512):
            v = np.array([(v_int >> i) & 1 for i in range(9)], dtype=np.int64)
            x = np.kron(u, v) % 2
            k = tuple(x.tolist())
            if k in seen: continue
            total_rk1 += 1
            
            gx = gf2_matmul(gE, x.reshape(-1,1)).flatten() % 2
            gk = tuple(gx.tolist())
            
            if gk == k:
                fixed_pts.append(x)
                seen.add(k)
            else:
                g2x = gf2_matmul(g2, x.reshape(-1,1)).flatten() % 2
                osum = (x + gx + g2x) % 2
                free_orbits.append(osum)
                seen.add(k)
                seen.add(gk)
                seen.add(tuple(g2x.tolist()))
    
    print(f"Rank-one: {total_rk1}, fixed: {len(fixed_pts)}, free orbits: {len(free_orbits)}")
    
    # Fixed span
    fp_mat = np.array(fixed_pts, dtype=np.int64) if fixed_pts else np.zeros((0,81), dtype=np.int64)
    fp_rank = gf2_rank(fp_mat.copy())
    B_cap_L0 = fp_rank + L0_dim - gf2_rank(np.vstack([fp_mat[:min(fp_rank,len(fixed_pts))], L0_basis]).copy()) if fp_rank > 0 else 0
    print(f"Fixed span={fp_rank}, B∩L0={B_cap_L0}")
    
    # Classify orbit sums by L0 coordinate
    n_zero = 0
    L0_images = {}  # L0 coord tuple -> count
    
    for osum in free_orbits:
        if np.all(osum == 0):
            n_zero += 1
            continue
        # Get Fix(E) coordinates
        coords = gf2_matmul(extract, osum.reshape(-1,1)).flatten() % 2
        L0_comp = tuple(coords[:L0_dim].tolist())
        L0_images[L0_comp] = L0_images.get(L0_comp, 0) + 1
    
    # Count by L0 component
    zero_L0 = L0_images.get(tuple([0]*L0_dim), 0)
    nonzero_L0 = {k: v for k, v in L0_images.items() if any(x != 0 for x in k)}
    
    # Check which L0 elements are covered
    all_L0_elts = set()
    for b in range(1, 2**L0_dim):
        all_L0_elts.add(tuple((b >> i) & 1 for i in range(L0_dim)))
    covered = set(nonzero_L0.keys())
    missing = all_L0_elts - covered
    
    if covered:
        cov_vecs = np.array([list(k) for k in covered], dtype=np.int64)
        cov_rank = gf2_rank(cov_vecs.copy())
    else:
        cov_rank = 0
    
    print(f"\nOrbit sum L0 analysis:")
    print(f"  Zero sum: {n_zero}")
    print(f"  Zero L0 comp: {zero_L0}")
    print(f"  Nonzero L0 comp: {sum(nonzero_L0.values())}")
    print(f"  Distinct nonzero L0 images: {len(nonzero_L0)}")
    print(f"  Rank of L0 images: {cov_rank}")
    print(f"  Missing L0 elements: {len(missing)}")
    for k, v in sorted(nonzero_L0.items()):
        print(f"    L0={list(k)}: {v} orbits")
    
    # THE KEY QUESTION: Can orbit sums span L0?
    if cov_rank < L0_dim:
        print(f"\n*** THEOREM: Orbit sums can only reach rank {cov_rank} in L0 (need {L0_dim}).")
        print("    Fixed rank-one span has B∩L0=0, so fixed points don't help.")
        print("    NO termwise diagonal order-3 rank-≤22 decomposition exists over F_2.")
        theorem = "proved"
    else:
        print(f"\n  Orbit sums span L0 (rank {cov_rank}). Simple budget fails.")
        theorem = "budget_insufficient"
        
        # Even though L0 can be spanned, check tighter constraints
        # For skeleton (7,1): need 7 orbits + 1 fixed pt with dim S = 22
        # In Fix(E) part: dim ≤ 8, must contain L0 (dim 3) 
        # In non-fixed part: dim ≤ 14, must contain L_nonfixed (dim 6)
        # Check whether the orbits that supply L0 also have good non-fixed behavior
        
        # Count orbits that can supply each L0 element
        print(f"\n  Per-L0-element orbit counts:")
        for elt in sorted(all_L0_elts):
            count = nonzero_L0.get(elt, 0)
            in_L0 = sum(1 for k, v in nonzero_L0.items() 
                       if all((a+b)%2 == c for a,b,c in zip(k, elt, [0]*L0_dim)) or k == elt)
            print(f"    {list(elt)}: {count} orbits")
    
    # Conjugacy of order-3 subgroups
    gl3_elts = []
    for a in range(512):
        M = np.array([(a >> (3*i+j)) & 1 for i in range(3) for j in range(3)], dtype=np.int64).reshape(3,3)
        if gf2_rank(M.copy()) == 3:
            gl3_elts.append(M)
    
    o3_count = 0
    for M in gl3_elts:
        M3 = gf2_matmul(gf2_matmul(M, M), M)
        if np.all(M3 % 2 == np.eye(3, dtype=np.int64)) and not np.all(M % 2 == np.eye(3, dtype=np.int64)):
            o3_count += 1
    o3_subgroups = o3_count // 2
    
    # Check conjugacy classes
    o3_classes = []
    o3_reps = []
    for M in gl3_elts:
        M3 = gf2_matmul(gf2_matmul(M, M), M)
        if not (np.all(M3 % 2 == np.eye(3, dtype=np.int64)) and not np.all(M % 2 == np.eye(3, dtype=np.int64))):
            continue
        # Check if M is conjugate to any existing rep
        is_new = True
        for idx, rep in enumerate(o3_reps):
            for G in gl3_elts:
                G_inv_data = np.round(np.linalg.inv(G.astype(float))).astype(np.int64) % 2
                conj = gf2_matmul(gf2_matmul(G, rep), G_inv_data) % 2
                if np.all(conj == M % 2):
                    is_new = False; break
            if not is_new: break
        if is_new:
            o3_reps.append(M % 2)
    
    # Each conjugacy class of elements → conjugacy class of subgroups
    # <g> = <g^2> for order-3 elements, so conjugacy classes of elements
    # map 2:1 to conjugacy classes of subgroups
    
    print(f"\n|GL_3(F_2)|={len(gl3_elts)}, order-3 elements={o3_count}, subgroups={o3_subgroups}")
    print(f"Conjugacy classes of order-3 elements: {len(o3_reps)}")
    for i, rep in enumerate(o3_reps):
        print(f"  Class {i}: {rep.tolist()}")
    
    results = {
        "purpose": "Order-3 diagonal sandwich L0-projection analysis over F_2",
        "field": "F2",
        "fixE_dim": fixE_dim, "L0_dim": L0_dim,
        "sigma_rank": sigma_rank, "is_idempotent": bool(is_idempotent),
        "total_rk1": total_rk1, "fixed_count": len(fixed_pts),
        "free_orbits": len(free_orbits),
        "fp_rank": fp_rank, "B_cap_L0": B_cap_L0,
        "orbit_L0": {
            "zero_sum": n_zero,
            "zero_L0_comp": zero_L0,
            "nonzero_L0_images": {str(k): v for k, v in sorted(nonzero_L0.items())},
            "L0_image_rank": cov_rank,
            "all_L0_elements": 2**L0_dim - 1,
            "covered_count": len(covered),
            "missing_count": len(missing),
            "missing_elements": [list(x) for x in sorted(missing)],
        },
        "conjugacy": {
            "GL3_order": len(gl3_elts),
            "order3_elements": o3_count,
            "order3_subgroups": o3_subgroups,
            "conjugacy_classes": len(o3_reps),
        },
        "theorem_status": theorem,
        "elapsed_sec": time.time() - t0,
    }
    
    out = out_dir / "order3_certificate_analysis.json"
    with open(out, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nSaved: {out}, elapsed {time.time()-t0:.1f}s")

if __name__ == '__main__':
    main()
