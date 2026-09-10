#!/usr/bin/env python3
r"""analysis: symmetry-invariant F_2 rank-22 search.

For sandwich elements F in GL_3(F_2), the action (F,F,F) on the UV space E
preserves L and acts on E/L. A sandwich-invariant rank-22 decomposition
must have its 22-dimensional UV span S be g-invariant.

We:
1. Compute eigenspace decomposition of order-7 and order-3 sandwich on E/L
2. Compute the full sandwich group fixed subspace
3. Count invariant 13-planes (quotient dimension)
4. If feasible, enumerate and test with the rank-one oracle
5. Report which symmetry families are excluded or admit candidates
"""

import numpy as np
import json, time, sys
from pathlib import Path

# ---------- GF(2) linear algebra ----------

def gf2_rref(M):
    """Row-reduce M over GF(2). Returns (rref_rows, rank, pivot_cols)."""
    M = np.array(M, dtype=np.int8) % 2
    rows, cols = M.shape
    pivots = []
    r = 0
    for c in range(cols):
        found = -1
        for i in range(r, rows):
            if M[i, c]:
                found = i; break
        if found < 0: continue
        if found != r:
            M[[r, found]] = M[[found, r]]
        pivots.append(c)
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] = (M[i] ^ M[r])
        r += 1
    return M[:r], r, pivots

def gf2_rank(M):
    _, r, _ = gf2_rref(np.array(M, dtype=np.int8))
    return r

def gf2_nullspace(M):
    """Basis of ker(M) over GF(2)."""
    M = np.array(M, dtype=np.int8) % 2
    rows, cols = M.shape
    rref, rank, pivots = gf2_rref(M)
    free = [c for c in range(cols) if c not in pivots]
    basis = []
    for f in free:
        v = np.zeros(cols, dtype=np.int8)
        v[f] = 1
        for i, p in enumerate(pivots):
            v[p] = rref[i, f]
        basis.append(v)
    if not basis:
        return np.zeros((0, cols), dtype=np.int8)
    return np.array(basis, dtype=np.int8)

def gf2_inv(M):
    """Invert square matrix over GF(2)."""
    n = M.shape[0]
    aug = np.hstack([np.array(M, dtype=np.int8) % 2, np.eye(n, dtype=np.int8)])
    for c in range(n):
        found = -1
        for i in range(c, n):
            if aug[i, c]:
                found = i; break
        assert found >= 0, "Singular"
        if found != c:
            aug[[c, found]] = aug[[found, c]]
        for i in range(n):
            if i != c and aug[i, c]:
                aug[i] ^= aug[c]
    return aug[:, n:]

def gf2_matpow(M, k):
    """M^k over GF(2)."""
    n = M.shape[0]
    result = np.eye(n, dtype=np.int8)
    base = np.array(M, dtype=np.int8) % 2
    while k > 0:
        if k & 1:
            result = (result @ base) % 2
        base = (base @ base) % 2
        k >>= 1
    return result

# ---------- Tensor construction ----------

def build_T333_flat():
    """Build T333 as 81x9 matrix (UV-W flattening)."""
    T = np.zeros((81, 9), dtype=np.int8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                uv = (3*i+j)*9 + (3*j+k)
                w = 3*k+i
                T[uv, w] = 1
    return T

def build_quotient_Q(T_flat):
    """72x81 quotient map with ker = col(T_flat)."""
    # Row space of T_flat^T spans L
    Lt = T_flat.T  # 9x81
    Q = gf2_nullspace(Lt)
    assert Q.shape[0] == 72
    assert gf2_rank(Q) == 72
    assert np.all((Q @ T_flat) % 2 == 0)
    return Q

def build_Q_right_inverse(Q):
    """81x72 matrix Qp with Q Qp = I_72."""
    _, _, pivots = gf2_rref(Q)
    Qpiv = Q[:, pivots]  # 72x72, should be invertible
    Qpiv_inv = gf2_inv(Qpiv)
    Qp = np.zeros((81, 72), dtype=np.int8)
    for i, p in enumerate(pivots):
        Qp[p] = Qpiv_inv[i]
    assert np.array_equal((Q @ Qp) % 2, np.eye(72, dtype=np.int8))
    return Qp

# ---------- Symmetry actions ----------

def sandwich_on_E(F):
    """81x81 action of sandwich (F,F,F) on E = K^9 ⊗ K^9.
    u -> (F⊗F^{-T})u,  v -> (F⊗F^{-T})v.
    On E: (F⊗F^{-T}) ⊗ (F⊗F^{-T}).
    """
    FiT = gf2_inv(F).T % 2
    M9 = np.kron(F, FiT) % 2
    return np.kron(M9, M9).astype(np.int8) % 2

def sandwich_on_W(F):
    """9x9 action of sandwich (F,F,F) on W=C space: R⊗P^{-T} = F⊗F^{-T}."""
    FiT = gf2_inv(F).T % 2
    return np.kron(F, FiT).astype(np.int8) % 2

def project_action(g81, Q, Qp):
    """Induced 72x72 action on E/L: g_bar = Q g81 Qp."""
    return (Q @ g81 @ Qp).astype(np.int8) % 2

# ---------- Eigenspace analysis ----------

def eigenspace_analysis(g_bar, label="g"):
    """Decompose 72-dim E/L under g (order dividing 7 or 3, etc.)."""
    n = g_bar.shape[0]
    I = np.eye(n, dtype=np.int8)
    
    results = {}
    
    # x^7-1 = (x+1)(x^3+x+1)(x^3+x^2+1) over F_2
    # Check powers
    g2 = (g_bar @ g_bar) % 2
    g3 = (g2 @ g_bar) % 2
    g4 = (g3 @ g_bar) % 2
    
    # ker(g - I) = fixed points
    ker1 = gf2_nullspace((g_bar ^ I) % 2)  # XOR = + over F_2
    d1 = ker1.shape[0]
    results['fixed'] = d1
    
    # ker(g^3 + g + I) - corresponds to irrep with min poly x^3+x+1
    mat2 = (g3 ^ g_bar ^ I) % 2
    ker2 = gf2_nullspace(mat2)
    d2 = ker2.shape[0]
    results['type1_x3x1'] = d2
    
    # ker(g^3 + g^2 + I) - corresponds to irrep with min poly x^3+x^2+1
    mat3 = (g3 ^ g2 ^ I) % 2
    ker3 = gf2_nullspace(mat3)
    d3 = ker3.shape[0]
    results['type2_x3x21'] = d3
    
    # For order-3 elements: x^3-1 = (x+1)(x^2+x+1) over F_2
    # ker(g^2 + g + I) - irrep with min poly x^2+x+1
    mat_o3 = (g2 ^ g_bar ^ I) % 2
    ker_o3 = gf2_nullspace(mat_o3)
    results['type_x2x1'] = ker_o3.shape[0]
    
    results['total'] = d1 + d2 + d3
    results['label'] = label
    
    return results

# ---------- Enumerate rank-one points and oracle ----------

def enumerate_rank_one_f2():
    """All 261121 nonzero rank-one 9x9 matrices over F_2, as 81-vectors."""
    points = []
    for u_int in range(1, 512):
        u = np.array([(u_int >> b) & 1 for b in range(9)], dtype=np.int8)
        for v_int in range(1, 512):
            v = np.array([(v_int >> b) & 1 for b in range(9)], dtype=np.int8)
            x = np.outer(u, v).ravel().astype(np.int8)
            points.append(x)
    return np.array(points, dtype=np.int8)

def oracle_test_H(H_basis, Q, Qp, L_basis, rank_one_q, rank_one_x):
    """Test a 13-dim quotient subspace H for the rank-22 condition.
    
    H_basis: k x 72 matrix (rows span H in E/L)
    Returns dict with qrank, xspan_rank, l_intersection_dim, success.
    """
    k = H_basis.shape[0]
    if k == 0:
        return {'qrank': 0, 'xspan_rank': 0, 'l_intersection_dim': 0, 'success': False, 'ro_count': 0}
    
    # Find rank-one points whose quotient image is in H
    # Project each rank-one quotient image onto H
    # A point q is in span(H) iff it's in the row space of H_basis
    # Build augmented matrix and check
    
    # Method: for each rank-one quotient image, check membership in span(H_basis)
    H_rref, H_rank, H_pivots = gf2_rref(H_basis)
    if H_rank < k:
        # H_basis not full rank, reduce
        H_basis = H_rref[:H_rank]
        k = H_rank
    
    # Fast membership test: solve H_basis^T c = q for each q
    # Instead: augment and check rank
    members_idx = []
    for i in range(rank_one_q.shape[0]):
        q = rank_one_q[i]
        aug = np.vstack([H_rref, q.reshape(1, -1)])
        if gf2_rank(aug) == H_rank:
            members_idx.append(i)
    
    if not members_idx:
        return {'qrank': 0, 'xspan_rank': 0, 'l_intersection_dim': 0, 'success': False, 'ro_count': 0}
    
    # Get the actual rank-one points in E
    member_x = rank_one_x[members_idx]  # N x 81
    member_q = rank_one_q[members_idx]  # N x 72
    
    # Check: do these rank-one points span a 22-dim space?
    xrank = gf2_rank(member_x)
    qrank = gf2_rank(member_q)
    
    # Check L-intersection: how much of L is in the span of member_x?
    # L is 9-dim, member_x spans xrank dims
    # L ∩ span(member_x): augment L_basis with member_x and see dim increase
    combined = np.vstack([member_x, L_basis])
    combined_rank = gf2_rank(combined)
    l_in_span = xrank + 9 - combined_rank  # dim(L ∩ span(X))
    
    success = (qrank == 13) and (xrank == 22) and (l_in_span == 9)
    
    return {
        'qrank': qrank,
        'xspan_rank': xrank,
        'l_intersection_dim': int(l_in_span),
        'success': bool(success),
        'ro_count': len(members_idx)
    }

# ---------- Orbit analysis ----------

def rank_one_orbits(g81, rank_one_points, order):
    """Classify rank-one points into orbits under g."""
    n = rank_one_points.shape[0]
    visited = np.zeros(n, dtype=bool)
    
    # Build index: point -> index (use tuple of bytes as key)
    point_to_idx = {}
    for i in range(n):
        key = rank_one_points[i].tobytes()
        point_to_idx[key] = i
    
    fixed = []
    free_orbits = []
    
    for start in range(n):
        if visited[start]:
            continue
        orbit = [start]
        visited[start] = True
        
        current = rank_one_points[start]
        for _ in range(order - 1):
            current = (g81 @ current) % 2
            key = current.tobytes()
            idx = point_to_idx.get(key)
            if idx is None or visited[idx]:
                break
            orbit.append(idx)
            visited[idx] = True
        
        if len(orbit) == 1:
            fixed.append(start)
        else:
            free_orbits.append(orbit)
    
    return fixed, free_orbits

# ---------- Main ----------

def main():
    t0 = time.time()
    out_dir = Path("data/symmetry_search")
    out_dir.mkdir(parents=True, exist_ok=True)
    
    T_flat = build_T333_flat()
    Q = build_quotient_Q(T_flat)
    Qp = build_Q_right_inverse(Q)
    L_basis = T_flat.T % 2  # 9x81, rows span L
    
    print(f"T flat: {T_flat.shape}, Q: {Q.shape}, Q@T=0: {np.all((Q @ T_flat) % 2 == 0)}")
    
    # GL_3(F_2) generators
    F7 = np.array([[0,0,1],[1,0,1],[0,1,0]], dtype=np.int8)  # companion of x^3+x+1, order 7
    T2 = np.array([[1,1,0],[0,1,0],[0,0,1]], dtype=np.int8)  # transvection, order 2
    F3 = np.array([[0,1,0],[0,0,1],[1,0,0]], dtype=np.int8)  # cyclic perm, order 3
    
    # Verify orders
    assert np.array_equal(gf2_matpow(F7, 7), np.eye(3, dtype=np.int8))
    assert np.array_equal(gf2_matpow(T2, 2), np.eye(3, dtype=np.int8))
    assert np.array_equal(gf2_matpow(F3, 3), np.eye(3, dtype=np.int8))
    print("Generator orders verified: F7^7=I, T2^2=I, F3^3=I")
    
    # Build sandwich actions on E
    g7_E = sandwich_on_E(F7)
    g2_E = sandwich_on_E(T2)
    g3_E = sandwich_on_E(F3)
    
    # Verify they preserve T (i.e., g T = T h for some h on W)
    for name, gE, F in [("F7", g7_E, F7), ("T2", g2_E, T2), ("F3", g3_E, F3)]:
        hW = sandwich_on_W(F)
        check = (gE @ T_flat - T_flat @ hW) % 2
        print(f"  {name}: g@T = T@h: {np.all(check == 0)}")
    
    # Project to E/L
    g7_bar = project_action(g7_E, Q, Qp)
    g2_bar = project_action(g2_E, Q, Qp)
    g3_bar = project_action(g3_E, Q, Qp)
    
    # Verify: these are invertible and have correct orders on E/L
    assert np.array_equal(gf2_matpow(g7_bar, 7), np.eye(72, dtype=np.int8))
    assert np.array_equal(gf2_matpow(g2_bar, 2), np.eye(72, dtype=np.int8))
    assert np.array_equal(gf2_matpow(g3_bar, 3), np.eye(72, dtype=np.int8))
    print("Projected actions have correct orders on E/L")
    
    # ===== Eigenspace analysis =====
    print("\n=== Eigenspace decomposition on E/L ===")
    
    # Order-7 sandwich
    res7 = eigenspace_analysis(g7_bar, "F7_sandwich")
    print(f"\nOrder-7 (F7 sandwich):")
    print(f"  Fixed: {res7['fixed']}")
    print(f"  x^3+x+1 block: {res7['type1_x3x1']} (should be 3k)")
    print(f"  x^3+x^2+1 block: {res7['type2_x3x21']} (should be 3k)")
    print(f"  Total: {res7['total']} (should be 72)")
    
    # Order-3 sandwich  
    res3 = eigenspace_analysis(g3_bar, "F3_sandwich")
    print(f"\nOrder-3 (F3 sandwich):")
    print(f"  Fixed: {res3['fixed']}")
    print(f"  x^2+x+1 block: {res3['type_x2x1']} (should be 2k)")
    print(f"  Total fixed + x^2+x+1: {res3['fixed'] + res3['type_x2x1']} (should be 72)")
    
    # Order-2 transvection
    res2 = eigenspace_analysis(g2_bar, "T2_sandwich")
    print(f"\nOrder-2 (T2 sandwich):")
    print(f"  Fixed: {res2['fixed']}")
    
    # Also decompose L under each element
    print("\n=== L decomposition ===")
    for name, F in [("F7", F7), ("T2", T2), ("F3", F3)]:
        h = sandwich_on_W(F)
        I9 = np.eye(9, dtype=np.int8)
        fix_L = gf2_nullspace((h ^ I9) % 2).shape[0]
        print(f"  {name}: dim(Fix ∩ L) = {fix_L}")
    
    # ===== Joint fixed subspace (full sandwich group) =====
    print("\n=== Joint fixed subspace of <F7, T2> on E/L ===")
    both = np.vstack([(g7_bar ^ np.eye(72, dtype=np.int8)) % 2,
                      (g2_bar ^ np.eye(72, dtype=np.int8)) % 2])
    joint_fix = gf2_nullspace(both)
    print(f"  dim(Fix(<F7,T2>)) = {joint_fix.shape[0]}")
    
    # Also with F3
    three = np.vstack([both, (g3_bar ^ np.eye(72, dtype=np.int8)) % 2])
    joint_fix3 = gf2_nullspace(three)
    print(f"  dim(Fix(<F7,T2,F3>)) = {joint_fix3.shape[0]}")
    
    # ===== Rank-one orbit analysis for order-7 =====
    print("\n=== Rank-one orbit analysis ===")
    print("Enumerating rank-one points...")
    ro_points = enumerate_rank_one_f2()
    ro_q = (Q @ ro_points.T).T % 2  # quotient images
    print(f"  {ro_points.shape[0]} rank-one points, quotient images computed")
    
    fixed7, free7 = rank_one_orbits(g7_E, ro_points, 7)
    print(f"\nOrder-7 orbits:")
    print(f"  Fixed rank-one points: {len(fixed7)}")
    print(f"  Free orbits (size 7): {len(free7)}")
    print(f"  Total: {len(fixed7) + 7*len(free7)} (should be 261121)")
    
    fixed3, free3 = rank_one_orbits(g3_E, ro_points, 3)
    print(f"\nOrder-3 orbits:")
    print(f"  Fixed rank-one points: {len(fixed3)}")
    print(f"  Free orbits (size 3): {len(free3)}")
    print(f"  Total: {len(fixed3) + 3*len(free3)} (should be 261121)")
    
    # ===== Feasibility analysis =====
    print("\n=== Invariant 13-plane enumeration feasibility ===")
    
    # For order-7: invariant subspaces decompose as
    # (k0-dim in fixed) + (k1 copies of 3-dim type1) + (k2 copies of 3-dim type2)
    # with k0 + 3*k1 + 3*k2 = 13
    
    f0 = res7['fixed']
    m1 = res7['type1_x3x1'] // 3 if res7['type1_x3x1'] % 3 == 0 else -1
    m2 = res7['type2_x3x21'] // 3 if res7['type2_x3x21'] % 3 == 0 else -1
    
    print(f"\nOrder-7 invariant 13-planes:")
    print(f"  Fixed dim on E/L: {f0}")
    print(f"  Type1 irrep copies: {m1}")
    print(f"  Type2 irrep copies: {m2}")
    
    # Gaussian binomial
    def gaussian_binom(n, k, q):
        """Compute [n choose k]_q."""
        if k < 0 or k > n: return 0
        if k == 0 or k == n: return 1
        num = 1
        den = 1
        for i in range(k):
            num *= (q**(n-i) - 1)
            den *= (q**(i+1) - 1)
        return num // den
    
    total_count = 0
    decomp_table = []
    for k0 in range(min(f0, 13) + 1):
        rem = 13 - k0
        if rem % 3 != 0 and rem < 3 * (m1 + m2 + 1): 
            # Try all valid (k1,k2)
            pass
        for k1 in range(min(m1, rem // 3) + 1):
            k2_needed = rem - 3*k1
            if k2_needed < 0 or k2_needed % 3 != 0: continue
            k2 = k2_needed // 3
            if k2 > m2: continue
            # Count
            c0 = gaussian_binom(f0, k0, 2)
            c1 = gaussian_binom(m1, k1, 8)  # F_8 subspaces
            c2 = gaussian_binom(m2, k2, 8)
            count = c0 * c1 * c2
            total_count += count
            decomp_table.append({
                'k0': k0, 'k1': k1, 'k2': k2,
                'count_fixed': c0, 'count_type1': c1, 'count_type2': c2,
                'total': count
            })
    
    print(f"\n  Dimension decompositions and counts:")
    for d in decomp_table:
        print(f"    ({d['k0']},{d['k1']},{d['k2']}): {d['count_fixed']} × {d['count_type1']} × {d['count_type2']} = {d['total']}")
    print(f"  TOTAL invariant 13-planes: {total_count}")
    
    # For order-3: invariant subspaces decompose as
    # (k0-dim in fixed) + (k1 copies of 2-dim type)
    # with k0 + 2*k1 = 13
    f0_3 = res3['fixed']
    m1_3 = res3['type_x2x1'] // 2 if res3['type_x2x1'] % 2 == 0 else -1
    
    print(f"\nOrder-3 invariant 13-planes:")
    print(f"  Fixed dim: {f0_3}, irrep copies: {m1_3}")
    
    total3 = 0
    for k0 in range(min(f0_3, 13) + 1):
        rem = 13 - k0
        if rem % 2 != 0: continue
        k1 = rem // 2
        if k1 > m1_3: continue
        c0 = gaussian_binom(f0_3, k0, 2)
        c1 = gaussian_binom(m1_3, k1, 4)
        total3 += c0 * c1
        print(f"    ({k0},{k1}): {c0} × {c1} = {c0*c1}")
    print(f"  TOTAL: {total3}")
    
    # ===== Test known seeds under symmetry =====
    print("\n=== Known seed quotient spans vs symmetry ===")
    
    schemes_dir = Path("data/fmm_r23_schemes")
    for name in ["cn122", "serendipitous_8d34", "naive_c88"]:
        path = schemes_dir / f"{name}_qmm.npz"
        if not path.exists():
            print(f"  {name}: file not found")
            continue
        d = np.load(str(path))
        U, V, W = d['U'] % 2, d['V'] % 2, d['W'] % 2
        # Build UV columns
        X = np.array([(np.outer(U[i], V[i]) % 2).ravel() for i in range(U.shape[0])], dtype=np.int8)
        # Check g7-invariance of span
        gX = np.array([(g7_E @ X[i]) % 2 for i in range(X.shape[0])], dtype=np.int8)
        span_X = gf2_rank(X)
        combined = np.vstack([X, gX])
        span_combined = gf2_rank(combined)
        is_inv = (span_combined == span_X)
        print(f"  {name}: X rank={span_X}, g7(X) combined rank={span_combined}, g7-invariant={is_inv}")
    
    # ===== Save results =====
    results = {
        'purpose': 'Symmetry-invariant analysis of E/L for rank-22 search over F_2',
        'eigenspace_order7': res7,
        'eigenspace_order3': res3,
        'eigenspace_order2': res2,
        'joint_fixed_F7_T2': int(joint_fix.shape[0]),
        'joint_fixed_F7_T2_F3': int(joint_fix3.shape[0]),
        'rank_one_orbits_order7': {
            'fixed': len(fixed7),
            'free_size7': len(free7),
            'total_check': len(fixed7) + 7 * len(free7)
        },
        'rank_one_orbits_order3': {
            'fixed': len(fixed3),
            'free_size3': len(free3),
            'total_check': len(fixed3) + 3 * len(free3)
        },
        'invariant_13planes_order7': {
            'decompositions': decomp_table,
            'total': total_count
        },
        'invariant_13planes_order3': {
            'total': total3
        },
        'elapsed': time.time() - t0
    }
    
    out_path = out_dir / "symmetry_eigenspace_analysis.json"
    with open(out_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nSaved to {out_path}")
    print(f"Total time: {time.time()-t0:.1f}s")

if __name__ == '__main__':
    main()
