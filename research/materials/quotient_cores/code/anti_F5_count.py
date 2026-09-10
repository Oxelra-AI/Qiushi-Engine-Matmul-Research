#!/usr/bin/env python3
"""analysis: F5 anti-sector decomposable count.

F3 has no sqrt(-1) and analysis found exactly 8 decomposable bivectors in the 
Laderman anti span. The review notes this may be a field artifact.
F5 contains i (2^2 = 4 = -1 mod 5), so run the same count there.
"""

import numpy as np
from pathlib import Path
import json

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA = WS / "data" / "S3_analysis"
DATA.mkdir(parents=True, exist_ok=True)

def E(i, j):
    M = np.zeros((3,3), dtype=int)
    M[i,j] = 1
    return M

terms = [
    (E(0,0)+E(0,1)+E(0,2)-E(1,0)-E(1,1)-E(2,1)-E(2,2), E(1,1), E(1,0)),
    (E(0,0)-E(1,0), -E(0,1)+E(1,1), E(0,1)+E(1,1)),
    (E(1,1), -E(0,0)+E(0,1)+E(1,0)-E(1,1)-E(1,2)-E(2,0)+E(2,2), E(0,1)),
    (-E(0,0)+E(1,0)+E(1,1), E(0,0)-E(0,1)+E(1,1), E(1,0)+E(0,1)+E(1,1)),
    (E(1,0)+E(1,1), -E(0,0)+E(0,1), E(1,0)+E(1,1)),
    (E(0,0), E(0,0), E(0,0)+E(1,0)+E(2,0)+E(0,1)+E(1,1)+E(0,2)+E(2,2)),
    (-E(0,0)+E(2,0)+E(2,1), E(0,0)-E(0,2)+E(1,2), E(2,0)+E(0,2)+E(2,2)),
    (-E(0,0)+E(2,0), E(0,2)-E(1,2), E(0,2)+E(2,2)),
    (E(2,0)+E(2,1), -E(0,0)+E(0,2), E(2,0)+E(2,2)),
    (E(0,0)+E(0,1)+E(0,2)-E(1,1)-E(1,2)-E(2,0)-E(2,1), E(1,2), E(2,0)),
    (E(2,1), -E(0,0)+E(0,2)+E(1,0)-E(1,1)-E(1,2)-E(2,0)+E(2,1), E(0,2)),
    (-E(0,2)+E(2,1)+E(2,2), E(1,1)+E(2,0)-E(2,1), E(1,0)+E(0,2)+E(1,2)),
    (E(0,2)-E(2,2), E(1,1)-E(2,1), E(0,2)+E(1,2)),
    (E(0,2), E(2,0), E(0,0)+E(1,0)+E(2,0)+E(0,1)+E(2,1)+E(0,2)+E(1,2)),
    (E(2,1)+E(2,2), -E(2,0)+E(2,1), E(1,0)+E(1,2)),
    (-E(0,2)+E(1,1)+E(1,2), E(1,2)+E(2,0)-E(2,2), E(2,0)+E(0,1)+E(2,1)),
    (E(0,2)-E(1,2), E(1,2)-E(2,2), E(0,1)+E(2,1)),
    (E(1,1)+E(1,2), -E(2,0)+E(2,2), E(2,0)+E(2,1)),
    (E(0,1), E(1,0), E(0,0)),
    (E(1,2), E(2,1), E(1,1)),
    (E(1,0), E(0,2), E(2,1)),
    (E(2,0), E(0,1), E(1,2)),
    (E(2,2), E(2,2), E(2,2)),
]

def transport_and_count(p, delta, R_cols):
    """Transport Laderman to standard tau, extract anti bivectors, count decomposables."""
    R = np.array(R_cols, dtype=int).T % p  # R_cols are COLUMNS
    
    # Standard tau coordinates: permutation from analysis
    pi12 = E(0,1) + E(1,0) + E(2,2)
    eps1 = np.diag([-1,1,1])
    eps2 = np.diag([1,-1,1])
    
    Q_mat = np.array([[0,1,0],[-1,0,0],[0,0,1]], dtype=int) % p  # eps1 @ pi12
    # Q = eps1 @ pi12 from analysis
    
    def matmul(A, B, p):
        n = A.shape[0]
        C = np.zeros((n,n), dtype=int)
        for i in range(n):
            for j in range(n):
                C[i,j] = sum(int(A[i,k])*int(B[k,j]) for k in range(n)) % p
        return C
    
    def mat_inv(M, p):
        d = (int(M[0,0])*(int(M[1,1])*int(M[2,2])-int(M[1,2])*int(M[2,1]))
            -int(M[0,1])*(int(M[1,0])*int(M[2,2])-int(M[1,2])*int(M[2,0]))
            +int(M[0,2])*(int(M[1,0])*int(M[2,1])-int(M[1,1])*int(M[2,0]))) % p
        if d == 0: return None
        from functools import reduce
        def egcd(a, b):
            if a == 0: return b, 0, 1
            g, x, y = egcd(b%a, a)
            return g, y-(b//a)*x, x
        di = egcd(d, p)[1] % p
        adj = np.zeros((3,3), dtype=int)
        for i in range(3):
            for j in range(3):
                mn = np.delete(np.delete(M, i, 0), j, 1)
                cof = (int(mn[0,0])*int(mn[1,1]) - int(mn[0,1])*int(mn[1,0])) % p
                adj[j,i] = ((-1)**(i+j) * cof * di) % p
        return adj % p
    
    Q_inv = mat_inv(Q_mat, p)
    R_inv = mat_inv(R, p)
    
    # Transport each term: (a,b,c) -> (Q a R^T, R b Q^T, ... )
    # From analysis: g = (Q, R) sandwich acts as a -> Q a R^T (9-vec Kronecker)
    transported = []
    for a0, b0, c0 in terms:
        a_new = matmul(matmul(Q_mat, a0 % p, p), R.T % p, p) % p
        b_new = matmul(matmul(R, b0 % p, p), Q_mat.T % p, p) % p
        
        # Third factor: need to be careful about convention
        # The sandwich on factor 3 is (R^{-T}, Q^{-T})? Need to check.
        # From T_{333} stabilizer: (Q⊗R^{-T}, R⊗?^{-T}, ?⊗Q^{-T})
        # Actually the standard sandwich is (P, Q, R) acting by a->PaQ^T, b->QbR^T, c->RcP^T
        # With P=Q_mat, Q=R: a->Q_mat a R^T, b->R b Q_mat^T, c->? 
        # Hmm, the convention for the matmul tensor is:
        # (P,Q,R): a->PaQ^{-1}, b->QbR^{-1}, c->RcP^{-1}
        # Let me use the analysis approach: g = (Q, R) means we compute Q a_l Q_inv^T (etc.)
        # Actually from analysis the transport is verified, so let me just compute the
        # bivectors directly from the transported first slice.
        
        transported.append((a_new, b_new))
    
    # Standard tau permutation (from analysis)
    tau_perm = [0,4,5,3,1,2,15,17,16,9,13,11,14,10,12,6,8,7,18,21,20,19,22]
    fixed_idx = [i for i in range(23) if tau_perm[i] == i]
    free_pairs = []
    seen = set()
    for i in range(23):
        j = tau_perm[i]
        if j != i and i not in seen:
            free_pairs.append((i, j))
            seen.add(i); seen.add(j)
    
    # Compute first-slice matrix for each term: M_l = v_l w_l^T in K^{9x9}
    # where v_l, w_l are the 9-vectors of the first two transported factors
    # Actually we need the "pairing" matrix. Each term contributes to the first slice space.
    # The bivector of a free pair (i, j=tau(i)) is: v_i ∧ w_j - v_j ∧ w_i or similar.
    
    # Actually, the bivector is computed from the two K^9 vectors of the pair.
    # In the tau-invariant decomposition, each free orbit pair (i, tau(i)) has vectors
    # v_i and v_{tau(i)} in K^9 (first-slice coordinates).
    # The bivector is v_i ∧ v_{tau(i)} (the alternating part of the pair's contribution).
    
    # Compute first-slice vectors
    P_mat = np.zeros((9, 9), dtype=int)  # Permutation P(X) from analysis
    for a in range(3):
        for b in range(3):
            P_mat[3*b + (a+b)%3, 3*a+b] = 1  # Corrected L_1 positions
    # Actually let me just use the L_1 basis from analysis: B_{ab} at (3b+k, 3k+a)
    # The first slice of transported term l: extract the 9-vector from transported a_l
    
    # The first-slice 9-vector of term l: flatten(a_l_transported)
    first_vecs = np.zeros((9, 23), dtype=int)
    for l in range(23):
        first_vecs[:, l] = transported[l][0].reshape(-1).astype(int) % p
    
    # Compute bivectors for free pairs
    # bivector of pair (i, j): v_i ∧ v_j in Λ²(K^9)
    # Represented as 36-vector (upper triangle of antisymmetric matrix)
    def wedge(u, v, p):
        """Compute u ∧ v as a 36-vector (entries (i,j) with i<j)."""
        n = len(u)
        w = []
        for i in range(n):
            for j in range(i+1, n):
                w.append((int(u[i]) * int(v[j]) - int(u[j]) * int(v[i])) % p)
        return np.array(w, dtype=int)
    
    bivectors = []
    for i, j in free_pairs:
        bv = wedge(first_vecs[:, i], first_vecs[:, j], p)
        bivectors.append(bv)
    
    # Anti target L_anti: 3-dimensional
    # theta_{ab} = -sum_k e_{ak} ∧ e_{bk} for a<b in {0,1,2}
    # where e_{ij} is the standard basis of K^9 at index 3i+j
    def make_theta(a, b, p):
        n = 9
        w = []
        for i in range(n):
            for j in range(i+1, n):
                val = 0
                for k in range(3):
                    ei_a = 3*a + k; ei_b = 3*b + k
                    if ei_a == i and ei_b == j: val = (val - 1) % p
                    elif ei_a == j and ei_b == i: val = (val + 1) % p
                w.append(val % p)
        return np.array(w, dtype=int)
    
    L_anti = np.column_stack([make_theta(0,1,p), make_theta(0,2,p), make_theta(1,2,p)])
    
    # Check anti span of bivectors
    biv_mat = np.column_stack(bivectors) if bivectors else np.zeros((36, 0), dtype=int)
    anti_span_rank = np.linalg.matrix_rank(biv_mat.astype(float))
    
    # Augment with L_anti
    aug = np.column_stack([biv_mat, L_anti]) if biv_mat.shape[1] > 0 else L_anti
    aug_rank = np.linalg.matrix_rank(aug.astype(float))
    anti_contained = (aug_rank == anti_span_rank) if anti_span_rank >= 3 else False
    
    print(f"\nField F_{p}: {len(free_pairs)} free pairs")
    print(f"  Bivector span rank: {anti_span_rank}")
    print(f"  Augmented with L_anti: {aug_rank}")
    print(f"  L_anti contained: {anti_contained}")
    
    # Count decomposable bivectors in the anti span
    # Project P^{dim-1}(F_p) within the anti span
    if anti_span_rank == 0:
        print(f"  No bivectors to enumerate")
        return {"field": f"F_{p}", "decomposable_count": 0}
    
    # Get basis of anti span
    # Use RREF over F_p
    biv_float = biv_mat.astype(float)
    # Find basis via column selection
    basis_cols = []
    for c in range(biv_mat.shape[1]):
        test = biv_mat[:, basis_cols + [c]].astype(float)
        if np.linalg.matrix_rank(test) == len(basis_cols) + 1:
            basis_cols.append(c)
            if len(basis_cols) == anti_span_rank:
                break
    
    anti_basis = biv_mat[:, basis_cols].astype(int) % p
    dim = anti_span_rank
    
    # Enumerate P^{dim-1}(F_p)
    total_proj = (p**dim - 1) // (p - 1)
    print(f"  Enumerating P^{dim-1}(F_{p}): {total_proj} projective points")
    
    decomposable_count = 0
    decomposable_bivs = []
    
    def is_decomposable(bv, p):
        """Check if bivector (36-vector) is decomposable: rank ≤ 2 as antisym 9x9."""
        # Reconstruct 9x9 antisymmetric matrix
        M = np.zeros((9,9), dtype=int)
        idx = 0
        for i in range(9):
            for j in range(i+1, 9):
                M[i,j] = int(bv[idx]) % p
                M[j,i] = (-int(bv[idx])) % p
                idx += 1
        # Check all 4x4 Pfaffians = 0 (or equivalently rank ≤ 2)
        # rank ≤ 2 iff all 3x3 minors of any half-row extraction vanish
        # Faster: check all 4x4 submatrix determinants
        for i1 in range(9):
            for i2 in range(i1+1, 9):
                for i3 in range(i2+1, 9):
                    for i4 in range(i3+1, 9):
                        sub = np.array([
                            [M[i1,i2], M[i1,i3], M[i1,i4]],
                            [M[i2,i3], M[i2,i4], 0],
                            [M[i3,i4], 0, 0]
                        ], dtype=int)
                        # Pfaffian of 4x4 antisymmetric = M[i1,i2]*M[i3,i4] - M[i1,i3]*M[i2,i4] + M[i1,i4]*M[i2,i3]
                        pf = (int(M[i1,i2])*int(M[i3,i4]) 
                             - int(M[i1,i3])*int(M[i2,i4]) 
                             + int(M[i1,i4])*int(M[i2,i3])) % p
                        if pf != 0:
                            return False
        return True
    
    # Generate all projective points in F_p^dim
    def proj_points(dim, p):
        """Generate all projective points in P^{dim-1}(F_p)."""
        for leading_one_pos in range(dim):
            # First nonzero coordinate is at position leading_one_pos, value 1
            ranges = [range(p) if k > leading_one_pos else ([1] if k == leading_one_pos else [0])
                      for k in range(dim)]
            for combo in itertools.product(*ranges):
                yield np.array(combo, dtype=int)
    
    import itertools
    checked = 0
    for coords in proj_points(dim, p):
        bv = np.zeros(36, dtype=int)
        for k in range(dim):
            bv = (bv + int(coords[k]) * anti_basis[:, k]) % p
        if np.all(bv == 0): continue
        if is_decomposable(bv, p):
            decomposable_count += 1
            decomposable_bivs.append(coords.tolist())
        checked += 1
        if checked % 50000 == 0:
            print(f"    Checked {checked}/{total_proj}, found {decomposable_count} so far")
    
    print(f"  Total decomposable projective bivectors: {decomposable_count}")
    
    return {
        "field": f"F_{p}",
        "delta": delta,
        "free_pairs": len(free_pairs),
        "anti_span_rank": int(anti_span_rank),
        "L_anti_contained": bool(anti_contained),
        "projective_points_checked": checked,
        "decomposable_count": decomposable_count,
    }

# F3 (control, should give 8)
print("=" * 60)
print("F3 anti-sector (control)")
r3 = transport_and_count(3, 2, [[0,0,1],[1,0,0],[1,2,0]])

# F5 (has sqrt(-1))
print("\n" + "=" * 60)
print("F5 anti-sector (has sqrt(-1))")
r5 = transport_and_count(5, 1, [[0,0,2],[0,1,0],[1,0,0]])

results = {"F3": r3, "F5": r5}
path = DATA / "anti_sector_F5_comparison.json"
path.write_text(json.dumps(results, indent=2) + "\n")
print(f"\nSAVED {path}")
print(json.dumps(results, indent=2))
