#!/usr/bin/env python3
"""
analysis: First-order annihilator perturbation analysis for BILR (2,7).

Question: can any infinitesimal SL_3 deformation of the 7 free orbits
drop the catalecticant rank of the residual cubic from 2 to 1?

If not, the (1,7) cyclic rank-22 skeleton is first-order infeasible.
"""
import numpy as np, itertools, json, sys
from pathlib import Path

OUT = Path(__file__).resolve().parent.parent / 'data' / 'bilr_27'
OUT.mkdir(parents=True, exist_ok=True)

def mat2vec(M):
    return np.array(M, dtype=np.int64).flatten()

# ── BILR (2,7) scheme ─────────────────────────────────────────────────
cubes = [
    mat2vec([[1,0,0],[0,0,1],[0,0,1]]),
    mat2vec([[0,0,0],[0,1,-1],[0,0,0]]),
]

orbits = [
    (mat2vec([[0,1,0],[0,0,1],[0,0,0]]), mat2vec([[0,0,0],[0,1,-1],[0,1,-1]]), mat2vec([[0,0,0],[1,0,-1],[0,0,0]])),
    (mat2vec([[0,-1,1],[0,0,0],[0,0,0]]), mat2vec([[0,0,0],[0,0,0],[0,0,1]]), mat2vec([[0,0,0],[0,0,0],[1,0,0]])),
    (mat2vec([[1,0,0],[1,0,0],[0,0,0]]), mat2vec([[0,-1,1],[0,0,0],[0,0,0]]), mat2vec([[0,0,0],[0,0,0],[0,1,0]])),
    (mat2vec([[1,0,0],[0,0,1],[0,0,0]]), mat2vec([[0,1,0],[0,0,1],[0,0,1]]), mat2vec([[0,0,0],[1,0,-1],[0,1,-1]])),
    (mat2vec([[1,0,0],[0,0,0],[0,0,0]]), mat2vec([[0,0,1],[0,0,1],[0,0,1]]), mat2vec([[0,0,0],[0,0,0],[1,-1,0]])),
    (mat2vec([[0,0,0],[0,0,1],[0,0,0]]), mat2vec([[0,1,0],[0,1,0],[0,1,0]]), mat2vec([[0,0,0],[-1,1,0],[0,0,0]])),
    (mat2vec([[0,0,0],[0,0,1],[0,0,1]]), mat2vec([[1,0,0],[1,0,0],[1,0,0]]), mat2vec([[-1,1,0],[0,0,0],[0,0,0]])),
]

# ── Build residual catalecticant ──────────────────────────────────────
def build_D_and_Cat():
    """Build third-derivative tensor D and catalecticant Cat of residual."""
    D = np.zeros((9,9,9), dtype=np.int64)
    # tr(M^3)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a,b,c = 3*i+j, 3*j+k, 3*k+i
                for p,q,r in itertools.permutations([a,b,c]):
                    D[p,q,r] += 1
    # -3 * orbit contributions
    for U,V,W in orbits:
        for a in range(9):
            for b in range(9):
                for c in range(9):
                    for pa,pb,pc in itertools.permutations([a,b,c]):
                        D[a,b,c] -= 3*(U[pa]*V[pb]*W[pc])
    # Catalecticant
    quad_list = [(b,c) for b in range(9) for c in range(b,9)]
    Cat = np.zeros((9, len(quad_list)), dtype=np.int64)
    for a in range(9):
        for qi,(b,c) in enumerate(quad_list):
            Cat[a, qi] = D[a,b,c]
    return D, Cat, quad_list

# ── sl_3 basis ────────────────────────────────────────────────────────
def sl3_basis():
    """8 generators of sl_3 as 3x3 integer matrices."""
    basis = []
    # Off-diagonal
    for i in range(3):
        for j in range(3):
            if i != j:
                M = np.zeros((3,3), dtype=np.int64)
                M[i,j] = 1
                basis.append(M)
    # Diagonal traceless
    M = np.zeros((3,3), dtype=np.int64); M[0,0]=1; M[1,1]=-1
    basis.append(M)
    M = np.zeros((3,3), dtype=np.int64); M[1,1]=1; M[2,2]=-1
    basis.append(M)
    return basis

# ── Perturbation catalecticant ────────────────────────────────────────
def compute_dCat(orbit_idx, X_3x3, quad_list):
    """
    Compute the derivative of the catalecticant when orbit `orbit_idx`
    is perturbed by sl_3 element X.

    Internal SL_3 action on orbit (U,V,W):
    The three vectors form a 9x3 matrix [U|V|W].
    Right multiplication by exp(eps*X):
      (dU, dV, dW) = ([U|V|W] * X)[:, 0], [:, 1], [:, 2]
    i.e., dU = X[0,0]*U + X[1,0]*V + X[2,0]*W, etc.

    The perturbation of -3*sum_perms U_a V_b W_c gives:
    dD[a,b,c] = -3 * sum_perms(a,b,c) [dU_p V_q W_r + U_p dV_q W_r + U_p V_q dW_r]
    """
    U, V, W = orbits[orbit_idx]
    X = X_3x3

    dU = X[0,0]*U + X[1,0]*V + X[2,0]*W
    dV = X[0,1]*U + X[1,1]*V + X[2,1]*W
    dW = X[0,2]*U + X[1,2]*V + X[2,2]*W

    dD = np.zeros((9,9,9), dtype=np.int64)
    for a in range(9):
        for b in range(9):
            for c in range(9):
                for pa,pb,pc in itertools.permutations([a,b,c]):
                    dD[a,b,c] -= 3*(dU[pa]*V[pb]*W[pc] +
                                     U[pa]*dV[pb]*W[pc] +
                                     U[pa]*V[pb]*dW[pc])

    dCat = np.zeros((9, len(quad_list)), dtype=np.int64)
    for a in range(9):
        for qi, (b,c) in enumerate(quad_list):
            dCat[a, qi] = dD[a,b,c]
    return dCat

def main():
    D, Cat, quad_list = build_D_and_Cat()
    basis = sl3_basis()
    print(f"Cat shape: {Cat.shape}, sl3 basis: {len(basis)}")

    # SVD of Cat
    Cat_f = Cat.astype(np.float64)
    U_svd, S_svd, Vt_svd = np.linalg.svd(Cat_f, full_matrices=True)
    rank_cat = np.sum(S_svd > 1e-10)
    print(f"Cat SVD rank: {rank_cat}, singular values: {S_svd[:4]}")

    # Row space: first 2 right singular vectors  
    # Project Cat to 9x2 via the row-space basis
    row_basis = Vt_svd[:rank_cat, :]  # 2x45
    Cat_proj = Cat_f @ row_basis.T    # 9x2

    # Compute all 56 perturbation catalecticants
    dCats = []
    labels = []
    for s in range(7):
        for xi, X in enumerate(basis):
            dCat = compute_dCat(s, X, quad_list)
            dCats.append(dCat)
            labels.append(f"orbit{s}_sl3gen{xi}")
    print(f"Computed {len(dCats)} perturbation catalecticants")

    # Project each dCat to the 2D row space
    dCat_projs = [dC.astype(np.float64) @ row_basis.T for dC in dCats]  # each 9x2

    # ── Minors analysis ──────────────────────────────────────────────
    # For the 9x2 projected matrix, the 36 minors are:
    # M_{ij} = Cat_proj[i,0]*Cat_proj[j,1] - Cat_proj[i,1]*Cat_proj[j,0]  for i<j
    minors_info = []
    for i in range(9):
        for j in range(i+1, 9):
            val = Cat_proj[i,0]*Cat_proj[j,1] - Cat_proj[i,1]*Cat_proj[j,0]
            minors_info.append((i, j, val))

    nonzero_minors = [(i,j,v) for i,j,v in minors_info if abs(v) > 1e-10]
    zero_minors = [(i,j,v) for i,j,v in minors_info if abs(v) <= 1e-10]
    print(f"\nNonzero 2x2 minors: {len(nonzero_minors)} / 36")
    print(f"Zero 2x2 minors: {len(zero_minors)} / 36")

    # For rank to drop from 2 to 1: ALL 36 minors must vanish.
    # At first order, the derivative of minor M_{ij} w.r.t. alpha_k is:
    # dM_{ij}/dalpha_k = dCat_proj_k[i,0]*Cat_proj[j,1] + Cat_proj[i,0]*dCat_proj_k[j,1]
    #                  - dCat_proj_k[i,1]*Cat_proj[j,0] - Cat_proj[i,1]*dCat_proj_k[j,0]

    # Build the first-order constraint matrix (nonzero minors)
    A_rows = []
    for i,j,v in nonzero_minors:
        row = np.zeros(len(dCats))
        for k, dCp in enumerate(dCat_projs):
            row[k] = (dCp[i,0]*Cat_proj[j,1] + Cat_proj[i,0]*dCp[j,1]
                      - dCp[i,1]*Cat_proj[j,0] - Cat_proj[i,1]*dCp[j,0])
        A_rows.append(row)

    A = np.array(A_rows)
    print(f"\nFirst-order constraint matrix shape: {A.shape}")
    rank_A = np.linalg.matrix_rank(A, tol=1e-8)
    print(f"Constraint matrix rank: {rank_A}")
    kernel_dim = len(dCats) - rank_A
    print(f"Kernel dimension (directions that could first-order drop rank): {kernel_dim}")

    if kernel_dim > 0:
        # Find the kernel
        U_a, S_a, Vt_a = np.linalg.svd(A, full_matrices=True)
        kernel = Vt_a[rank_A:, :].T  # 56 x kernel_dim
        print(f"Kernel basis shape: {kernel.shape}")

        # For each kernel direction, verify it actually makes all nonzero minors vanish
        for ki in range(min(kernel_dim, 5)):
            alpha = kernel[:, ki]
            dCat_combined = sum(alpha[k] * dCats[k].astype(float) for k in range(len(dCats)))
            dCat_proj_comb = dCat_combined @ row_basis.T
            # Check all minor derivatives
            max_deriv = 0
            for i,j,v in nonzero_minors:
                dval = (dCat_proj_comb[i,0]*Cat_proj[j,1] + Cat_proj[i,0]*dCat_proj_comb[j,1]
                       - dCat_proj_comb[i,1]*Cat_proj[j,0] - Cat_proj[i,1]*dCat_proj_comb[j,0])
                max_deriv = max(max_deriv, abs(dval))
            print(f"  Kernel vec {ki}: max minor derivative = {max_deriv:.2e}")

            # But we also need to check: does this direction actually change the
            # catalecticant in a useful way? Check if the full Cat + eps*dCat
            # approaches rank 1 along this direction.
            # Compute the Cat + eps*dCat for small eps and check rank
            for eps in [0.01, 0.1, 1.0]:
                Cat_pert = Cat_f + eps * dCat_combined
                U_p, S_p, _ = np.linalg.svd(Cat_pert)
                r_p = np.sum(S_p > 1e-8 * S_p[0])
                print(f"    eps={eps}: sv = [{S_p[0]:.4f}, {S_p[1]:.4f}, {S_p[2]:.6f}], rank={r_p}")

        # Also check: are any kernel directions pure stabilizer directions?
        # The global Stab(omega) acts on all 7 orbits simultaneously.
        # A global sl_3 direction X acts as the same X on all orbits.
        # Check if the kernel contains such global directions.
        print("\nChecking if kernel contains global sl_3 directions...")
        for xi, X in enumerate(basis):
            # Global direction: alpha_k = 1 for all k that correspond to X on any orbit
            alpha_global = np.zeros(len(dCats))
            for s in range(7):
                k = s * len(basis) + xi
                alpha_global[k] = 1.0
            # Project onto kernel
            proj = kernel @ (kernel.T @ alpha_global)
            residual = alpha_global - proj
            rel_residual = np.linalg.norm(residual) / np.linalg.norm(alpha_global)
            in_kernel = rel_residual < 1e-6
            if in_kernel:
                print(f"  sl3_gen_{xi}: IN kernel (residual {rel_residual:.2e})")
    else:
        print("\n*** RESULT: No first-order perturbation can drop catalecticant rank ***")
        print("*** The (1,7) cyclic rank-22 skeleton is FIRST-ORDER BLOCKED ***")
        print("*** at the BILR (2,7) point under internal SL_3 deformations ***")

    # ── Also: check whether the full catalecticant perturbation space ──
    # spans enough of the row-complement.
    # The 9x45 catalecticant has 2-dim row space and 7-dim annihilator.
    # Perturbations act on the 9x45 matrix. For rank to drop, the perturbation
    # must kill one row-space direction while adding nothing new.

    # Alternative test: project the 56 perturbations to the 7-dim annihilator
    # (left kernel) and check if they can make the annihilator grow to 8-dim.
    # For ann dim to grow: the perturbed Cat must have a new left-kernel vector.
    # If v is the new kernel vector (v^T Cat_pert = 0), then at first order:
    # v^T dCat + dv^T Cat = 0.
    # For v not in the current kernel: v = v_rowspace + v_ann.
    # If v is purely in the row space: v_rowspace^T dCat = 0, but v_rowspace^T Cat != 0.
    # So we need v^T dCat to be in the column space of Cat^T... this is getting circular.

    # The cleanest formulation: Let P_ann = projection onto the annihilator.
    # For rank drop, we need P_ann * (Cat + eps*dCat) to have a larger kernel.
    # But P_ann * Cat = 0, so P_ann * (Cat + eps*dCat) = eps * P_ann * dCat.
    # For the perturbed matrix to have rank <= 1: the 9x45 matrix Cat + eps*dCat
    # restricted to a specific 2D row space must collapse. The analysis above
    # via minors is the correct approach.

    # Save results
    results = {
        'n_perturbation_dirs': len(dCats),
        'cat_rank': int(rank_cat),
        'n_nonzero_minors': len(nonzero_minors),
        'n_zero_minors': len(zero_minors),
        'constraint_matrix_shape': list(A.shape),
        'constraint_rank': int(rank_A),
        'first_order_kernel_dim': int(kernel_dim),
        'conclusion': 'first-order blocked' if kernel_dim == 0 else 'first-order open'
    }
    out_path = OUT / 'annihilator_perturbation.json'
    out_path.write_text(json.dumps(results, indent=2) + '\n')
    print(f"\nSaved {out_path}")

if __name__ == '__main__':
    main()
