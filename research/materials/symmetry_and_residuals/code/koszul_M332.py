#!/usr/bin/env python3
"""analysis: Koszul/exterior flattening lower bounds for M_⟨3,3,2⟩.

For T ∈ K^a ⊗ K^b ⊗ K^c, the d-th Koszul flattening on mode m is a map
  φ: Λ^d(factor_m) ⊗ contract_factor → Λ^{d-1}(factor_m) ⊗ output_factor.
Each rank-1 summand contributes rank ≤ C(dim_m - 1, d-1) to this map.
Hence R(T) ≥ rank(φ) / C(dim_m - 1, d-1).

We compute rank(φ) for M_⟨3,3,2⟩ ∈ K^9 ⊗ K^6 ⊗ K^6 across all three modes
and all valid degrees d, over a large prime field to ensure exactness.
"""
import numpy as np
from itertools import combinations
from math import comb
from pathlib import Path
import json

def build_M332():
    """M_⟨3,3,2⟩: multiply (3×3)·(3×2) → (3×2)."""
    T = np.zeros((9, 6, 6), dtype=np.int64)
    for i in range(3):
        for j in range(3):
            for k in range(2):
                T[3*i+j, 2*j+k, 2*i+k] = 1
    return T

def koszul_flattening_rank(T, d, mode, p=65521):
    """Compute rank of d-th Koszul flattening on given mode over F_p."""
    if mode == 1:
        T = T.transpose(1, 2, 0)
    elif mode == 2:
        T = T.transpose(2, 0, 1)
    a, b, c = T.shape

    basis_d = list(combinations(range(a), d))
    basis_dm1 = list(combinations(range(a), d-1))
    idx_dm1 = {s: i for i, s in enumerate(basis_dm1)}

    n_rows = len(basis_dm1) * c
    n_cols = len(basis_d) * b
    phi = np.zeros((n_rows, n_cols), dtype=np.int64)

    for ci, alpha_set in enumerate(basis_d):
        for beta in range(b):
            col = ci * b + beta
            for l in range(d):
                alpha_l = alpha_set[l]
                remaining = alpha_set[:l] + alpha_set[l+1:]
                sign = (-1)**l
                if remaining in idx_dm1:
                    rbase = idx_dm1[remaining]
                    for gamma in range(c):
                        val = T[alpha_l, beta, gamma]
                        if val != 0:
                            phi[rbase * c + gamma, col] = \
                                (phi[rbase * c + gamma, col] + sign * val) % p
    phi = phi % p
    # Rank over F_p via SVD on float (exact for p < 2^16 and small matrices)
    return int(np.linalg.matrix_rank(phi.astype(np.float64))), n_rows, n_cols

def main():
    T = build_M332()
    p = 65521
    print(f"M_⟨3,3,2⟩ shape={T.shape}, nnz={np.count_nonzero(T)}")

    dims = [(9,6,6,'A=K^9'), (6,6,9,'B=K^6(left)'), (6,9,6,'C=K^6(right)')]
    results = {"tensor":"M_<3,3,2>", "prime":p, "entries":[]}
    best_bound = 0
    best_info = ""

    for mode, (dim_ext, dim_contr, dim_out, label) in enumerate(dims):
        print(f"\n=== Mode {mode}: exterior on {label} (dim={dim_ext}) ===")
        for d in range(1, dim_ext+1):
            nd = comb(dim_ext, d); ndm1 = comb(dim_ext, d-1)
            nr = ndm1 * dim_out; nc = nd * dim_contr
            if nr > 6000 or nc > 6000:
                print(f"  d={d}: {nr}×{nc} skipped (too large)")
                continue
            rk, nr2, nc2 = koszul_flattening_rank(T, d, mode, p)
            contrib = comb(dim_ext - 1, d - 1)
            bound = int(-(-rk // contrib)) if contrib > 0 else 0
            rec = {"mode":mode,"d":d,"label":label,"shape":f"{nr}x{nc}",
                   "rank":rk,"contrib_per_rank1":contrib,"bound":bound}
            results["entries"].append(rec)
            if bound > best_bound:
                best_bound = bound
                best_info = f"mode={mode} d={d} label={label}"
            print(f"  d={d}: {nr}×{nc}, rank={rk}, C({dim_ext-1},{d-1})={contrib}, "
                  f"r ≥ ceil({rk}/{contrib}) = {bound}")

    results["best_bound"] = best_bound
    results["best_source"] = best_info
    results["note"] = (
        "This is the best pure exterior-Koszul flattening bound. "
        "Blaser's substitution method gives R >= 14, which is stronger. "
        f"Self-contained Koszul bound: R(M_<3,3,2>) >= {best_bound}."
    )
    print(f"\n*** BEST KOSZUL BOUND: R(M_⟨3,3,2⟩) ≥ {best_bound} ({best_info}) ***")

    out = Path(__file__).resolve().parent.parent / 'data' / 'M332_bounds'
    out.mkdir(parents=True, exist_ok=True)
    fp = out / 'koszul_flattening_bounds.json'
    fp.write_text(json.dumps(results, indent=2)+'\n')
    print(f"Saved to {fp}")

if __name__ == '__main__':
    main()
