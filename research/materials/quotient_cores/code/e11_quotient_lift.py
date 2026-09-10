#!/usr/bin/env python3
"""Lift rank-15 quotient decompositions to rank-19 E11 CPDs over F2.

Mathematical construction:
Given prefix P = {u_0,...,u_3} in F2^8 and a rank-15 decomposition of the
A-side quotient tensor Q = sum_j bar_a_j x b_j x c_j, we search for lift
coefficients c_{k,j} in F2 such that the residual

  R_k = T_E11[u_k-slice] - sum_j c_{k,j} (b_j x c_j)

has rank <= 1 for each prefix direction k = 0,...,3.  The four rank-1
conditions are independent, each requiring a search over 2^15 binary
vectors.  Success gives a rank-19 E11 CPD; with the +3 elementary lift,
this yields a rank-22 full T333 decomposition over F2.
"""
from __future__ import annotations
import argparse, json, time, hashlib
from pathlib import Path
import numpy as np

# ---- GF(2) utilities ----

def parity(x: int) -> int:
    return int(x).bit_count() & 1

def bits_to_vec(mask: int, n: int) -> np.ndarray:
    return np.array([(mask >> i) & 1 for i in range(n)], dtype=np.uint8)

def vec_to_mask(v) -> int:
    return sum(int(v[i]) << i for i in range(len(v)))

def gf2_basis(vectors: list[int]) -> list[int]:
    basis: dict[int, int] = {}
    for v in vectors:
        x = int(v)
        while x:
            p = x.bit_length() - 1
            if p in basis:
                x ^= basis[p]
            else:
                basis[p] = x
                break
    return sorted(basis.values(), reverse=True)

def gf2_rank_int(vectors: list[int]) -> int:
    return len(gf2_basis(vectors))

def annihilator_basis(prefix: list[int], n: int = 8) -> list[int]:
    d = gf2_rank_int(prefix)
    candidates = [l for l in range(1, 1 << n) if all(parity(l & v) == 0 for v in prefix)]
    out: list[int] = []
    for l in candidates:
        if gf2_rank_int(out + [l]) > len(out):
            out.append(l)
        if len(out) == n - d:
            break
    assert len(out) == n - d
    return out

def find_dual_vectors(ann_masks: list[int], prefix_masks: list[int], n: int = 8) -> list[int]:
    """Find w_i in F2^n with l_k(w_i) = delta_{ki} for annihilator l_k."""
    d_ann = len(ann_masks)
    M = np.zeros((d_ann, n), dtype=np.uint8)
    for k, l in enumerate(ann_masks):
        for b in range(n):
            M[k, b] = (l >> b) & 1
    duals = []
    for k in range(d_ann):
        target = np.zeros(d_ann, dtype=np.uint8)
        target[k] = 1
        aug = np.hstack([M.copy(), target.reshape(-1, 1)])
        row = 0
        pivots = []
        for col in range(n):
            piv = None
            for r in range(row, d_ann):
                if aug[r, col]:
                    piv = r
                    break
            if piv is None:
                continue
            aug[[row, piv]] = aug[[piv, row]]
            for r in range(d_ann):
                if r != row and aug[r, col]:
                    aug[r] ^= aug[row]
            pivots.append((row, col))
            row += 1
        x = np.zeros(n, dtype=np.uint8)
        for r, c in pivots:
            x[c] = aug[r, n]
        duals.append(vec_to_mask(x))
    return duals

def find_phi_vectors(prefix_masks: list[int], n: int = 8) -> list[int]:
    """Find phi_k in F2^n with parity(phi_k & u_i) = delta_{ki} for prefix u_i."""
    d = len(prefix_masks)
    P = np.zeros((d, n), dtype=np.uint8)
    for i, u in enumerate(prefix_masks):
        for b in range(n):
            P[i, b] = (u >> b) & 1
    phis = []
    for k in range(d):
        target = np.zeros(d, dtype=np.uint8)
        target[k] = 1
        aug = np.hstack([P.copy(), target.reshape(-1, 1)])
        row = 0
        pivots = []
        for col in range(n):
            piv = None
            for r in range(row, d):
                if aug[r, col]:
                    piv = r
                    break
            if piv is None:
                continue
            aug[[row, piv]] = aug[[piv, row]]
            for r in range(d):
                if r != row and aug[r, col]:
                    aug[r] ^= aug[row]
            pivots.append((row, col))
            row += 1
        x = np.zeros(n, dtype=np.uint8)
        for r, c in pivots:
            x[c] = aug[r, n]
        phis.append(vec_to_mask(x))
    return phis

# ---- Tensor construction ----

def build_t333() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T

def build_e11_core() -> np.ndarray:
    return build_t333()[1:, :, :]

def quotient_core(core: np.ndarray, ann: list[int]) -> np.ndarray:
    q = np.zeros((len(ann), core.shape[1], core.shape[2]), dtype=np.uint8)
    for i, l in enumerate(ann):
        for a in range(core.shape[0]):
            if (l >> a) & 1:
                q[i] ^= core[a].astype(np.uint8)
    return q

# ---- Fast rank-1 search ----

def search_rank1_gray(target_rows: list[int], b_masks: list[int], c_masks: list[int]) -> list[int]:
    """Find all subsets S of terms where target XOR sum_{j in S} outer(b_j,c_j) has rank <= 1.
    
    Uses Gray code enumeration for O(1) matrix update per ARTIFACT.
    Returns solution Gray codes (=subset bitmasks).
    """
    n = len(b_masks)
    current = list(target_rows)
    solutions = []

    # Precompute which rows each term affects
    # For term j: affects row i iff bit i of b_masks[j] is set
    # The XOR value for those rows is c_masks[j]

    def is_rank_leq_1():
        ref = 0
        for r in current:
            if r:
                if not ref:
                    ref = r
                elif r != ref:
                    return False
        return True

    if is_rank_leq_1():
        solutions.append(0)

    for step in range(1, 1 << n):
        j = (step & -step).bit_length() - 1  # flipping bit
        bm = b_masks[j]
        cm = c_masks[j]
        for i in range(9):
            if (bm >> i) & 1:
                current[i] ^= cm
        if is_rank_leq_1():
            solutions.append(step ^ (step >> 1))  # Gray code = subset mask

    return solutions

def extract_rank1(rows: list[int]) -> tuple[int, int]:
    """From a rank-1 matrix (rows as 9-bit ints), extract v_mask, w_mask."""
    v = 0
    w = 0
    for i, r in enumerate(rows):
        if r:
            v |= (1 << i)
            w = r
    return v, w

# ---- Main ----

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--core", type=str, default=None)
    ap.add_argument("--pool", type=str, required=True)
    ap.add_argument("--prefix", type=str, required=True)
    ap.add_argument("--outdir", type=str, required=True)
    ap.add_argument("--scheme-idx", type=int, default=-1, help="-1 = try all")
    ap.add_argument("--max-schemes", type=int, default=0, help="0 = no limit")
    ap.add_argument("--stop-on-first", action="store_true")
    args = ap.parse_args()

    t0 = time.time()
    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    prefix = [int(x) for x in args.prefix.split(",")]
    assert len(prefix) == 4, f"Need 4 prefix masks, got {len(prefix)}"
    assert gf2_rank_int(prefix) == 4, "Prefix must span 4 dimensions"

    # E11 core
    if args.core:
        core = np.load(args.core).astype(np.uint8) & 1
    else:
        core = build_e11_core()
    assert core.shape == (8, 9, 9) and int(core.sum()) == 24

    # Annihilator and quotient
    ann = annihilator_basis(prefix, 8)
    assert len(ann) == 4
    Q = quotient_core(core, ann)
    print(f"E11 core nnz={int(core.sum())}  prefix={prefix}  ann={ann}  Q shape={Q.shape} nnz={int(Q.sum())}")

    # Dual vectors for lift
    duals = find_dual_vectors(ann, prefix, 8)
    for k, l in enumerate(ann):
        for i, w in enumerate(duals):
            assert parity(l & w) == (1 if k == i else 0), "Dual verification failed"

    # Phi vectors for extracting V-slices
    phis = find_phi_vectors(prefix, 8)
    for k in range(4):
        for i in range(4):
            assert parity(phis[k] & prefix[i]) == (1 if k == i else 0), "Phi verification failed"

    # Load pool
    pool = np.load(args.pool)
    n_schemes, n_cols = pool.shape
    rank_q = n_cols // 3
    assert rank_q * 3 == n_cols
    print(f"Pool: {n_schemes} schemes of rank {rank_q}")

    if args.scheme_idx >= 0:
        indices = [args.scheme_idx]
    else:
        indices = list(range(n_schemes))
    if args.max_schemes > 0:
        indices = indices[:args.max_schemes]

    results = []
    witness = None

    for idx in indices:
        scheme = pool[idx]
        u_masks = [int(scheme[3*j]) for j in range(rank_q)]
        b_masks = [int(scheme[3*j+1]) for j in range(rank_q)]
        c_masks_q = [int(scheme[3*j+2]) for j in range(rank_q)]

        # Verify quotient decomposition
        Q_check = np.zeros_like(Q)
        for j in range(rank_q):
            for a in range(Q.shape[0]):
                if (u_masks[j] >> a) & 1:
                    for b in range(9):
                        if (b_masks[j] >> b) & 1:
                            for c in range(9):
                                if (c_masks_q[j] >> c) & 1:
                                    Q_check[a, b, c] ^= 1
        qdiff = int(np.sum((Q ^ Q_check) % 2))
        if qdiff != 0:
            results.append({"scheme_idx": idx, "quotient_diff": qdiff, "skip": True})
            continue

        # Initial lifts
        lifts = []
        for j in range(rank_q):
            a = 0
            for i in range(len(duals)):
                if (u_masks[j] >> i) & 1:
                    a ^= duals[i]
            lifts.append(a)

        # Compute residual R = core XOR sum_j lift_j x b_j x c_j (over F2)
        R = core.copy()
        for j in range(rank_q):
            a_vec = bits_to_vec(lifts[j], 8)
            for a in range(8):
                if a_vec[a]:
                    for b in range(9):
                        if (b_masks[j] >> b) & 1:
                            for c in range(9):
                                if (c_masks_q[j] >> c) & 1:
                                    R[a, b, c] ^= 1

        # Extract V-slices using phi vectors
        R_slices = []  # list of 9 lists of 9-bit ints (rows)
        for k in range(4):
            phi_vec = bits_to_vec(phis[k], 8)
            rows = []
            for b in range(9):
                row_val = 0
                for c in range(9):
                    bit = 0
                    for a in range(8):
                        if phi_vec[a]:
                            bit ^= R[a, b, c]
                    if bit & 1:
                        row_val |= (1 << c)
                rows.append(row_val)
            R_slices.append(rows)

        # Verify reconstruction: R should equal sum_k u_k x R_slices[k]
        R_recon = np.zeros((8, 9, 9), dtype=np.uint8)
        for k in range(4):
            u_vec = bits_to_vec(prefix[k], 8)
            for a in range(8):
                if u_vec[a]:
                    for b in range(9):
                        for c in range(9):
                            if (R_slices[k][b] >> c) & 1:
                                R_recon[a, b, c] ^= 1
        recon_diff = int(np.sum((R ^ R_recon) % 2))

        slice_ranks = []
        for k in range(4):
            slice_ranks.append(gf2_rank_int([r for r in R_slices[k] if r]))

        # Search for rank-1 lifts
        dir_solutions = []
        for k in range(4):
            sols = search_rank1_gray(R_slices[k], b_masks, c_masks_q)
            dir_solutions.append(sols)

        n_sols = [len(s) for s in dir_solutions]
        all_solvable = all(n > 0 for n in n_sols)

        rec = {
            "scheme_idx": idx,
            "quotient_verified": True,
            "recon_diff": recon_diff,
            "initial_slice_ranks": slice_ranks,
            "solutions_per_direction": n_sols,
            "all_solvable": all_solvable,
        }

        if all_solvable:
            # Assemble full rank-19 E11 decomposition
            codes = [dir_solutions[k][0] for k in range(4)]

            # Prefix terms: extract v, w from modified residual slices
            full_u, full_v, full_w = [], [], []
            for k in range(4):
                mod_rows = list(R_slices[k])
                for j in range(rank_q):
                    if (codes[k] >> j) & 1:
                        bm = b_masks[j]
                        cm = c_masks_q[j]
                        for i in range(9):
                            if (bm >> i) & 1:
                                mod_rows[i] ^= cm
                v_m, w_m = extract_rank1(mod_rows)
                full_u.append(prefix[k])
                full_v.append(v_m)
                full_w.append(w_m)

            # Quotient terms with adjusted lifts
            for j in range(rank_q):
                a_j = lifts[j]
                for k in range(4):
                    if (codes[k] >> j) & 1:
                        a_j ^= prefix[k]
                full_u.append(a_j)
                full_v.append(b_masks[j])
                full_w.append(c_masks_q[j])

            # Verify
            check = np.zeros((8, 9, 9), dtype=np.uint8)
            for t in range(len(full_u)):
                for a in range(8):
                    if (full_u[t] >> a) & 1:
                        for b in range(9):
                            if (full_v[t] >> b) & 1:
                                for c in range(9):
                                    if (full_w[t] >> c) & 1:
                                        check[a, b, c] ^= 1
            diff = int(np.sum((check ^ core) % 2))

            n_nonzero_prefix = sum(1 for k in range(4) if full_v[k] and full_w[k])
            total_rank = n_nonzero_prefix + rank_q

            rec["e11_rank19_diff"] = diff
            rec["e11_verified"] = diff == 0
            rec["total_rank"] = total_rank
            rec["lift_codes"] = codes
            rec["decomposition"] = {
                "u_masks": full_u,
                "v_masks": full_v,
                "w_masks": full_w,
            }

            if diff == 0:
                print(f"  *** SCHEME {idx}: VERIFIED RANK-{total_rank} E11 CPD! ***")
                # Also lift to full T333
                t333_u = [u << 1 for u in full_u[:n_nonzero_prefix + rank_q]]
                t333_v = list(full_v[:n_nonzero_prefix + rank_q])
                t333_w = list(full_w[:n_nonzero_prefix + rank_q])
                # Add 3 elementary terms
                t333_u.extend([1, 1, 1])
                t333_v.extend([1, 2, 4])
                t333_w.extend([1, 2, 4])
                # Verify full T333
                T333 = build_t333()
                T_check = np.zeros((9, 9, 9), dtype=np.uint8)
                for t in range(len(t333_u)):
                    for a in range(9):
                        if (t333_u[t] >> a) & 1:
                            for b in range(9):
                                if (t333_v[t] >> b) & 1:
                                    for c in range(9):
                                        if (t333_w[t] >> c) & 1:
                                            T_check[a, b, c] ^= 1
                t333_diff = int(np.sum((T_check ^ T333) % 2))
                t333_rank = total_rank + 3
                rec["t333_diff"] = t333_diff
                rec["t333_verified"] = t333_diff == 0
                rec["t333_rank"] = t333_rank
                rec["t333_decomposition"] = {
                    "u_masks": t333_u,
                    "v_masks": t333_v,
                    "w_masks": t333_w,
                }
                if t333_diff == 0:
                    print(f"  *** FULL T333 RANK-{t333_rank} VERIFIED! ***")
                    witness = rec
            else:
                print(f"  Scheme {idx}: assembly diff={diff}")
        else:
            if idx < 5 or idx % 50 == 0:
                print(f"  Scheme {idx}: slice_ranks={slice_ranks} sols={n_sols}")

        results.append(rec)
        if witness and args.stop_on_first:
            break

    elapsed = time.time() - t0
    summary = {
        "purpose": "Lift quotient rank-15 to E11 rank-19 CPD over F2",
        "prefix": prefix,
        "annihilator_basis": ann,
        "dual_vectors": duals,
        "phi_vectors": phis,
        "pool_path": str(args.pool),
        "schemes_tried": len(results),
        "e11_witnesses": sum(1 for r in results if r.get("e11_verified")),
        "t333_witnesses": sum(1 for r in results if r.get("t333_verified")),
        "elapsed_sec": elapsed,
    }
    if witness:
        summary["first_witness"] = witness

    out_path = outdir / "quotient_lift_results.json"
    out_path.write_text(json.dumps(summary, indent=2, sort_keys=True, default=int) + "\n")
    print(f"\nSummary: {summary['schemes_tried']} tried, "
          f"{summary['e11_witnesses']} E11 witnesses, "
          f"{summary['t333_witnesses']} T333 witnesses, "
          f"{elapsed:.1f}s")
    print(f"wrote {out_path}")

if __name__ == "__main__":
    main()
