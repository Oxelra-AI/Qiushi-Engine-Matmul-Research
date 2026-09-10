#!/usr/bin/env python3
"""this investigation E11 bridge verification and core structure analysis.

Independent reconstruction:
  1. Build T_{3,3,3} over F_2 from definition
  2. Build E11 core via codimension-one restriction (delete a00 slice)
  3. Verify T = T_core_embedded + mask ⊗ T[0,:,:]
  4. Verify removed slice = 3 elementary rank-one terms
  5. Load rank-21 pool control, verify core CPD, lift, verify full T_{333}
  6. Analyze core block structure for the B⊗C factorization surface

Convention: A_{ij} = a[3i+j], B_{jk} = b[3j+k], C_{ik} = c[3i+k].
T[a,b,c] = 1 iff a=3i+j, b=3j+k, c=3i+k for some i,j,k.
E11 mask = 1 (bit 0 = a_{00}), pivot = 0.
Core is T[1:9, :, :]. For E11 the mask has no free bits, so there is no XOR with T[0].
"""
import json, sys
from pathlib import Path
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent  # workspace/
OUTDIR = WS / "data" / "e11_bridge"
OUTDIR.mkdir(parents=True, exist_ok=True)

def build_t333():
    """Standard 9x9x9 matrix multiplication tensor over F_2."""
    T = np.zeros((9,9,9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a, b, c = 3*i+j, 3*j+k, 3*i+k
                T[a,b,c] = 1
    return T

def build_e11_core_direct():
    """Build E11 core: for mask=1 (pivot=0, no free bits), core = T[1:9,:,:].
    
    General formula: T_restr[i] = T[i] XOR (free_bit_i * T[pivot]).
    For E11: mask=1, pivot=0, free = mask ^ (1<<pivot) = 0, so no XOR.
    Core is simply the 8 non-pivot slices.
    """
    T = build_t333()
    core = T[1:9].copy()  # shape (8,9,9), nnz=24
    return core, T

def verify_reconstruction(core, T):
    """Verify T = embed(core) + mask ⊗ T[0,:,:].
    
    For E11 (mask=1, pivot=0, no free bits):
    - embed(core)[0] = 0, embed(core)[i] = core[i-1] for i=1..8
    - mask ⊗ T[0,:,:] contributes T[0] at position 0 only (bit 0 of mask)
    - Reconstruction: T[0] = T[0], T[i] = core[i-1] for i=1..8
    """
    T_recon = np.zeros_like(T)
    T_recon[0] = T[0]  # removed slice contribution (mask bit 0)
    for i in range(1, 9):
        T_recon[i] = core[i-1]  # direct embedding, no XOR for E11
    return bool(np.array_equal(T_recon, T)), int(np.sum(T_recon ^ T))

def check_removed_slice(T):
    """T[0,:,:] should be I_3 in the first 3x3 block of B×C (B_{0k}, C_{0k})."""
    S = T[0]  # 9x9 matrix
    nnz = int(S.sum())
    # Expected: S[b,c] = 1 iff b=k, c=k for k=0,1,2  (a=0 means i=0,j=0, so b=3*0+k=k, c=3*0+k=k)
    expected = np.zeros((9,9), dtype=np.uint8)
    for k in range(3):
        expected[k,k] = 1
    matches = bool(np.array_equal(S, expected))
    # The three rank-one terms: (mask=1, b=1<<k, c=1<<k) for k=0,1,2
    terms = [(1, 1<<k, 1<<k) for k in range(3)]
    return matches, nnz, terms

def vec_from_mask(mask, n):
    return np.array([(int(mask)>>i)&1 for i in range(n)], dtype=np.uint8)

def mask_from_vec(v):
    out = 0
    for i, b in enumerate(v):
        if int(b) & 1:
            out |= 1 << i
    return out

def reconstruct_from_masks(terms, dims):
    T = np.zeros(dims, dtype=np.uint8)
    for u, v, w in terms:
        U = vec_from_mask(u, dims[0]).reshape(-1,1,1)
        V = vec_from_mask(v, dims[1]).reshape(1,-1,1)
        W = vec_from_mask(w, dims[2]).reshape(1,1,-1)
        T ^= (U * V * W).astype(np.uint8)
    return T

def load_pool_row(pool_path, row_idx):
    """Load one row from the flip-cpd pool (flat mask triples)."""
    pool = np.load(pool_path)
    row = pool[row_idx]
    rank = len(row) // 3
    terms = []
    for t in range(rank):
        u, v, w = int(row[3*t]), int(row[3*t+1]), int(row[3*t+2])
        terms.append((u, v, w))
    return terms, rank

def analyze_core_block_structure(core):
    """Analyze which 3x3 blocks of each 9x9 core slice are nonzero."""
    results = []
    for s in range(8):
        S = core[s]  # 9x9
        blocks = {}
        for br in range(3):
            for bc in range(3):
                block = S[3*br:3*br+3, 3*bc:3*bc+3]
                if block.any():
                    blocks[(br,bc)] = block.tolist()
        results.append({
            'slice': s,
            'a_index': s+1,  # original A index
            'nnz': int(S.sum()),
            'nonzero_blocks': {f"({k[0]},{k[1]})": v for k,v in blocks.items()},
            'block_count': len(blocks)
        })
    return results

def analyze_inner_product_condition():
    """Over F_2: for 3-dim vectors b,c, check rank(I_3 + bc^T)."""
    results = {'rank_2_count': 0, 'rank_3_count': 0, 'rank_2_pairs': [], 'rank_3_pairs': []}
    for bm in range(8):  # 0..7 (3-bit vectors)
        for cm in range(8):
            b = vec_from_mask(bm, 3)
            c = vec_from_mask(cm, 3)
            M = np.eye(3, dtype=np.uint8) ^ np.outer(b, c).astype(np.uint8)
            # Rank over F_2: Gaussian elimination
            r = gf2_rank(M)
            dot = int(np.dot(b, c)) % 2
            if r == 2:
                results['rank_2_count'] += 1
                results['rank_2_pairs'].append({'b': bm, 'c': cm, 'dot': dot})
            else:
                results['rank_3_count'] += 1
                results['rank_3_pairs'].append({'b': bm, 'c': cm, 'dot': dot, 'rank': r})
    return results

def gf2_rank(M):
    """Compute rank of matrix over F_2."""
    A = M.copy().astype(np.uint8) % 2
    rows, cols = A.shape
    rank = 0
    for col in range(cols):
        pivot = None
        for row in range(rank, rows):
            if A[row, col] & 1:
                pivot = row
                break
        if pivot is None:
            continue
        A[[rank, pivot]] = A[[pivot, rank]]
        for row in range(rows):
            if row != rank and (A[row, col] & 1):
                A[row] ^= A[rank]
        rank += 1
    return rank

def main():
    print("=" * 60)
    print("E11 BRIDGE VERIFICATION - research research_record")
    print("=" * 60)
    
    # analysis: Build tensors
    core, T = build_e11_core_direct()
    print(f"\nT_{333} shape: {T.shape}, nnz: {int(T.sum())}")
    print(f"E11 core shape: {core.shape}, nnz: {int(core.sum())}")
    
    # analysis: Verify reconstruction identity
    recon_ok, recon_diff = verify_reconstruction(core, T)
    print(f"\nReconstruction T = embed(core) + mask⊗T[0]: {'PASS' if recon_ok else 'FAIL'} (diff={recon_diff})")
    
    # analysis: Check removed slice
    slice_ok, slice_nnz, removed_terms = check_removed_slice(T)
    print(f"Removed slice T[0] = I_3 in block (0,0): {'PASS' if slice_ok else 'FAIL'} (nnz={slice_nnz})")
    print(f"Removed slice terms: {removed_terms}")
    
    # analysis: Analyze core block structure
    blocks = analyze_core_block_structure(core)
    print(f"\n--- Core Block Structure ---")
    for b in blocks:
        print(f"  Slice {b['slice']} (A={b['a_index']}): nnz={b['nnz']}, blocks={list(b['nonzero_blocks'].keys())}")
    
    # analysis: Inner product condition over F_2
    ipc = analyze_inner_product_condition()
    print(f"\n--- Inner Product Condition rank(I_3 + bc^T) over F_2 ---")
    print(f"  rank=2 pairs (b·c=1): {ipc['rank_2_count']}")
    print(f"  rank≠2 pairs: {ipc['rank_3_count']}")
    # Verify the claim: rank=2 iff b·c=1
    all_rank2_dot1 = all(p['dot'] == 1 for p in ipc['rank_2_pairs'])
    all_rank3_dot0 = all(p['dot'] == 0 for p in ipc['rank_3_pairs'])
    print(f"  rank=2 iff b·c=1: {all_rank2_dot1 and all_rank3_dot0}")
    
    # analysis: Load rank-21 control and verify lift
    pool_path = str(Path(__file__).resolve().parents[3] / "data" / "e11_flip_workspace" / "data" / "schemes_modp" / "e11core" / "mod2-rank21a.npy")
    # Fallback: try research root
    if not Path(pool_path).exists():
        pool_path = str(Path(__file__).resolve().parents[4] / "research_record" / "workspace" / "data" / "e11_flip_workspace" / "data" / "schemes_modp" / "e11core" / "mod2-rank21a.npy")
    if not Path(pool_path).exists():
        # Direct root-relative
        import os
        for candidate in [
            "data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy",
        ]:
            if os.path.exists(candidate):
                pool_path = candidate
                break
    core_terms, core_rank = load_pool_row(pool_path, 0)
    print(f"\n--- Rank-21 Positive Control ---")
    print(f"Core rank: {core_rank}")
    
    core_recon = reconstruct_from_masks(core_terms, (8,9,9))
    core_match = bool(np.array_equal(core_recon, core))
    core_diff = int(np.sum(core_recon ^ core))
    print(f"Core CPD verifies: {'PASS' if core_match else 'FAIL'} (diff={core_diff})")
    
    # Lift: shift A masks left by 1 bit (embed in bits 1..8), add 3 removed terms
    full_terms = [(u << 1, v, w) for u, v, w in core_terms]
    full_terms += removed_terms
    full_rank = len(full_terms)
    full_recon = reconstruct_from_masks(full_terms, (9,9,9))
    full_match = bool(np.array_equal(full_recon, T))
    full_diff = int(np.sum(full_recon ^ T))
    print(f"Full T_{333} rank after lift: {full_rank}")
    print(f"Full CPD verifies: {'PASS' if full_match else 'FAIL'} (diff={full_diff})")
    
    # analysis: Also check what rank-19 would give
    print(f"\n--- Rank Bridge Summary ---")
    print(f"Core rank 19 => full rank 22 (the target!)")
    print(f"Core rank 20 => full rank 23 (known)")
    print(f"Core rank 21 => full rank 24 (verified above)")
    
    # Save results
    result = {
        "research": "research_record",
        "tensor": "T_{3,3,3} over F_2",
        "e11_core": {
            "shape": list(core.shape),
            "nnz": int(core.sum()),
            "convention": "core[i] = T[i+1] for i=0..7; E11 deletes the a00 slice and has no free-bit XOR",
            "mask": 1,
            "pivot": 0,
            "pivot_label": "a00"
        },
        "reconstruction_verified": recon_ok,
        "removed_slice": {
            "matches_I3_block00": slice_ok,
            "nnz": slice_nnz,
            "rank_one_terms": [list(t) for t in removed_terms],
            "rank": 3
        },
        "block_structure": blocks,
        "inner_product_condition": {
            "rank2_iff_dot1": all_rank2_dot1 and all_rank3_dot0,
            "rank_2_count": ipc['rank_2_count'],
            "rank_3_count": ipc['rank_3_count']
        },
        "positive_control": {
            "pool": pool_path,
            "pool_row": 0,
            "core_rank": core_rank,
            "core_verified": core_match,
            "core_diff": core_diff,
            "full_rank": full_rank,
            "full_verified": full_match,
            "full_diff": full_diff
        },
        "bridge_formula": {
            "statement": "A rank-r E11 core CPD lifts to a rank-(r+3) full T_{333} CPD over F_2",
            "lift": "shift A masks left 1 bit (embed in bits 1..8) + add [(1,1,1),(1,2,2),(1,4,4)]",
            "target": "rank-19 core => rank-22 full (the research target)"
        },
        "all_checks_pass": recon_ok and slice_ok and core_match and full_match and (all_rank2_dot1 and all_rank3_dot0)
    }
    
    with open(OUTDIR / "bridge_verification.json", "w") as f:
        json.dump(result, f, indent=2)
    print(f"\nSaved: {OUTDIR / 'bridge_verification.json'}")
    print(f"\nALL CHECKS PASS: {result['all_checks_pass']}")
    
    # Save the core tensor as .npy for later use
    np.save(OUTDIR / "e11_core_8x9x9.npy", core)
    np.save(OUTDIR / "t333_9x9x9.npy", T)
    print(f"Saved core and T tensors to {OUTDIR}")
    
    if not result['all_checks_pass']:
        sys.exit(1)

if __name__ == "__main__":
    main()
