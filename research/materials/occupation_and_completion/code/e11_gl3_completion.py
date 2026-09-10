#!/usr/bin/env python3
"""GL₃(F₂) completion module for E11 core capacity-3 slices.

For a slice with exactly 3 active terms, the 3 rank-1 matrices sum to I₃ on 
the own block, so V_block × W_block^T = I₃ with V,W ∈ GL₃(F₂). This module
precomputes GL₃(F₂) and provides completion utilities.

Also provides a fixed-support completion checker: given an A-support (19 u-masks),
determine the capacity profile, enumerate GL₃ choices for cap-3 slices, and
assess the remaining bilinear system.
"""
import numpy as np
import json, time
from pathlib import Path
from itertools import product as iproduct

# ── Block structure ──────────────────────────────────────────────────────
GROUP = [7, 56, 448]  # contiguous: {0,1,2}, {3,4,5}, {6,7,8}

def slice_block(s):
    a = s + 1
    return a % 3, a // 3  # (j=row_group, i=col_group)

def det3_f2(M):
    """3×3 determinant over F₂ (0 or 1)."""
    a,b,c = M[0]; d,e,f = M[1]; g,h,ii = M[2]
    return (a*(e*ii ^ f*h) ^ b*(d*ii ^ f*g) ^ c*(d*h ^ e*g)) & 1

def inv3_f2(M):
    """3×3 inverse over F₂ using adjugate."""
    a,b,c = [int(x) for x in M[0]]
    d,e,f = [int(x) for x in M[1]]
    g,h,i = [int(x) for x in M[2]]
    adj = np.array([
        [e*i ^ f*h, c*h ^ b*i, b*f ^ c*e],
        [f*g ^ d*i, a*i ^ c*g, c*d ^ a*f],
        [d*h ^ e*g, b*g ^ a*h, a*e ^ b*d],
    ], dtype=np.uint8) & 1
    # det = 1 (must be invertible)
    return adj

def matmul3_f2(A, B):
    """3×3 matrix multiply over F₂."""
    C = np.zeros((3,3), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            s = 0
            for k in range(3):
                s ^= int(A[i,k]) & int(B[k,j])
            C[i,j] = s
    return C

# ── GL₃(F₂) enumeration ────────────────────────────────────────────────
def enumerate_gl3_f2():
    """Generate all 168 elements of GL₃(F₂) as 3×3 numpy arrays."""
    gl3 = []
    for bits in range(512):  # 2^9 = 512 possible 3×3 binary matrices
        M = np.array([[(bits >> (3*r+c)) & 1 for c in range(3)] for r in range(3)], dtype=np.uint8)
        if det3_f2(M) == 1:
            gl3.append(M)
    assert len(gl3) == 168, f"Expected 168, got {len(gl3)}"
    return gl3

# ── Completion utilities ────────────────────────────────────────────────
def cap3_completions(j_group, i_group, gl3_list):
    """For a cap-3 slice on block R_j × C_i, generate all (V_full, W_full) pairs.
    
    Each element of GL₃(F₂) gives one decomposition:
      V_block = X (columns are the 3 v-restrictions to R_j)
      W_block = X^{-T} (columns are the 3 w-restrictions to C_i)
    
    Returns list of (v_masks, w_masks) where each is a tuple of 3 integer masks.
    """
    results = []
    for X in gl3_list:
        Xinv = inv3_f2(X)
        # V_block columns = columns of X → v_t restricted to R_j
        # W_block = X^{-T} = (X^{-1})^T → columns of Xinv^T = rows of Xinv
        W_block = Xinv.T  # each column is a w-restriction
        
        # Verify: X × W_block^T = X × Xinv = I₃
        check = matmul3_f2(X, W_block.T)
        assert np.array_equal(check, np.eye(3, dtype=np.uint8))
        
        # Convert to 9-bit masks
        v_masks = []
        w_masks = []
        for col in range(3):
            # v_t: X[:, col] placed in R_j positions
            v_bits = 0
            for k in range(3):
                if X[k, col]:
                    v_bits |= 1 << (3*j_group + k)
            v_masks.append(v_bits)
            
            # w_t: W_block[:, col] placed in C_i positions
            w_bits = 0
            for k in range(3):
                if W_block[k, col]:
                    w_bits |= 1 << (3*i_group + k)
            w_masks.append(w_bits)
        
        results.append((tuple(v_masks), tuple(w_masks)))
    return results

def analyze_support(u_masks, rank=19):
    """Analyze a 19-point A-support for block-spread properties.
    
    Returns capacity profile, which slices are cap-3, total weight, etc.
    """
    caps = [0] * 8
    active = [[] for _ in range(8)]  # active[s] = list of term indices
    for t in range(rank):
        for s in range(8):
            if (u_masks[t] >> s) & 1:
                caps[s] += 1
                active[s].append(t)
    
    p = sum(1 for c in caps if c == 3)
    total_w = sum(caps)
    cap3_slices = [s for s in range(8) if caps[s] == 3]
    
    return {
        "caps": caps,
        "p": p,
        "total_weight": total_w,
        "cap3_slices": cap3_slices,
        "active": active,
        "feasible": all(c >= 3 for c in caps) and p <= 5 and total_w >= 27,
    }

def build_core():
    """Build E11 8×9×9 core."""
    T = np.zeros((9,9,9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T[1:9].copy()

def attempt_completion(u_masks, core=None, gl3=None, verbose=False):
    """Attempt to complete a rank-19 E11 core decomposition for a given A-support.
    
    Strategy:
    1. Analyze capacity profile
    2. For cap-3 slices: enumerate GL₃ completions
    3. For each GL₃ combination: check off-block conditions
    4. Solve remaining bilinear system
    
    Returns dict with results and any found decomposition.
    """
    if core is None:
        core = build_core()
    if gl3 is None:
        gl3 = enumerate_gl3_f2()
    
    rank = len(u_masks)
    info = analyze_support(u_masks, rank)
    
    if not info["feasible"]:
        return {"status": "infeasible", "reason": "capacity/weight check failed", **info}
    
    cap3_slices = info["cap3_slices"]
    p = info["p"]
    
    if p == 0:
        return {"status": "no_cap3", "reason": "all slices have capacity ≥ 4", **info}
    
    # For cap-3 slices, enumerate GL₃ completions
    cap3_options = []
    for s in cap3_slices:
        j_s, i_s = slice_block(s)
        completions = cap3_completions(j_s, i_s, gl3)
        cap3_options.append((s, info["active"][s], completions))
    
    # Try all combinations of GL₃ choices for cap-3 slices
    # For p=1: 168 combinations. p=2: 28K. p=3: 4.7M. p=4: 800M. p=5: too many.
    if p > 3:
        return {"status": "too_many_cap3", "p": p, 
                "combinations": 168**p, **info}
    
    total_tried = 0
    for combo in iproduct(*(range(168) for _ in range(p))):
        total_tried += 1
        
        # Assign v,w for cap-3 terms
        v_assign = {}  # term -> v_mask
        w_assign = {}  # term -> w_mask
        
        valid = True
        for idx, (s, active_terms, completions) in enumerate(cap3_options):
            choice = combo[idx]
            v_ms, w_ms = completions[choice]
            for local_t, global_t in enumerate(active_terms):
                if global_t in v_assign:
                    # This term is in two cap-3 slices (should be impossible by purity)
                    valid = False
                    break
                v_assign[global_t] = v_ms[local_t]
                w_assign[global_t] = w_ms[local_t]
            if not valid:
                break
        
        if not valid:
            continue
        
        # Check off-block cancellation for committed terms in other slices
        # For each non-cap3 slice s', the committed terms contribute off-block
        # Their contribution must cancel with other terms
        offblock_ok = True
        for s in range(8):
            if s in cap3_slices:
                continue
            # Check: for each block β in this slice, the committed terms
            # contribute at most on their own original block, not on β
            # (since they're block-pure). So committed terms contribute 0
            # to the own block of slice s. Only free terms contribute.
            # This is automatically handled by the Brent equations.
            # But we should check: committed terms active in s contribute
            # OFF-block. For R2: no singleton off-block hits.
            
            active_s = info["active"][s]
            j_s, i_s = slice_block(s)
            
            for j in range(3):
                for i in range(3):
                    if j == j_s and i == i_s:
                        continue
                    # Count terms in active_s that hit block (j,i)
                    hit_count = 0
                    for t in active_s:
                        v = v_assign.get(t)
                        w = w_assign.get(t)
                        if v is not None and w is not None:
                            if (v & GROUP[j]) and (w & GROUP[i]):
                                hit_count += 1
                        # Free terms: unknown v,w, can't check yet
                    # If only committed terms are counted and hit_count == 1,
                    # we need a free term to also hit. Not definitive yet.
        
        if total_tried % 10000 == 0 and verbose:
            print(f"  Tried {total_tried} GL₃ combinations...")
    
    return {
        "status": "enumerated",
        "total_tried": total_tried,
        "note": "Full bilinear solve not yet implemented for free terms",
        **info,
    }


def main():
    t0 = time.time()
    
    # Precompute GL₃(F₂)
    gl3 = enumerate_gl3_f2()
    print(f"GL₃(F₂) has {len(gl3)} elements")
    
    # Verify a few properties
    I = np.eye(3, dtype=np.uint8)
    identity_found = any(np.array_equal(M, I) for M in gl3)
    print(f"Identity in GL₃: {identity_found}")
    
    # Check closure under multiplication
    products_in = 0
    total_checked = 0
    for i in range(min(50, len(gl3))):
        for j in range(min(50, len(gl3))):
            P = matmul3_f2(gl3[i], gl3[j])
            if any(np.array_equal(P, M) for M in gl3):
                products_in += 1
            total_checked += 1
    print(f"Closure check: {products_in}/{total_checked} products in GL₃")
    
    # Generate completions for block (1, 0) = R_1 × C_0 (slice 0)
    comps = cap3_completions(1, 0, gl3)
    print(f"\nCap-3 completions for slice 0 (R₁×C₀): {len(comps)}")
    
    # Verify first completion: V × W^T should be I₃ on the block
    core = build_core()
    v_ms, w_ms = comps[0]
    recon = np.zeros((9, 9), dtype=np.uint8)
    for t in range(3):
        v = v_ms[t]; w = w_ms[t]
        for b in range(9):
            if (v >> b) & 1:
                for c in range(9):
                    if (w >> c) & 1:
                        recon[b, c] ^= 1
    # Should match core[0] (slice 0)
    match = np.array_equal(recon, core[0])
    print(f"First completion reconstructs slice 0: {match}")
    
    # Count how many completions reconstruct slice 0 perfectly
    perfect = 0
    for v_ms, w_ms in comps:
        recon = np.zeros((9, 9), dtype=np.uint8)
        for t in range(3):
            v, w = v_ms[t], w_ms[t]
            for b in range(9):
                if (v >> b) & 1:
                    for c in range(9):
                        if (w >> c) & 1:
                            recon[b, c] ^= 1
        if np.array_equal(recon, core[0]):
            perfect += 1
    print(f"Completions that perfectly reconstruct slice 0: {perfect}/168")
    
    # Save GL₃ data
    outdir = Path("data/block_spread")
    outdir.mkdir(parents=True, exist_ok=True)
    
    gl3_data = {
        "size": len(gl3),
        "elements_as_flat": [M.flatten().tolist() for M in gl3],
        "identity_index": next(i for i, M in enumerate(gl3) if np.array_equal(M, I)),
    }
    (outdir / "gl3_f2.json").write_text(json.dumps(gl3_data, indent=2) + '\n')
    
    elapsed = time.time() - t0
    print(f"\nTotal time: {elapsed:.2f}s")
    print(f"Saved GL₃(F₂) data to {outdir / 'gl3_f2.json'}")

if __name__ == "__main__":
    main()
