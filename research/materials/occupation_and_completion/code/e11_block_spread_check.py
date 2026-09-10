#!/usr/bin/env python3
"""Block-spread structure verification for E11 core decompositions over F₂.

CORRECTED convention (matching the bridge T[3i+j, 3j+k, 3i+k]):
  Row groups (B-side): R_j = {3j, 3j+1, 3j+2}
  Col groups (C-side): C_i = {3i, 3i+1, 3i+2}
  Both use the SAME contiguous partition: masks [7, 56, 448].

  Core slice s → a = s+1 = 3i+j → block R_j × C_i
    where j = (s+1)%3 (row group), i = (s+1)//3 (col group)

Purity lemma: if capacity_s = 3, the 3 terms have v ∈ R_{j(s)}, w ∈ C_{i(s)}.
R1: each slice needs ≥ 3 block-hitting terms.
R2: no singleton off-block hits per slice.
Cap3 separation: no term in two distinct capacity-3 slices.
GL₃: capacity-3 terms form an invertible 3×3 matrix over F₂.
"""

import numpy as np
import json, sys, time
from pathlib import Path

# Both groups use the same contiguous partition
GROUP = [0b000000111, 0b000111000, 0b111000000]  # {0,1,2}, {3,4,5}, {6,7,8}
GROUP_COMP = [0x1FF ^ g for g in GROUP]  # complement within 9 bits

def slice_block(s):
    """Slice s → (j, i) where j=row-group index, i=col-group index."""
    a = s + 1
    return a % 3, a // 3  # (j, i)

def det3_f2(rows):
    """3×3 determinant over F₂."""
    a, b, c = rows[0]; d, e, f = rows[1]; g, h, ii = rows[2]
    return (a*(e*ii ^ f*h) ^ b*(d*ii ^ f*g) ^ c*(d*h ^ e*g)) & 1

def extract_group(val, g):
    """Extract 3 bits of val at group g = {3g, 3g+1, 3g+2}."""
    return [(val >> (3*g + k)) & 1 for k in range(3)]

def build_core():
    """Build E11 8×9×9 core using bridge convention."""
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T[1:9].copy()

def check_row(row, R, core_for_brent=None):
    """Check block-spread properties for one pool row."""
    # Parse terms
    u_arr = [int(row[3*t])   for t in range(R)]
    v_arr = [int(row[3*t+1]) for t in range(R)]
    w_arr = [int(row[3*t+2]) for t in range(R)]
    
    # Optional Brent check
    brent_ok = None
    if core_for_brent is not None:
        recon = np.zeros((8,9,9), dtype=np.uint8)
        for t in range(R):
            u, v, w = u_arr[t], v_arr[t], w_arr[t]
            for s in range(8):
                if (u >> s) & 1:
                    for b in range(9):
                        if (v >> b) & 1:
                            for c in range(9):
                                if (w >> c) & 1:
                                    recon[s,b,c] ^= 1
        brent_ok = bool(np.array_equal(recon, core_for_brent))
    
    # Precompute per-term group memberships
    brow = [[False]*3 for _ in range(R)]  # brow[t][j] = v_t meets R_j
    bcol = [[False]*3 for _ in range(R)]  # bcol[t][i] = w_t meets C_i
    for t in range(R):
        for g in range(3):
            brow[t][g] = (v_arr[t] & GROUP[g]) != 0
            bcol[t][g] = (w_arr[t] & GROUP[g]) != 0
    
    caps = [0]*8
    purity_fail = 0; r1_fail = 0; r2_fail = 0; gl3_fail = 0
    cap3_slices = []
    
    for s in range(8):
        j_s, i_s = slice_block(s)  # row group j, col group i
        active = [t for t in range(R) if (u_arr[t] >> s) & 1]
        caps[s] = len(active)
        
        # R1: ≥ 3 block-hitting terms
        n_hit = sum(1 for t in active if brow[t][j_s] and bcol[t][i_s])
        if n_hit < 3:
            r1_fail += 1
        
        # R2: no singleton off-block hits
        for j in range(3):
            for i in range(3):
                if j == j_s and i == i_s:
                    continue
                n_off = sum(1 for t in active if brow[t][j] and bcol[t][i])
                if n_off == 1:
                    r2_fail += 1
        
        # Purity + GL₃ for capacity-3
        if caps[s] == 3:
            cap3_slices.append(s)
            all_pure = True
            for t in active:
                if (v_arr[t] & GROUP_COMP[j_s]) != 0 or (w_arr[t] & GROUP_COMP[i_s]) != 0:
                    purity_fail += 1
                    all_pure = False
            if all_pure:
                V = [extract_group(v_arr[t], j_s) for t in active]
                if det3_f2(V) != 1:
                    gl3_fail += 1
    
    # Cap3 separation
    cap3_shared = 0
    for t in range(R):
        c3_count = sum(1 for s in cap3_slices if (u_arr[t] >> s) & 1)
        if c3_count >= 2:
            cap3_shared += 1
    
    p = len(cap3_slices)
    total_w = sum(caps)
    
    # Block-spread: |B(t)| per term
    bt_sizes = [sum(1 for j in range(3) for i in range(3) 
                    if brow[t][j] and bcol[t][i]) for t in range(R)]
    
    return {
        "caps": caps, "p": p, "total_weight": total_w,
        "purity_fail": purity_fail, "r1_fail": r1_fail,
        "r2_fail": r2_fail, "cap3_shared": cap3_shared, "gl3_fail": gl3_fail,
        "bt_sizes": bt_sizes, "brent_ok": brent_ok,
        "all_ok": (purity_fail + r1_fail + r2_fail + cap3_shared + gl3_fail) == 0,
    }

def main():
    t0 = time.time()
    core = build_core()
    assert core.sum() == 24
    
    # Verify block structure
    for s in range(8):
        j_s, i_s = slice_block(s)
        for k in range(3):
            assert core[s, 3*j_s+k, 3*i_s+k] == 1
        for b in range(9):
            for c in range(9):
                if b//3 == j_s and c//3 == i_s:
                    continue
                assert core[s, b, c] == 0
    print("Core block structure verified (contiguous groups, both R and C).")
    
    pool_path = Path("data/"
                     "e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy")
    pool = np.load(pool_path)
    N = pool.shape[0]
    R = pool.shape[1] // 3
    print(f"Pool: {N} rows, rank {R}, raw shape {pool.shape}")
    
    # Spot-check Brent on first rows
    brent_spot = min(10, N)
    brent_ok_count = 0
    for idx in range(brent_spot):
        res = check_row(pool[idx], R, core_for_brent=core)
        if res["brent_ok"]:
            brent_ok_count += 1
    print(f"Brent spot-check: {brent_ok_count}/{brent_spot}")
    
    # Full block-spread check (no Brent reconstruction for speed)
    all_pass = True; fails = []
    p_hist = {}; w_hist = {}; cap_hist = {}; bt_hist = {}
    min_w = 999; max_p = 0
    
    for idx in range(N):
        res = check_row(pool[idx], R)
        if not res["all_ok"]:
            all_pass = False
            if len(fails) < 5:
                fails.append({"row": idx, **{k: res[k] for k in 
                    ["caps","p","total_weight","purity_fail","r1_fail",
                     "r2_fail","cap3_shared","gl3_fail"]}})
        
        p = res["p"]; tw = res["total_weight"]
        p_hist[p] = p_hist.get(p, 0) + 1
        w_hist[tw] = w_hist.get(tw, 0) + 1
        ck = str(sorted(res["caps"]))
        cap_hist[ck] = cap_hist.get(ck, 0) + 1
        min_w = min(min_w, tw); max_p = max(max_p, p)
        for sz in res["bt_sizes"]:
            bt_hist[sz] = bt_hist.get(sz, 0) + 1
    
    elapsed = time.time() - t0
    summary = {
        "pool_rows": N, "rank": R,
        "brent_spot_check": f"{brent_ok_count}/{brent_spot}",
        "all_block_spread_pass": all_pass,
        "fail_count": len(fails),
        "fail_examples": fails,
        "p_capacity3_histogram": dict(sorted(p_hist.items())),
        "total_weight_histogram": dict(sorted(w_hist.items())),
        "min_total_weight": min_w, "max_p_capacity3": max_p,
        "capacity_profiles_top15": dict(
            sorted(cap_hist.items(), key=lambda x: -x[1])[:15]),
        "term_block_spread_histogram": dict(sorted(bt_hist.items())),
        "theoretical_rank19_bounds": {"p_max": 5, "weight_min": 27},
        "block_convention": {
            "row_groups_R_j": "R_j = {3j, 3j+1, 3j+2}",
            "col_groups_C_i": "C_i = {3i, 3i+1, 3i+2}",
            "masks": "[7, 56, 448] for both R and C",
            "slice_s_block": "(j=(s+1)%3, i=(s+1)//3)",
            "tensor_convention": "T[3i+j, 3j+k, 3i+k] = 1",
        },
        "elapsed_sec": round(elapsed, 2),
    }
    
    outdir = Path("data/block_spread")
    outdir.mkdir(parents=True, exist_ok=True)
    out = outdir / "pool_block_spread_check.json"
    out.write_text(json.dumps(summary, indent=2, default=str) + "\n")
    print(json.dumps(summary, indent=2, default=str))
    
    if all_pass:
        print(f"\n✓ All {N} rows pass all block-spread checks in {elapsed:.1f}s.")
    else:
        print(f"\n✗ {len(fails)} rows failed!")
        for f in fails[:3]:
            print(f"  Row {f['row']}: p={f['p']}, w={f['total_weight']}, "
                  f"purity={f['purity_fail']}, R1={f['r1_fail']}, "
                  f"R2={f['r2_fail']}, cap3_shared={f['cap3_shared']}")
        sys.exit(1)

if __name__ == "__main__":
    main()
