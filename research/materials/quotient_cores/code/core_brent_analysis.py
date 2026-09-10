#!/usr/bin/env python3
"""Analyze the E11 core Brent equation structure for SAT encoding.

The core Brent equations are: for each (s, b, c) with s=0..7, b=0..8, c=0..8:
  sum_{t=1}^{19} u_t[s] * v_t[b] * w_t[c] = core[s,b,c]  (mod 2)

This script:
1. Counts the nonzero and zero target equations
2. Analyzes the block structure to identify redundancies
3. Estimates the SAT encoding size
4. Identifies useful symmetry-breaking constraints
"""
import numpy as np
from pathlib import Path
import json

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUTDIR = WS / "data" / "core_sat_analysis"
OUTDIR.mkdir(parents=True, exist_ok=True)

def build_t333():
    T = np.zeros((9,9,9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T

def build_e11_core():
    T = build_t333()
    return T[1:9].copy()  # (8, 9, 9)

def main():
    core = build_e11_core()
    print(f"Core shape: {core.shape}, nnz: {int(core.sum())}")
    
    # Count equation types
    n_one = 0
    n_zero = 0
    one_entries = []
    for s in range(8):
        for b in range(9):
            for c in range(9):
                if core[s,b,c]:
                    n_one += 1
                    one_entries.append((s, b, c))
                else:
                    n_zero += 1
    
    print(f"\nBrent equations: {n_one + n_zero} total")
    print(f"  Target = 1: {n_one} (must be covered)")
    print(f"  Target = 0: {n_zero} (must cancel)")
    
    # Block structure: each slice has I_3 in one 3x3 block
    print(f"\n--- Block assignments ---")
    block_map = {}
    for s in range(8):
        for br in range(3):
            for bc in range(3):
                block = core[s, 3*br:3*br+3, 3*bc:3*bc+3]
                if block.any():
                    is_I3 = np.array_equal(block, np.eye(3, dtype=np.uint8))
                    block_map[s] = (br, bc, is_I3)
                    print(f"  Slice {s}: block ({br},{bc}), I_3: {is_I3}")
    
    # For SAT encoding: each trilinear equation u[s]*v[b]*w[c] = target
    # is linearized as: product p_{t,s,b,c} = u_t[s] AND v_t[b] AND w_t[c]
    # then: XOR_{t=1}^{19} p_{t,s,b,c} = target
    
    # But the triple AND needs intermediate variables:
    # Let x_{t,s} = u_t[s] AND v_t[b] ... wait, we need per-(s,b,c) products
    # Actually: for each term t, we can define:
    #   uv_{t,s,b} = u_t[s] AND v_t[b]
    #   p_{t,s,b,c} = uv_{t,s,b} AND w_t[c]
    # Then: XOR_t p_{t,s,b,c} = core[s,b,c]
    
    # Number of auxiliary variables:
    # uv: 19 * 8 * 9 = 1368
    # p: 19 * 8 * 9 * 9 = 12312 (but many will be constrained to 0 by structure)
    # Actually we don't need p explicitly if we use XOR-clause encoding
    
    # Better approach: for each equation (s,b,c):
    # Define contribution_t = u_t[s] * v_t[b] * w_t[c]
    # This is a 3-way AND. Standard Tseytin:
    # Let a_{t,s,b} = u_t[s] AND v_t[b] (introduce once, reuse across c)
    # Then contribution_{t,s,b,c} = a_{t,s,b} AND w_t[c]
    
    n_terms = 19
    n_aux_uv = n_terms * 8 * 9  # 1368 a_{t,s,b} variables
    n_base = n_terms * (8 + 9 + 9)  # 494 base variables
    
    print(f"\n--- SAT Encoding Size Estimates ---")
    print(f"Base variables: {n_base} (19 terms × 26 bits)")
    print(f"UV auxiliary: {n_aux_uv} (for u*v products)")
    print(f"Total variables (approx): {n_base + n_aux_uv}")
    
    # Clause count estimate:
    # Each a_{t,s,b} = u AND v needs 3 clauses (Tseytin)
    n_tseytin_uv = n_aux_uv * 3
    
    # Each equation (s,b,c) with target t:
    # XOR_{t=1}^{19} (a_{t,s,b} AND w_t[c]) = target
    # This is a conditional XOR - each addend is a 2-way AND
    # Standard encoding: introduce contribution variables, then XOR
    # Or use cardinality/parity constraints
    
    # For the parity constraint: need 19 contribution variables per equation
    # Total contribution vars: 648 * 19 = 12312
    # But we can reuse a_{t,s,b} across c-values
    
    # Actually, more efficient: for each (s,b), we have a_{t,s,b} fixed.
    # Then for each c: XOR_t (a_{t,s,b} AND w_t[c]) = core[s,b,c]
    # This is 9 parity constraints sharing the same a values.
    
    # A better encoding: for each (s,b) pair:
    # We have the 19-bit vector a_{*,s,b} and 9 targets core[s,b,0..8].
    # The equation system is: for each c, XOR_t (a_{t,s,b} AND w_t[c]) = core[s,b,c]
    # This is a bilinear system in (a, w) for fixed s,b.
    
    # Let's count unique (s,b) pairs where there's at least one nonzero target:
    active_sb = set()
    for s in range(8):
        for b in range(9):
            if core[s,b,:].any():
                active_sb.add((s,b))
    
    print(f"\nActive (s,b) pairs with nonzero targets: {len(active_sb)}")
    
    # Each active (s,b) has 1-3 nonzero c-values (from I_3 structure)
    for s,b in sorted(active_sb):
        nz_c = [c for c in range(9) if core[s,b,c]]
        print(f"  ({s},{b}): nonzero c = {nz_c}")
    
    # Symmetry analysis
    print(f"\n--- Symmetry Breaking ---")
    print("Item symmetry: 19! permutations of terms")
    print("Can fix first term's A-factor to lexicographic minimum")
    
    # Useful structural constraints
    print(f"\n--- Structural Constraints ---")
    
    # Per-slice capacity: each slice needs at least 3 terms (to produce I_3)
    print("Per-slice capacity: |T_s| >= 3 for each s=0..7")
    print("Total A-weight: sum popcount(u_t) >= 24")
    
    # Block-zero constraints: each term's v⊗w matrix must cancel in all
    # non-assigned blocks across all slices it participates in.
    # This is captured by the Brent equations themselves.
    
    # The core has 24 nonzero entries and 624 zero entries.
    # The zero entries provide "cancellation" constraints.
    # Key: most of the work is in ensuring the 624 zero equations hold.
    
    # Estimate: how many of the 624 zero equations are trivially satisfied
    # (because no term can contribute to that entry)?
    # An entry (s,b,c) with core[s,b,c]=0 can still receive contributions
    # from terms where u_t[s]=1, v_t[b]=1, w_t[c]=1.
    # Since u_t, v_t, w_t are free variables, any entry can receive contributions.
    # So all 624 zero equations are nontrivial constraints.
    
    # However, the block structure helps. For a term in slice s (u_t[s]=1),
    # its 9×9 v⊗w contributes I_3 to block (j_s, i_s) and must be zero
    # in all other blocks. But the term also participates in other slices,
    # where its v⊗w contributes to potentially different blocks.
    
    # Cross-contamination count: for each term, the number of off-block
    # entries it can pollute depends on which blocks v and w span.
    
    # Save analysis
    result = {
        "core_shape": list(core.shape),
        "core_nnz": int(core.sum()),
        "n_equations": n_one + n_zero,
        "n_target_1": n_one,
        "n_target_0": n_zero,
        "n_terms": n_terms,
        "n_base_vars": n_base,
        "n_aux_uv": n_aux_uv,
        "n_active_sb_pairs": len(active_sb),
        "block_assignments": {str(k): v for k, v in block_map.items()},
        "one_entries": one_entries,
    }
    
    with open(OUTDIR / "core_brent_analysis.json", "w") as f:
        json.dump(result, f, indent=2)
    print(f"\nSaved: {OUTDIR / 'core_brent_analysis.json'}")

if __name__ == "__main__":
    main()
