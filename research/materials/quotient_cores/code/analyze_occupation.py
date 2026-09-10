#!/usr/bin/env python3
"""Analyze Wang certificate dimension-2 orbits containing E11
to derive occupation constraints on the E11 core's decomposition.

For each 2D orbit with E11 as one constraint:
- The second constraint gives a 1D restriction of the E11 core
- The certified LB gives an occupation constraint on the core's rank-r decomposition
- Specifically: at most (r - LB) terms can have A-factor in the kernel

We check whether the combined constraints are consistent with rank 19.
"""
import numpy as np
import json
from pathlib import Path

def build_matmul_tensor_f2():
    T = np.zeros((9,9,9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    return T

def apply_constraint_f2(T, mask):
    result = T.copy()
    pivot = mask.bit_length() - 1
    free_bits = mask ^ (1 << pivot)
    for i in range(T.shape[0]):
        if (free_bits >> i) & 1:
            result[i] = (result[i] + result[pivot]) % 2
    result[pivot] = 0
    indices = [j for j in range(T.shape[0]) if j != pivot]
    return result[indices]

def f2_rank(M):
    m = M.copy().astype(np.uint8) % 2
    rows, cols = m.shape
    rank = 0
    for col in range(cols):
        prow = None
        for row in range(rank, rows):
            if m[row, col] & 1:
                prow = row
                break
        if prow is None: continue
        if prow != rank:
            m[[rank, prow]] = m[[prow, rank]]
        for row in range(rows):
            if row != rank and (m[row, col] & 1):
                m[row] ^= m[rank]
        rank += 1
    return rank

def main():
    outdir = Path('data/restricted_cores')
    
    # Build E11 core
    T = build_matmul_tensor_f2()
    core_e11 = apply_constraint_f2(T, 1)
    na, nb, nc = core_e11.shape
    
    # Core A-coordinate map:
    # core[0]=related analysis, core[1]=related analysis, core[2]=a10, core[3]=a11,
    # core[4]=a12, core[5]=a20, core[6]=a21, core[7]=a22
    core_labels = ['related analysis', 'related analysis', 'a10', 'a11', 'a12', 'a20', 'a21', 'a22']
    full_to_core = {1:0, 2:1, 3:2, 4:3, 5:4, 6:5, 7:6, 8:7}
    
    # Dimension-2 orbits containing E11 (mask 1)
    # From cert_profile.json
    orbits_with_e11 = [
        {'mask2': 2,   'lb': 17, 'label': 'E12 (related analysis)'},
        {'mask2': 10,  'lb': 18, 'label': 'E12+E21 (related analysis+a10)'},
        {'mask2': 16,  'lb': 18, 'label': 'E22 (a11)'},
        {'mask2': 20,  'lb': 18, 'label': 'E13+E22 (related analysis+a11)'},
        {'mask2': 84,  'lb': 18, 'label': 'E13+E22+E31 (related analysis+a11+a20)'},
        {'mask2': 160, 'lb': 18, 'label': 'E23+E32 (a12+a21)'},
    ]
    
    print("="*70)
    print("WANG 2D ORBITS → E11 CORE OCCUPATION CONSTRAINTS")
    print("="*70)
    
    # For each orbit: compute the kernel vector in core space
    # The kernel of the 2D restriction projected to the core is:
    # the RREF mask2 vector with full-tensor bit 0 removed
    for orb in orbits_with_e11:
        mask2 = orb['mask2']
        pivot2 = mask2.bit_length() - 1
        free2 = mask2 ^ (1 << pivot2)
        
        # Kernel vector in full space: 1 at pivot and free bits
        kernel_full = [0]*9
        for bit in range(9):
            if (mask2 >> bit) & 1:
                kernel_full[bit] = 1
        
        # Project to core (remove bit 0)
        kernel_core = tuple(kernel_full[i] for i in range(9) if i != 0)
        
        # The linear functional on core that defines the restriction
        func_bits = []
        for idx in range(8):
            if kernel_core[idx]:
                func_bits.append(f'u[{idx}]={core_labels[idx]}')
        
        orb['kernel_core'] = kernel_core
        orb['func_description'] = ' + '.join(func_bits) + ' = 0'
        
        print(f"\n  Orbit [1, {mask2}] ({orb['label']}), LB={orb['lb']}")
        print(f"    Core kernel vector: {kernel_core}")
        print(f"    Core restriction: {orb['func_description']}")
        print(f"    For rank-19: at most {19 - orb['lb']} terms with u_core = {list(kernel_core)}")
    
    # Now check: for rank 19, what does the A-slice rank structure require?
    print(f"\n{'='*70}")
    print("A-SLICE RANK ANALYSIS FOR E11 CORE")
    print("="*70)
    
    for a in range(na):
        sl = core_e11[a]
        rk = f2_rank(sl)
        print(f"  core[{a}] ({core_labels[a]} slice): rank {rk}")
        print(f"    In a rank-r decomp: at least {rk} terms have u[{a}]=1")
    
    # Key insight: for rank 19, how many terms can have u[a]=0?
    # terms with u[a]=0 = r - (terms with u[a]=1) ≤ r - rank(core[a])
    # But this is a LOWER bound on terms with u[a]=1, not an upper bound.
    
    # The occupation constraints give: for specific kernel vectors m,
    # at most (r - LB) terms have u_core = m.
    
    # Can we derive a SLICE-LEVEL occupation argument?
    # For each a: core[a,:,:] = Σ_{t: u_t[a]=1} v_t ⊗ w_t
    # Number of such terms = |{t: u_t[a]=1}|
    # matrix rank of sum ≤ |{t: u_t[a]=1}|
    # So |{t: u_t[a]=1}| ≥ rank(core[a,:,:]) = 3
    
    # Also: |{t: u_t[a]=0}| = r - |{t: u_t[a]=1}|
    # The "complementary slice" is:
    # T_full[a_full,:,:] - core[a,:,:] if a maps to a full slice with nonzero complement
    # Actually, the core IS T with a00=0, so core[a,:,:] = T[a+1,:,:] for the E11 case
    # (no folding for mask 1)
    
    # For rank 19 with 8 slices each needing ≥ 3 terms:
    # Total (a,t) pairs where u_t[a]=1: ≥ 8×3 = 24
    # Average weight of u_t: ≥ 24/19 ≈ 1.26
    # So many terms have weight ≥ 2
    
    print(f"\n  Minimum total weight: 24, with 19 terms")
    print(f"  Average weight: {24/19:.3f}")
    
    # Let's check whether the orbit constraints create a counting obstruction.
    # The orbits under the stabilizer of E11 partition all 255 nonzero
    # core vectors into 6 classes. Let me compute the orbit sizes.
    
    print(f"\n{'='*70}")
    print("ORBIT ANALYSIS: FEASIBILITY OF RANK-19 DECOMPOSITION")
    print("="*70)
    
    # For each nonzero core vector, determine which orbit it belongs to
    # by computing the rank of the corresponding matrix in the A-space
    # The orbit type depends on the rank of the matrix element viewed
    # as a 3x3 F2 matrix (with a00=0 and the relevant entry structure)
    
    # Actually, the orbit classification is based on the symmetry group action,
    # not just matrix rank. Let me instead focus on the direct counting argument.
    
    # For rank 19, occupation constraints from 1D core restrictions:
    # Each RREF mask vector m_core (nonzero in F2^8) gives:
    #   multiplicity(m_core) ≤ 19 - LB(m_core)
    # where LB is from the corresponding 2D orbit of the full tensor
    
    # The 6 orbit types give:
    # Type 1 (LB=17): multiplicity ≤ 2 (orbit of kernel_core for [1,2])
    # Type 2-6 (LB=18): multiplicity ≤ 1 (5 orbit types)
    
    # The key question: what are the orbit SIZES?
    # If orbit type 1 has N1 elements and types 2-6 have N2,...,N6 elements:
    # Maximum total terms = 2*N1 + 1*(N2+N3+N4+N5+N6)
    # This must be ≥ 19 for rank-19 to be possible.
    
    # Let me compute: which nonzero core vectors belong to each orbit type
    
    # The orbit of a core vector under the stabilizer of E11 in GL(3,2)×GL(3,2)
    # is determined by the equivalence class of the corresponding 3×3 matrix
    # (with a00=0) under the stabilizer action.
    
    # But computing this exactly requires knowing the stabilizer group.
    # Instead, let me use a simpler approach: for each of the 255 nonzero
    # core vectors, apply each of the 6 restriction functionals and see
    # which orbit it would belong to.
    
    # Actually, the orbit of a core vector m determines the LB of the
    # 2D full-tensor orbit {E11, m}. So the LB(m) for each m tells us
    # its orbit type.
    
    # To compute LB(m) for all 255 core vectors, I'd need to check
    # which full-tensor 2D orbit each span{E11, m~} belongs to.
    # This requires the symmetry group action.
    
    # Simpler: the Wang certificate directly gives LBs for all
    # dimension-2 orbits. There are 14 orbits total. Of these, 6
    # contain E11 in their canonical form. But the other 8 might also
    # contain 2D subspaces with E11.
    
    # Let me just enumerate: for each nonzero core vector m,
    # compute the 2D restriction of the full tensor at {E11, m~}
    # and compute the flattening lower bound as a quick check.
    
    print("\n  Computing flattening lower bounds for all 255 core restrictions...")
    
    # For each nonzero m in F2^8, the core restriction is a 7×9×9 tensor
    # Its flattening rank gives a lower bound
    flb_counts = {}
    for m_int in range(1, 256):
        m_core = tuple((m_int >> i) & 1 for i in range(8))
        # Apply this restriction to the core
        mask_core = m_int  # this IS the mask in core space
        pivot_core = mask_core.bit_length() - 1
        free_core = mask_core ^ (1 << pivot_core)
        
        restricted = core_e11.copy()
        for i in range(8):
            if (free_core >> i) & 1:
                restricted[i] = (restricted[i] + restricted[pivot_core]) % 2
        restricted[pivot_core] = 0
        
        # Extract 7×9×9 core
        indices = [j for j in range(8) if j != pivot_core]
        sub = restricted[indices]
        
        # Compute flattening ranks
        flat_a = sub.reshape(7, 81)
        flat_b = sub.transpose(1,0,2).reshape(9, 63)
        flat_c = sub.transpose(2,0,1).reshape(9, 63)
        
        ra = f2_rank(flat_a)
        rb = f2_rank(flat_b)
        rc = f2_rank(flat_c)
        flb = max(ra, rb, rc)
        
        if flb not in flb_counts:
            flb_counts[flb] = 0
        flb_counts[flb] += 1
    
    print(f"  Flattening lower bound distribution over 255 core restrictions:")
    for lb, cnt in sorted(flb_counts.items()):
        print(f"    FLB >= {lb}: {cnt} restrictions")
    
    # Note: Wang's LBs are MUCH stronger than flattening.
    # Flattening gives 7 or 9 typically, while Wang gives 17-18.
    # The flattening LBs don't directly help for rank-19 feasibility.
    
    # The TRUE occupation constraints from Wang are:
    # For the 6 orbit types with E11, the LBs are 17 and 18.
    # Under the stabilizer of E11, the 255 core vectors are partitioned.
    # To compute orbit sizes, I need the stabilizer group.
    
    # For now, save the analysis and flag what's needed.
    
    results = {
        'core': 'E11',
        'core_shape': [8, 9, 9],
        'all_slice_ranks': [3]*8,
        'orbits_with_e11': orbits_with_e11,
        'flattening_lb_distribution': flb_counts,
        'notes': [
            'Occupation constraint: for rank-19, each core restriction kernel vector has multiplicity ≤ 19-LB',
            'LB=17 orbit: multiplicity ≤ 2',
            'LB=18 orbits: multiplicity ≤ 1',
            'Need orbit sizes under stabilizer of E11 to determine if rank 19 is feasible',
            'Key question: is the total capacity Σ (19-LB(m)) × orbit_size(m) ≥ 19?',
        ],
    }
    
    with open(outdir / 'occupation_analysis.json', 'w') as f:
        json.dump(results, f, indent=2, default=str)
    
    print(f"\nSaved to {outdir}/occupation_analysis.json")

if __name__ == '__main__':
    main()
