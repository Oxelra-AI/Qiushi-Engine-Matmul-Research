#!/usr/bin/env python3
"""Build the three Wang codim-1 restricted cores of T<3,3,3> over F2
and compute their structural invariants.

Each core is an 8x9x9 tensor obtained by applying one Wang constraint
(a linear functional on the A-mode set to 0). The three constraints are:
  mask  1 = E11 (bit 0):          a00 = 0, pivot=0, no free
  mask 10 = E12+E21 (bits 1,3):   a10 = related analysis, pivot=3, free={1}
  mask 84 = E13+E22+E31 (bits 2,4,6): a20 = related analysis+a11, pivot=6, free={2,4}

For any constraint, T = T_restricted + mask_vec ⊗ T[pivot,:,:].
Since every A-slice of T<3,3,3> has B⊗C matrix rank 3,
  R(T) ≤ R(core) + 3.
Wang certifies R(core) ≥ 19 for all three.
So: R(core) = 19 implies R_F2(T) ≤ 22.
    R(core) ≥ 20 implies R_F2(T) ≥ 21.
"""

import numpy as np
import json, sys
from pathlib import Path
from collections import Counter

# ─── F2 linear algebra ──────────────────────────────────────

def f2_rank(M):
    """Gaussian elimination rank over F2."""
    m = M.copy().astype(np.uint8) % 2
    rows, cols = m.shape
    rank = 0
    for col in range(cols):
        pivot_row = None
        for row in range(rank, rows):
            if m[row, col] & 1:
                pivot_row = row
                break
        if pivot_row is None:
            continue
        if pivot_row != rank:
            m[[rank, pivot_row]] = m[[pivot_row, rank]]
        for row in range(rows):
            if row != rank and (m[row, col] & 1):
                m[row] ^= m[rank]
        rank += 1
    return rank

# ─── Tensor construction ────────────────────────────────────

def build_matmul_tensor_f2(n0=3, n1=3, n2=3):
    """T_{<n0,n1,n2>} over F2.
    A-coords: (i,j), index = n1*i + j,  dim NA = n0*n1
    B-coords: (j,k), index = n2*j + k,  dim NB = n1*n2
    C-coords: (i,k), index = n2*i + k,  dim NC = n0*n2
    T[a,b,c] = 1 iff a=(i,j), b=(j,k), c=(i,k) for some i,j,k
    Row-major: (AB)_{ik} = Σ_j A_{ij} B_{jk}, output C_{ik}.
    """
    na, nb, nc = n0*n1, n1*n2, n0*n2
    T = np.zeros((na, nb, nc), dtype=np.uint8)
    for i in range(n0):
        for j in range(n1):
            for k in range(n2):
                a = n1*i + j
                b = n2*j + k
                c = n2*i + k  # C-index = (i,k) row-major
                T[a, b, c] = 1
    return T

def apply_constraint_f2(T, mask):
    """Apply one F2 constraint (RREF row) to A-mode.
    Returns the full 9x9x9 tensor with pivot slice zeroed and
    free slices XOR-folded."""
    result = T.copy()
    pivot = mask.bit_length() - 1
    free_bits = mask ^ (1 << pivot)
    na = T.shape[0]
    for i in range(na):
        if (free_bits >> i) & 1:
            result[i] = (result[i] + result[pivot]) % 2
    result[pivot] = 0
    return result, pivot

def extract_core(T_full, pivot):
    """Remove zero pivot slice to get (NA-1)×NB×NC core."""
    indices = [i for i in range(T_full.shape[0]) if i != pivot]
    return T_full[indices], indices

# ─── Invariant computation ──────────────────────────────────

def flattening_ranks(T):
    na, nb, nc = T.shape
    flat_a = T.reshape(na, nb*nc)
    flat_b = T.transpose(1, 0, 2).reshape(nb, na*nc)
    flat_c = T.transpose(2, 0, 1).reshape(nc, na*nb)
    return {
        'A_flat_rank': f2_rank(flat_a),
        'B_flat_rank': f2_rank(flat_b),
        'C_flat_rank': f2_rank(flat_c),
        'A_flat_shape': [na, nb*nc],
        'B_flat_shape': [nb, na*nc],
        'C_flat_shape': [nc, na*nb],
    }

def slice_ranks(T, mode_name, mode_axis):
    """Compute rank of each slice along given mode axis."""
    n = T.shape[mode_axis]
    ranks = []
    for idx in range(n):
        sl = np.take(T, idx, axis=mode_axis)
        ranks.append(int(f2_rank(sl)))
    return {
        f'{mode_name}_slice_ranks': ranks,
        f'{mode_name}_slice_rank_max': max(ranks),
        f'{mode_name}_slice_rank_min': min(ranks),
        f'{mode_name}_slice_rank_distribution': dict(Counter(ranks)),
    }

def removed_slice_info(T_original, pivot):
    """Info about the A-slice at the pivot coordinate."""
    sl = T_original[pivot]  # NB x NC matrix
    return {
        'pivot': pivot,
        'removed_slice_rank': int(f2_rank(sl)),
        'removed_slice_nnz': int(np.sum(sl)),
        'removed_slice_shape': list(sl.shape),
    }

def nonzero_stats(T):
    return {
        'nnz': int(np.sum(T)),
        'total_entries': int(np.prod(T.shape)),
        'density': float(np.sum(T)) / float(np.prod(T.shape)),
    }

# ─── Scheme reading and restriction ────────────────────────

def read_qmm_scheme(path):
    terms = []
    term = {}
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line.startswith('term '):
                if 'u' in term:
                    terms.append(term)
                term = {'index': int(line.split()[1])}
            elif line.startswith('u '):
                term['u'] = list(map(int, line.split()[1:]))
            elif line.startswith('v '):
                term['v'] = list(map(int, line.split()[1:]))
            elif line.startswith('w '):
                term['w'] = list(map(int, line.split()[1:]))
    if 'u' in term:
        terms.append(term)
    return terms

def restrict_scheme_f2(terms, mask):
    """Restrict rank-1 terms to the F2 hyperplane defined by mask.
    Returns list of restricted terms, with A-factor projected and
    terms with zero A-factor removed. Also tracks cancellations."""
    pivot = mask.bit_length() - 1
    free_bits = mask ^ (1 << pivot)
    na = len(terms[0]['u'])

    restricted = []
    vanished_indices = []
    for t in terms:
        u = [abs(x) % 2 for x in t['u']]  # -1 -> 1 over F2
        v = [abs(x) % 2 for x in t['v']]
        w = [abs(x) % 2 for x in t['w']]

        # Fold pivot into free coords
        for i in range(na):
            if (free_bits >> i) & 1:
                u[i] = (u[i] + u[pivot]) % 2
        u[pivot] = 0

        # Extract core A-vector (drop pivot coordinate)
        u_core = tuple(u[i] for i in range(na) if i != pivot)

        if any(u_core):
            restricted.append({
                'u': list(u_core),
                'v': v,
                'w': w,
                'original_index': t['index'],
            })
        else:
            vanished_indices.append(t['index'])

    return restricted, vanished_indices

def verify_restricted_decomposition(core, restricted_terms, na_core, nb, nc):
    """Check that Σ u⊗v⊗w = core over F2."""
    recon = np.zeros((na_core, nb, nc), dtype=np.uint8)
    for t in restricted_terms:
        u = np.array(t['u'], dtype=np.uint8).reshape(na_core, 1, 1)
        v = np.array(t['v'], dtype=np.uint8).reshape(1, nb, 1)
        w = np.array(t['w'], dtype=np.uint8).reshape(1, 1, nc)
        recon = (recon + u * v * w) % 2
    return np.array_equal(recon, core % 2)

def check_duplicate_terms(restricted_terms):
    """Check for identical (u,v,w) triples that would cancel over F2."""
    triples = [(tuple(t['u']), tuple(t['v']), tuple(t['w']))
               for t in restricted_terms]
    counts = Counter(triples)
    duplicates = {str(k): v for k, v in counts.items() if v > 1}
    effective_length = sum(v % 2 for v in counts.values())
    return {
        'raw_surviving_terms': len(restricted_terms),
        'unique_triples': len(counts),
        'duplicate_triples': duplicates,
        'effective_f2_length': effective_length,
    }

# ─── A-coordinate label map ─────────────────────────────────

def a_coord_labels(n0=3, n1=3):
    """Map A-indices to matrix-entry names."""
    labels = []
    for i in range(n0):
        for j in range(n1):
            labels.append(f'a{i}{j}')
    return labels

def core_coord_labels(all_labels, pivot):
    return [all_labels[i] for i in range(len(all_labels)) if i != pivot]

# ─── Main ───────────────────────────────────────────────────

def main():
    outdir = Path('data/restricted_cores')
    outdir.mkdir(parents=True, exist_ok=True)

    # Build T<3,3,3> over F2
    T = build_matmul_tensor_f2()
    print(f'T<3,3,3> shape: {T.shape}, nnz: {np.sum(T)}, entries: {np.prod(T.shape)}')

    # Full tensor invariants
    full_inv = flattening_ranks(T)
    full_inv.update(nonzero_stats(T))
    print(f'Full tensor flattenings: A={full_inv["A_flat_rank"]}, B={full_inv["B_flat_rank"]}, C={full_inv["C_flat_rank"]}')

    a_labels = a_coord_labels()
    masks = {
        'mask_001_E11':          {'mask': 1,  'label': 'E11'},
        'mask_010_E12_E21':      {'mask': 10, 'label': 'E12+E21'},
        'mask_084_E13_E22_E31':  {'mask': 84, 'label': 'E13+E22+E31'},
    }

    scheme_path = Path('data/cn122_3x3_r23_repro/scheme.qmm')
    terms = read_qmm_scheme(scheme_path)
    print(f'\ncn122 scheme: {len(terms)} terms')

    results = {'full_tensor': full_inv, 'cores': {}}

    for name, info in masks.items():
        mask = info['mask']
        label = info['label']
        print(f'\n{"="*60}')
        print(f'Constraint: {label}, mask={mask} (0b{mask:09b})')

        pivot = mask.bit_length() - 1
        free_bits = mask ^ (1 << pivot)
        free_list = [i for i in range(9) if (free_bits >> i) & 1]
        print(f'  Pivot bit: {pivot} ({a_labels[pivot]})')
        print(f'  Free bits: {free_list} ({[a_labels[i] for i in free_list]})')

        # Apply constraint
        T_restr, piv = apply_constraint_f2(T, mask)
        core, core_indices = extract_core(T_restr, piv)
        core_labels = core_coord_labels(a_labels, piv)
        print(f'  Core shape: {core.shape}')
        print(f'  Core A-coordinates: {core_labels}')

        # Verify reconstruction: T = T_restr + mask_vec ⊗ T[pivot,:,:]
        mask_vec = np.zeros(9, dtype=np.uint8)
        for bit in range(9):
            if (mask >> bit) & 1:
                mask_vec[bit] = 1
        recon = (T_restr + np.einsum('a,bc->abc', mask_vec, T[pivot])) % 2
        assert np.array_equal(recon, T), f"Reconstruction check failed for {name}"
        print(f'  ✓ T = T_restricted + mask_vec ⊗ T[pivot,:,:] verified')

        # Removed slice info
        rem_info = removed_slice_info(T, pivot)
        print(f'  Removed slice rank: {rem_info["removed_slice_rank"]}, nnz: {rem_info["removed_slice_nnz"]}')

        # Core invariants
        core_flat = flattening_ranks(core)
        core_nnz = nonzero_stats(core)
        print(f'  Core flattenings: A={core_flat["A_flat_rank"]}, B={core_flat["B_flat_rank"]}, C={core_flat["C_flat_rank"]}')
        print(f'  Core nnz: {core_nnz["nnz"]}/{core_nnz["total_entries"]} (density {core_nnz["density"]:.4f})')

        # Slice ranks
        b_slices = slice_ranks(core, 'B', 1)
        c_slices = slice_ranks(core, 'C', 2)
        a_slices = slice_ranks(core, 'A', 0)
        print(f'  A-slice rank dist: {a_slices["A_slice_rank_distribution"]}')
        print(f'  B-slice rank dist: {b_slices["B_slice_rank_distribution"]}')
        print(f'  C-slice rank dist: {c_slices["C_slice_rank_distribution"]}')
        print(f'  Forced product bound (B-slice max): {b_slices["B_slice_rank_max"]}')
        print(f'  Forced product bound (C-slice max): {c_slices["C_slice_rank_max"]}')

        # Restrict cn122
        restricted, vanished = restrict_scheme_f2(terms, mask)
        print(f'\n  cn122 restriction:')
        print(f'    Vanished terms (zero A-factor): {len(vanished)} (indices: {vanished})')
        print(f'    Surviving terms: {len(restricted)}')

        dup_info = check_duplicate_terms(restricted)
        print(f'    Unique (u,v,w) triples: {dup_info["unique_triples"]}')
        print(f'    Effective F2 length: {dup_info["effective_f2_length"]}')
        if dup_info['duplicate_triples']:
            print(f'    Duplicate triples: {dup_info["duplicate_triples"]}')

        # Verify the restricted decomposition
        ok = verify_restricted_decomposition(core, restricted, *core.shape)
        print(f'    ✓ Restricted decomposition verified: {ok}')

        # Save core tensor as npy and metadata
        np.save(outdir / f'{name}_core.npy', core)
        core_meta = {
            'name': name,
            'mask': mask,
            'mask_binary': f'0b{mask:09b}',
            'label': label,
            'pivot': pivot,
            'pivot_label': a_labels[pivot],
            'free_bits': free_list,
            'free_labels': [a_labels[i] for i in free_list],
            'core_shape': list(core.shape),
            'core_a_coordinates': core_labels,
            'core_a_indices': core_indices,
            'removed_slice': rem_info,
            'flattenings': core_flat,
            'nonzero_stats': core_nnz,
            'A_slices': a_slices,
            'B_slices': b_slices,
            'C_slices': c_slices,
            'forced_product_lower_bound': max(b_slices['B_slice_rank_max'],
                                               c_slices['C_slice_rank_max']),
            'cn122_restriction': {
                'vanished_indices': vanished,
                'surviving_count': len(restricted),
                **dup_info,
                'decomposition_verified': ok,
            },
            'wang_certified_lower_bound': 19,
            'rank_upper_bound_from_cn122': dup_info['effective_f2_length'],
            'rank_dichotomy': (
                f'If R_F2(core) = 19 then R_F2(T) <= 19 + {rem_info["removed_slice_rank"]} = '
                f'{19 + rem_info["removed_slice_rank"]}. '
                f'If R_F2(core) >= 20 then R_F2(T) >= 21.'
            ),
        }
        results['cores'][name] = core_meta

        with open(outdir / f'{name}_meta.json', 'w') as f:
            json.dump(core_meta, f, indent=2)

    # Save master summary
    with open(outdir / 'cores_summary.json', 'w') as f:
        json.dump(results, f, indent=2)
    print(f'\n\nAll results saved to {outdir}/')

    # Print the dichotomy table
    print(f'\n{"="*60}')
    print(f'DICHOTOMY TABLE')
    print(f'{"="*60}')
    for name, meta in results['cores'].items():
        label = meta['label']
        lb = meta['wang_certified_lower_bound']
        ub = meta['rank_upper_bound_from_cn122']
        fp = meta['forced_product_lower_bound']
        sl_rk = meta['removed_slice']['removed_slice_rank']
        eff = meta['cn122_restriction']['effective_f2_length']
        print(f'\n  {label} (mask {meta["mask"]}):')
        print(f'    Wang certified:     R_F2(core) >= {lb}')
        print(f'    cn122 restriction:  R_F2(core) <= {ub} ({eff} effective terms)')
        print(f'    Forced product:     R_F2(core) >= {fp}')
        print(f'    Removed slice rank: {sl_rk}')
        print(f'    => If R(core)=19: R_F2(T) <= {19+sl_rk}')
        print(f'    => If R(core)>=20: R_F2(T) >= 21')

if __name__ == '__main__':
    main()
