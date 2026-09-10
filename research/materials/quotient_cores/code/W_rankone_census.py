#!/usr/bin/env python3
"""analysis: rank-one census of the target space W = col(D).

W is the 9-dimensional column space of the (A,B)|C flattening D of T_{3,3,3}.
Every exact rank-n decomposition over F2 requires n rank-one 9x9 matrices
whose span contains W.  The census of rank-one matrices IN W itself is the
starting structure for any bottom-up construction approach.

We also compute: for each rank-one v in W, the span W' = W + added rank-ones
achievable by greedy extension, the rank-one content at each ARTIFACT, and the
maximal achievable span dimension before running out of new rank-ones.
"""
from __future__ import annotations
import json, sys, time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
import residual_repair_geometry as rg
from linear_completion import build_t333_f2, tensor_to_D

OUTDIR = Path('data/rankone_lattice')


def rank_of_ints(vals):
    piv = {}
    r = 0
    for v in vals:
        x = int(v)
        while x:
            p = x.bit_length() - 1
            if p in piv:
                x ^= piv[p]
            else:
                piv[p] = x
                r += 1
                break
    return r


def all_rank_ones_in_subspace(basis_vectors: List[int]) -> List[Tuple[int, int]]:
    """All nonzero rank-one 9x9 matrices in the span of basis_vectors.
    
    Uses reduced-echelon approach: build echelon basis of the subspace,
    then for each a, find B-kernel of reduction.
    """
    # Build echelon basis
    echelon: Dict[int, int] = {}
    for v in basis_vectors:
        x = int(v)
        while x:
            p = x.bit_length() - 1
            if p in echelon:
                x ^= echelon[p]
            else:
                # Reduce existing entries by new pivot
                for q in list(echelon.keys()):
                    if (echelon[q] >> p) & 1:
                        echelon[q] ^= x
                echelon[p] = x
                break
    
    def reduce(v):
        x = int(v)
        while x:
            p = x.bit_length() - 1
            if p in echelon:
                x ^= echelon[p]
            else:
                break
        return x
    
    out = []
    for a in range(1, 512):
        # For fixed a, column beta maps to a tensor product a ⊗ e_beta (81-bit).
        # Reduce each: if all reduce to 0, then b_mask is in the kernel.
        rems = []
        for beta in range(9):
            v = rg.vec_mask9_to_outer81(a, 1 << beta)
            rems.append(reduce(v))
        # Kernel of the linear map beta -> rem[beta]
        # Find all b such that XOR_{beta set in b} rem[beta] = 0
        piv2 = {}
        free_bits = []
        for beta in range(9):
            x = rems[beta]
            e = 1 << beta
            while x:
                p = x.bit_length() - 1
                if p in piv2:
                    bv, be = piv2[p]
                    x ^= bv
                    e ^= be
                else:
                    piv2[p] = (x, e)
                    break
            if x == 0 and e:
                free_bits.append(e)
        if not free_bits:
            continue
        # Enumerate kernel from free bits
        ker = [0]
        for fb in free_bits:
            ker += [k ^ fb for k in ker]
        for bmask in ker:
            if bmask:
                out.append((a, bmask))
    return out


def greedy_extension(W_basis: List[int], target_dim: int = 22) -> dict:
    """Greedily extend W by adding rank-one matrices outside the current span."""
    current_basis = list(W_basis)
    current_dim = rank_of_ints(current_basis)
    history = [{'dim': current_dim, 'rank_ones_in_span': len(all_rank_ones_in_subspace(current_basis))}]
    
    while current_dim < target_dim:
        # Find all rank-one matrices in the current span
        ro = all_rank_ones_in_subspace(current_basis)
        # Find all rank-one matrices NOT in the span but adjacent
        # (i.e., adding them increases dim by 1)
        extensions = []
        for a in range(1, 512):
            for b in range(1, 512):
                v = rg.vec_mask9_to_outer81(a, b)
                if rank_of_ints(current_basis + [v]) > current_dim:
                    extensions.append((a, b, v))
                    if len(extensions) >= 100:  # sample
                        break
            if len(extensions) >= 100:
                break
        
        if not extensions:
            break
        
        # Among extensions, pick the one that maximizes rank-one content
        # (Greedy: this is just a heuristic)
        best_ext = None
        best_ro_count = -1
        for a, b, v in extensions[:50]:  # test first 50
            test_basis = current_basis + [v]
            ro_count = len(all_rank_ones_in_subspace(test_basis))
            if ro_count > best_ro_count:
                best_ro_count = ro_count
                best_ext = (a, b, v)
        
        if best_ext is None:
            break
        
        a, b, v = best_ext
        current_basis.append(v)
        current_dim += 1
        history.append({
            'dim': current_dim,
            'added': (a, b),
            'rank_ones_in_span': best_ro_count,
        })
    
    return {'final_dim': current_dim, 'history': history}


def main():
    t0 = time.time()
    T = build_t333_f2()
    D = tensor_to_D(T)
    
    # Build W basis as 81-bit integers
    W_basis = []
    for c in range(9):
        v = 0
        for i in range(81):
            if D[i, c] & 1:
                v |= 1 << i
        W_basis.append(v)
    
    print(f'W dimension: {rank_of_ints(W_basis)}')
    
    # Census of rank-one matrices in W
    ro_in_W = all_rank_ones_in_subspace(W_basis)
    print(f'Rank-one matrices in W: {len(ro_in_W)}')
    
    # Classify by A-mask
    a_to_count = Counter()
    for a, b in ro_in_W:
        a_to_count[a] += 1
    print(f'Distinct A-values with rank-ones in W: {len(a_to_count)}')
    print(f'A-multiplicity histogram: {dict(sorted(Counter(a_to_count.values()).items()))}')
    
    # Rank of the rank-one matrices in W
    ro_vecs = [rg.vec_mask9_to_outer81(a, b) for a, b in ro_in_W]
    ro_rank = rank_of_ints(ro_vecs)
    print(f'Rank of rank-one span in W: {ro_rank} (W dim = 9)')
    
    out = {
        'W_dim': 9,
        'rank_ones_in_W': len(ro_in_W),
        'rank_one_span_in_W': ro_rank,
        'distinct_A': len(a_to_count),
        'A_mult_hist': dict(sorted(Counter(a_to_count.values()).items())),
        'rank_one_list': [[a, b] for a, b in ro_in_W],
        'elapsed_sec': time.time() - t0,
    }
    
    OUTDIR.mkdir(parents=True, exist_ok=True)
    op = OUTDIR / 'W_rankone_census.json'
    op.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(f'\nSaved: {op}')
    print(json.dumps({k: v for k, v in out.items() if k != 'rank_one_list'},
                     indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
