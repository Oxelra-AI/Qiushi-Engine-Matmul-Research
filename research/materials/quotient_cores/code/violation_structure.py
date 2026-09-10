#!/usr/bin/env python3
"""analysis (part 4): Near-miss Wang violation structure analysis.

Check the 9 violations of the near-miss support: their dimensions, L values,
and whether they correspond to any dual-line D⊥ subspaces. This informs
what kind of global obstruction to pursue next.
"""
import json
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np

WDIR = Path("research/research_record/workspace")
SCRIPTS = WDIR / "scripts"
ODIR = WDIR / "data" / "pencil_wang_comparison"
ODIR.mkdir(parents=True, exist_ok=True)

if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from wang_capacity_lazy import rref_basis, pack_basis, unpack_basis, in_rowspace, subspace_points_from_basis
from core_capacity_from_wang_lut import CoreQuotient, load_lut


def gf2_inner(a, b):
    return bin(a & b).count('1') % 2


def main():
    t0 = time.time()

    # Load LUT
    lut_path = WDIR / "data" / "wang_f2_lb20" / "wang_subspace_lut.pkl"
    lut, meta = load_lut(lut_path)
    core = CoreQuotient(1)

    # Near-miss support
    S = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]
    s = 19

    # Check ALL subset-span Wang rows for the near-miss
    # For efficiency, only enumerate spans of the support points
    # (violations must occur on subspaces spanned by support elements)
    m = len(S)
    violations = []

    # Build all subset spans
    basis_by_mask = {0: tuple()}
    key_checked = set()

    for mask in range(1, 1 << m):
        lb = mask & -mask
        j = lb.bit_length() - 1
        prev = mask ^ lb
        b = rref_basis(list(basis_by_mask[prev]) + [S[j]], n=8)
        basis_by_mask[mask] = b
        key8 = pack_basis(b)
        if key8 in key_checked:
            continue
        key_checked.add(key8)

        dim8 = key8 & 0xF
        key9 = core.key9_from_key8(key8)
        L = lut.get(key9, None)
        if L is None:
            continue

        # Count occupancy
        pts = subspace_points_from_basis(unpack_basis(key8))
        occ = sum(1 for p in S if p in pts)
        cap = s - L

        if occ > cap:
            violations.append({
                'key8': key8,
                'dim8': dim8,
                'key9': key9,
                'dim9': key9 & 0xF,
                'L': L,
                'cap': cap,
                'occ': occ,
                'excess': occ - cap,
                'basis8': [int(x) for x in unpack_basis(key8)],
            })

    violations.sort(key=lambda v: (v['excess'], v['L'], -v['dim8']), reverse=True)

    print(f"Near-miss Wang violations: {len(violations)}")
    print(f"Violations by dim8: {dict(Counter(v['dim8'] for v in violations))}")
    print(f"Violations by L: {dict(Counter(v['L'] for v in violations))}")
    print(f"Violations by excess: {dict(Counter(v['excess'] for v in violations))}")

    print(f"\nAll violations:")
    for v in violations:
        print(f"  dim8={v['dim8']} L={v['L']} cap={v['cap']} occ={v['occ']} "
              f"excess={v['excess']} basis={v['basis8']}")

    # For each violation, check if the violating subspace is D⊥ for some dual line
    # A 6D subspace U is D⊥ iff U = ker(q1) ∩ ker(q2) for some q1, q2
    # Equivalently, U⊥ = D has dimension 2
    for v in violations:
        if v['dim8'] == 6:
            # Find D = U⊥ (the 2D dual subspace)
            basis = unpack_basis(v['key8'])
            # D = U⊥: find two independent functionals orthogonal to all basis vectors
            dual_basis = []
            for q in range(1, 256):
                if all(gf2_inner(q, b) == 0 for b in basis):
                    dual_basis = list(rref_basis(dual_basis + [q], n=8))
                    if len(dual_basis) == 2:
                        break
            v['dual_D'] = [int(x) for x in dual_basis]
            v['dual_D_third'] = int(dual_basis[0]) ^ int(dual_basis[1]) if len(dual_basis) == 2 else None

    # Check if violation subspaces are related to contraction ranks
    T = np.zeros((8, 9, 9), dtype=np.uint8)
    idx = 0
    for i in range(3):
        for j in range(3):
            if i == 0 and j == 0:
                continue
            for k in range(3):
                T[idx, 3*j+k, 3*i+k] = 1
            idx += 1

    def crank(q):
        M = np.zeros((9,9), dtype=np.uint8)
        for j in range(8):
            if (q >> j) & 1:
                M = (M + T[j]) % 2
        from pencil_wang_comparison import gf2_rank
        return gf2_rank(M)

    for v in violations:
        if 'dual_D' in v and len(v['dual_D']) == 2:
            q1, q2 = v['dual_D']
            q3 = q1 ^ q2
            v['contraction_ranks'] = [crank(q1), crank(q2), crank(q3)]
            v['rank_type'] = tuple(sorted(v['contraction_ranks']))

    print(f"\nViolation subspace details:")
    for v in violations:
        extra = ""
        if 'dual_D' in v:
            extra = f" D={v['dual_D']} ranks={v.get('contraction_ranks', '?')} type={v.get('rank_type', '?')}"
        print(f"  dim8={v['dim8']} L={v['L']} occ={v['occ']}{extra}")

    results = {
        'near_miss': S,
        'total_violations': len(violations),
        'by_dim': {str(k): v for k, v in Counter(vv['dim8'] for vv in violations).items()},
        'by_L': {str(k): v for k, v in Counter(vv['L'] for vv in violations).items()},
        'violations': violations,
        'elapsed_sec': time.time() - t0,
    }

    out = ODIR / "near_miss_violation_structure.json"
    with open(out, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nSaved: {out}")
    print(f"Elapsed: {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
