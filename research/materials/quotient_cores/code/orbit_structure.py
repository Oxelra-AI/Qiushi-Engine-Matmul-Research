#!/usr/bin/env python3
r"""analysis: E11 stabilizer orbit structure on 255 nonzero core directions.

Compute the orbit decomposition of {1,...,255} under the 1152-element
E11 stabilizer (standard left/right GL(3,F2) fixing E11, with transpose).
This could dramatically reduce the search space for 19-point supports.
"""
from __future__ import annotations
import json, sys, time
from collections import Counter, defaultdict
from pathlib import Path
import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import build_matmul_tensor_f2, contraction_matrix, mat_rank_f2

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/family_consequence"


def build_e11_core_tensor():
    return build_matmul_tensor_f2()[1:,:,:].astype(np.uint8) % 2


def mat3x3_to_8bit(M):
    """Convert 3x3 binary matrix to 8-bit mask (excluding E11 position)."""
    mapping = [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]  # bit 0..7
    val = 0
    for bit, (r,c) in enumerate(mapping):
        if int(M[r,c]) & 1:
            val |= 1 << bit
    return val


def bit8_to_mat3x3(val):
    """Convert 8-bit mask to 3x3 binary matrix (E11=0)."""
    M = np.zeros((3,3), dtype=np.uint8)
    mapping = [(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]
    for bit, (r,c) in enumerate(mapping):
        if (val >> bit) & 1:
            M[r,c] = 1
    return M


def gl3f2_elements():
    """Generate all elements of GL(3,F2) as 3x3 numpy arrays."""
    result = []
    for a in range(512):
        M = np.array([[(a >> (i*3+j)) & 1 for j in range(3)] for i in range(3)], dtype=np.uint8)
        if int(round(abs(np.linalg.det(M.astype(float))))) % 2 == 1:
            result.append(M)
    return result


def apply_conj(P, Q, X):
    """Compute P X Q^T mod 2 (the conjugation action on matrices)."""
    return np.mod(P @ X @ Q.T, 2).astype(np.uint8)


def main():
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)

    T_core = build_e11_core_tensor()

    # Generate GL(3,F2)
    gl3 = gl3f2_elements()
    print(f"|GL(3,F2)| = {len(gl3)}")

    # E11 stabilizer: pairs (P, Q) in GL(3,F2) x GL(3,F2) such that
    # P E11 Q^T = E11, plus optional transpose.
    # P E11 Q^T = P[:,0] Q[:,0]^T, so P[:,0] Q[:,0]^T = E11 = e1 e1^T
    # => P[:,0] = e1 (P fixes first column direction) and Q[:,0] = e1
    # So P and Q both have first column = [1,0,0]^T

    stabilizer_pairs = []
    e1 = np.array([1,0,0], dtype=np.uint8)
    for P in gl3:
        if not np.array_equal(P[:,0] % 2, e1):
            continue
        for Q in gl3:
            if not np.array_equal(Q[:,0] % 2, e1):
                continue
            stabilizer_pairs.append((P, Q))

    print(f"|Stabilizer pairs (P,Q)| = {len(stabilizer_pairs)}")

    # Build the action: for each (P,Q), map 8-bit direction to 8-bit direction
    # Also include transpose: X -> X^T
    # A direction p maps to mat3x3, then P*mat*Q^T, then back to 8-bit
    # For transpose: mat -> mat^T, then 8-bit
    
    # Compute orbit under (P,Q) without transpose first
    point_set = list(range(1, 256))
    orbit_map = {}  # p -> orbit representative
    visited = set()
    orbits_no_trans = []
    
    for p in point_set:
        if p in visited:
            continue
        orbit = set()
        queue = [p]
        while queue:
            curr = queue.pop()
            if curr in orbit:
                continue
            orbit.add(curr)
            X = bit8_to_mat3x3(curr)
            for P, Q in stabilizer_pairs:
                img = apply_conj(P, Q, X)
                img_bit = mat3x3_to_8bit(img)
                if img_bit and img_bit not in orbit:
                    queue.append(img_bit)
        orbits_no_trans.append(sorted(orbit))
        for pp in orbit:
            orbit_map[pp] = min(orbit)
            visited.add(pp)
    
    print(f"Orbits without transpose: {len(orbits_no_trans)}")
    
    # Now with transpose
    visited2 = set()
    orbits_with_trans = []
    
    for p in point_set:
        if p in visited2:
            continue
        orbit = set()
        queue = [p]
        while queue:
            curr = queue.pop()
            if curr in orbit:
                continue
            orbit.add(curr)
            X = bit8_to_mat3x3(curr)
            XT = X.T.copy()
            xt_bit = mat3x3_to_8bit(XT)
            if xt_bit and xt_bit not in orbit:
                queue.append(xt_bit)
            for P, Q in stabilizer_pairs:
                img = apply_conj(P, Q, X)
                img_bit = mat3x3_to_8bit(img)
                if img_bit and img_bit not in orbit:
                    queue.append(img_bit)
                img2 = apply_conj(P, Q, XT)
                img2_bit = mat3x3_to_8bit(img2)
                if img2_bit and img2_bit not in orbit:
                    queue.append(img2_bit)
        orbits_with_trans.append(sorted(orbit))
        for pp in orbit:
            visited2.add(pp)
    
    print(f"Orbits with transpose: {len(orbits_with_trans)}")
    
    # Orbit sizes
    orbit_sizes = sorted([len(o) for o in orbits_with_trans])
    print(f"Orbit sizes: {orbit_sizes}")
    print(f"Sum: {sum(orbit_sizes)} (should be 255)")
    
    # Orbit representatives and matrix rank distribution
    print(f"\nOrbit details:")
    orbit_info = []
    for orb in sorted(orbits_with_trans, key=lambda o: (len(o), o[0])):
        rep = orb[0]
        M = bit8_to_mat3x3(rep)
        rk = np.linalg.matrix_rank(M.astype(float))
        mapping = ["E12","E13","E21","E22","E23","E31","E32","E33"]
        name = "+".join(mapping[i] for i in range(8) if (rep>>i)&1)
        print(f"  rep={rep:3d} ({name:20s}) rank={rk} size={len(orb)}")
        orbit_info.append({
            "representative": rep,
            "name": name,
            "rank": int(rk),
            "size": len(orb),
            "members": orb,
        })

    # How many orbit-level variables for a 19-point support?
    n_orbits = len(orbits_with_trans)
    print(f"\nOrbit-level model: {n_orbits} orbit count variables")
    print(f"Compared to 255 binary point variables")
    
    # For the near-miss: orbit profile
    nm_orbits = Counter()
    for p in [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]:
        for oi in orbit_info:
            if p in oi["members"]:
                nm_orbits[oi["representative"]] += 1
                break
    print(f"\nNear-miss orbit profile: {dict(nm_orbits)}")
    print(f"Near-miss uses {len(nm_orbits)} distinct orbits")

    elapsed = time.time() - t0
    result = {
        "schema": "orbit_structure_v1",
        "elapsed_sec": round(elapsed, 3),
        "stabilizer_order": len(stabilizer_pairs) * 2,  # with transpose
        "orbits_without_transpose": len(orbits_no_trans),
        "orbits_with_transpose": n_orbits,
        "orbit_sizes": orbit_sizes,
        "orbits": [{"rep": oi["representative"], "name": oi["name"],
                     "rank": oi["rank"], "size": oi["size"]}
                    for oi in orbit_info],
        "near_miss_orbit_profile": dict(nm_orbits),
    }
    out = OUTDIR / "orbit_structure.json"
    with open(out, 'w') as f:
        json.dump(result, f, indent=2)
    print(f"\nSaved {out}")
    print(f"Elapsed: {elapsed:.1f}s")


if __name__ == '__main__':
    main()
