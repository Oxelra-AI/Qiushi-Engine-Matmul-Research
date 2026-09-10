#!/usr/bin/env python3
"""this investigation verification of the E11 quotient stabilizer action on A/<E00>.

This is a compact, self-contained replay of the quotient-action object needed for
sound orbit branching in the rank-19 E11-core CPD SAT search.

Covector action for matrix multiplication factors:
    U -> P^T U Q^{-T},  V -> Q^T V R^{-T},  W -> P^{-1} W R.
For the quotient by <E00>, the A-side action is well-defined exactly when
    row_0(P)=e0^T and col_0(Q)=e0,
so P and Q each range over a 24-element subgroup of GL(3,2).  With R=I these
576 pairs preserve the E11 core tensor.  The induced action partitions the 255
nonzero quotient A-points into 8 orbits of sizes [3,3,9,36,36,36,36,96].

The output JSON includes full orbit members; this is required for complete
branch CNFs that forbid all earlier orbit members and force one representative
from the branch orbit.
"""
from __future__ import annotations

import argparse
import json
import time
from collections import Counter, deque
from pathlib import Path
from typing import Iterable

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DEFAULT_OUT = WS / "data" / "e11_orbits" / "e11_quotient_orbits.json"


def mat_from_mask(x: int) -> np.ndarray:
    return np.array([[(int(x) >> (3 * i + j)) & 1 for j in range(3)] for i in range(3)], dtype=np.uint8)


def mask_from_mat(M: np.ndarray) -> int:
    A = M.astype(np.uint8) & 1
    out = 0
    for i in range(3):
        for j in range(3):
            if int(A[i, j]):
                out |= 1 << (3 * i + j)
    return out


def I3() -> np.ndarray:
    return np.eye(3, dtype=np.uint8)


def mm(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    return (A @ B) & 1


def gf2_rank(M: np.ndarray) -> int:
    A = M.copy().astype(np.uint8) & 1
    r = 0
    rows, cols = A.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if A[i, c]:
                piv = i
                break
        if piv is None:
            continue
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for i in range(rows):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        r += 1
    return r


def mat_inv(M: np.ndarray) -> np.ndarray:
    A = np.concatenate([M.copy().astype(np.uint8) & 1, I3()], axis=1)
    r = 0
    for c in range(3):
        piv = None
        for i in range(r, 3):
            if A[i, c]:
                piv = i
                break
        if piv is None:
            raise ValueError("singular matrix")
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for i in range(3):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        r += 1
    return A[:, 3:]


def generate_gl3() -> list[np.ndarray]:
    return [mat_from_mask(x) for x in range(512) if gf2_rank(mat_from_mask(x)) == 3]


def lower_right_swap() -> np.ndarray:
    M = I3(); M[1, 1] = 0; M[2, 2] = 0; M[1, 2] = 1; M[2, 1] = 1
    return M


def lower_right_shear() -> np.ndarray:
    M = I3(); M[1, 2] = 1
    return M


def P_row_stabilizer_generators() -> list[np.ndarray]:
    g10 = I3(); g10[1, 0] = 1
    g20 = I3(); g20[2, 0] = 1
    return [g10, g20, lower_right_swap(), lower_right_shear()]


def Q_col_stabilizer_generators() -> list[np.ndarray]:
    g01 = I3(); g01[0, 1] = 1
    g02 = I3(); g02[0, 2] = 1
    return [g01, g02, lower_right_swap(), lower_right_shear()]


def subgroup_closure(gens: list[np.ndarray]) -> list[np.ndarray]:
    full_gens = [g.astype(np.uint8) & 1 for g in gens]
    full_gens += [mat_inv(g) for g in full_gens]
    ident = I3()
    seen = {mask_from_mat(ident): ident}
    q = deque([ident])
    while q:
        A = q.popleft()
        for G in full_gens:
            for H in (mm(G, A), mm(A, G)):
                k = mask_from_mat(H)
                if k not in seen:
                    seen[k] = H
                    q.append(H)
    return [seen[k] for k in sorted(seen)]


def quotient_mask_from_full_drop_bit0(full: int) -> int:
    q = 0; j = 0
    for bit in range(9):
        if bit == 0:
            continue
        if (int(full) >> bit) & 1:
            q |= 1 << j
        j += 1
    return q


def full_mask_from_quotient_section(q: int) -> int:
    full = 0; j = 0
    for bit in range(9):
        if bit == 0:
            continue
        if (int(q) >> j) & 1:
            full |= 1 << bit
        j += 1
    return full


def apply_A_quotient(q: int, P: np.ndarray, Q: np.ndarray) -> int:
    M = mat_from_mask(full_mask_from_quotient_section(q))
    N = (P.T @ M @ mat_inv(Q).T) & 1
    return quotient_mask_from_full_drop_bit0(mask_from_mat(N))


def apply_A_quotient_from_full(full: int, P: np.ndarray, Q: np.ndarray) -> int:
    M = mat_from_mask(full)
    N = (P.T @ M @ mat_inv(Q).T) & 1
    return quotient_mask_from_full_drop_bit0(mask_from_mat(N))


def perm_for_pair(P: np.ndarray, Q: np.ndarray) -> tuple[int, ...]:
    return tuple([0] + [apply_A_quotient(q, P, Q) for q in range(1, 256)])


def perm_compose(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(p[q[i]] for i in range(256))


def permutation_closure(gens0: list[tuple[int, ...]]) -> set[tuple[int, ...]]:
    ident = tuple(range(256))
    gens = list(gens0)
    # include short powers to avoid assuming generators are involutions
    for g in list(gens0):
        h = g
        for _ in range(1, 8):
            h = perm_compose(g, h)
            gens.append(h)
            if h == ident:
                break
    seen = {ident}
    q = deque([ident])
    while q:
        p = q.popleft()
        for g in gens:
            for h in (perm_compose(g, p), perm_compose(p, g)):
                if h not in seen:
                    seen.add(h)
                    q.append(h)
    return seen


def build_e11_core() -> np.ndarray:
    T = np.zeros((8, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            a_full = 3 * i + j
            if a_full == 0:
                continue
            for k in range(3):
                T[a_full - 1, 3 * j + k, 3 * i + k] = 1
    return T


def vec_from_mask(mask: int, n: int) -> np.ndarray:
    return np.array([(int(mask) >> i) & 1 for i in range(n)], dtype=np.uint8)


def add_outer(T: np.ndarray, q: int, v: int, w: int):
    T ^= (vec_from_mask(q, T.shape[0]).reshape(-1, 1, 1)
          * vec_from_mask(v, T.shape[1]).reshape(1, -1, 1)
          * vec_from_mask(w, T.shape[2]).reshape(1, 1, -1)).astype(np.uint8)


def apply_B(v: int, Q: np.ndarray, R: np.ndarray | None = None) -> int:
    if R is None:
        R = I3()
    M = mat_from_mask(v)
    N = (Q.T @ M @ mat_inv(R).T) & 1
    return mask_from_mat(N)


def apply_W(w: int, P: np.ndarray, R: np.ndarray | None = None) -> int:
    if R is None:
        R = I3()
    M = mat_from_mask(w)
    N = (mat_inv(P) @ M @ R) & 1
    return mask_from_mat(N)


def transform_core(core: np.ndarray, P: np.ndarray, Q: np.ndarray) -> np.ndarray:
    out = np.zeros_like(core)
    for a in range(8):
        q2 = apply_A_quotient(1 << a, P, Q)
        for b in range(9):
            v2 = apply_B(1 << b, Q)
            for c in range(9):
                if int(core[a, b, c]):
                    w2 = apply_W(1 << c, P)
                    add_outer(out, q2, v2, w2)
    return out


def A_point_signature(q: int) -> dict:
    M = mat_from_mask(full_mask_from_quotient_section(q))
    row0_tail = int(M[0, 1]) + 2 * int(M[0, 2])
    col0_tail = int(M[1, 0]) + 2 * int(M[2, 0])
    return {
        "section_rank": gf2_rank(M),
        "row0_tail_nonzero": bool(row0_tail),
        "col0_tail_nonzero": bool(col0_tail),
        "weight": int(q).bit_count(),
    }


def orbit_partition(perms: Iterable[tuple[int, ...]]) -> tuple[list[dict], dict[int, int]]:
    perms = list(perms)
    unseen = set(range(1, 256))
    orbits = []
    point_orbit = {}
    while unseen:
        seed = min(unseen)
        orb = {seed}
        stack = [seed]
        while stack:
            x = stack.pop()
            for p in perms:
                y = p[x]
                if y not in orb:
                    orb.add(y)
                    stack.append(y)
        idx = len(orbits)
        for x in orb:
            point_orbit[x] = idx
        members = sorted(orb)
        sig_counter = Counter(json.dumps(A_point_signature(x), sort_keys=True) for x in members)
        orbits.append({
            "orbit": idx,
            "seed": seed,
            "rep": seed,
            "size": len(members),
            "members": members,
            "members_by_weight_then_value_head": sorted(members, key=lambda z: (z.bit_count(), z))[:20],
            "signature_counts": {k: v for k, v in sorted(sig_counter.items())},
            "weight_counts": {str(k): v for k, v in sorted(Counter(x.bit_count() for x in members).items())},
        })
        unseen -= orb
    return orbits, point_orbit


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=DEFAULT_OUT)
    ap.add_argument("--save-perms", action="store_true")
    args = ap.parse_args()

    t0 = time.time()
    gl = generate_gl3()
    P_direct = [G for G in gl if np.array_equal(G[0, :], np.array([1, 0, 0], dtype=np.uint8))]
    Q_direct = [G for G in gl if np.array_equal(G[:, 0], np.array([1, 0, 0], dtype=np.uint8))]
    P_gen = subgroup_closure(P_row_stabilizer_generators())
    Q_gen = subgroup_closure(Q_col_stabilizer_generators())
    assert {mask_from_mat(x) for x in P_direct} == {mask_from_mat(x) for x in P_gen}
    assert {mask_from_mat(x) for x in Q_direct} == {mask_from_mat(x) for x in Q_gen}

    I = I3()
    gen_perms = [perm_for_pair(P, I) for P in P_row_stabilizer_generators()] + [perm_for_pair(I, Q) for Q in Q_col_stabilizer_generators()]
    closure = permutation_closure(gen_perms)
    explicit = {perm_for_pair(P, Q) for P in P_direct for Q in Q_direct}
    perm_bijective = all(p[0] == 0 and set(p[1:]) == set(range(1, 256)) for p in explicit)

    well_defined_failures = []
    for P in P_direct:
        for Q in Q_direct:
            for q in range(256):
                full = full_mask_from_quotient_section(q)
                a = apply_A_quotient_from_full(full, P, Q)
                b = apply_A_quotient_from_full(full ^ 1, P, Q)
                if a != b:
                    well_defined_failures.append({"q": q, "P": mask_from_mat(P), "Q": mask_from_mat(Q), "a": a, "b": b})
                    break
            if well_defined_failures:
                break
        if well_defined_failures:
            break

    core = build_e11_core()
    tensor_failures = []
    for P in P_direct:
        for Q in Q_direct:
            image = transform_core(core, P, Q)
            if not np.array_equal(image, core):
                tensor_failures.append({"P": mask_from_mat(P), "Q": mask_from_mat(Q), "diff": int(np.sum(image ^ core))})
                if len(tensor_failures) >= 5:
                    break
        if len(tensor_failures) >= 5:
            break

    orbits, point_orbit = orbit_partition(explicit)
    sizes = sorted(o["size"] for o in orbits)
    result = {
        "purpose": "this investigation E11 quotient stabilizer action and nonzero quotient-point orbit cover for rank-19 core SAT branching.",
        "field": "F2",
        "action": "q=[U] -> [P^T U Q^{-T}] modulo <E00>; P row0=e0^T, Q col0=e0; R=I on B/C for core preservation check.",
        "subgroup_sizes": {
            "GL3": len(gl),
            "P_row_stabilizer": len(P_direct),
            "Q_col_stabilizer": len(Q_direct),
            "explicit_pairs": len(P_direct) * len(Q_direct),
            "distinct_permutations": len(explicit),
            "generator_closure": len(closure),
        },
        "checks": {
            "generator_closure_equals_explicit_pairs": closure == explicit,
            "all_perms_bijective_on_nonzero_points": perm_bijective,
            "well_defined_mod_E00": len(well_defined_failures) == 0,
            "well_defined_failures_head": well_defined_failures[:5],
            "all_preserve_E11_core_tensor": len(tensor_failures) == 0,
            "tensor_failures_head": tensor_failures,
            "point_orbit_sizes_sorted_expected": sizes == [3, 3, 9, 36, 36, 36, 36, 96],
        },
        "point_orbits": {
            "num_orbits": len(orbits),
            "sizes_sorted": sizes,
            "orbits": orbits,
            "point_to_orbit": {str(k): v for k, v in sorted(point_orbit.items())},
        },
        "branch_cover_semantics": "For any CPD with at least one nonzero quotient A-factor, let i be the minimum orbit index among its nonzero u_t values. A stabilizer transform sends one value in orbit i to the listed representative while preserving orbit indices; branch i forbids all earlier orbit members and forces one term to the representative. The union over all i covers all nonzero CPDs satisfying the Brent equations. Zero u_t padding is allowed, but the E11 tensor equations/capacity force some nonzero u_t values.",
        "elapsed_sec": time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")

    if args.save_perms:
        arr = np.array([list(p) for p in sorted(explicit)], dtype=np.uint16)
        perm_path = args.out.with_suffix(".perms.npz")
        np.savez_compressed(perm_path, perms=arr)
        result["perm_npz"] = str(perm_path)

    print(json.dumps({
        "status": "ok",
        "out": str(args.out),
        "P": len(P_direct),
        "Q": len(Q_direct),
        "perms": len(explicit),
        "closure": len(closure),
        "well_defined": len(well_defined_failures) == 0,
        "tensor_preservation": len(tensor_failures) == 0,
        "orbit_sizes_sorted": sizes,
        "checks_ok": (closure == explicit and perm_bijective and not well_defined_failures and not tensor_failures and sizes == [3, 3, 9, 36, 36, 36, 36, 96]),
    }, indent=2, sort_keys=True))

    assert closure == explicit
    assert perm_bijective
    assert not well_defined_failures
    assert not tensor_failures
    assert sizes == [3, 3, 9, 36, 36, 36, 36, 96]


if __name__ == "__main__":
    main()
