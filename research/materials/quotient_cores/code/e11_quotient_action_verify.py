#!/usr/bin/env python3
"""Verify the E11 quotient stabilizer action and point-orbit partition over F2.

The E11 restricted core is the projection of the A-factor space by the killed
line <E00>.  Full 3x3 matrix-multiplication decompositions use the covector
isotropy

    U -> P^T U Q^{-T},   V -> Q^T V R^{-T},   W -> P^{-1} W R.

A full action induces a well-defined action on A/<E00> exactly when the killed
line is invariant, i.e. P^T E00 Q^{-T} = E00 over F2.  Equivalently

    row_0(P) = e0^T,    col_0(Q) = e0.

This script rebuilds those two 24-element subgroups from explicit generators,
checks closure against direct enumeration, verifies that the induced quotient
permutations form the same 576-element action as all subgroup pairs, checks
well-definedness on quotient representatives, verifies preservation of the E11
core tensor (with R=I) for every pair, and records the nonzero point orbits in
F2^8.  It also computes the older complement-preserving partition for comparison
only, resolving the conflicting analysis/analysis orbit-size records.
"""
from __future__ import annotations

import argparse
import json
import time
from collections import Counter, deque
from pathlib import Path
from typing import Iterable

import numpy as np


# ---------- packed 3x3 matrices over F2 ----------

def mat_from_mask(x: int) -> np.ndarray:
    return np.array([[(int(x) >> (3 * i + j)) & 1 for j in range(3)] for i in range(3)], dtype=np.uint8)


def mask_from_mat(M: np.ndarray) -> int:
    out = 0
    A = M.astype(np.uint8) & 1
    for i in range(3):
        for j in range(3):
            if int(A[i, j]):
                out |= 1 << (3 * i + j)
    return out


def mat_key(M: np.ndarray) -> int:
    return mask_from_mat(M)


def f2_rank_mat(M: np.ndarray) -> int:
    A = (M.copy().astype(np.uint8) & 1)
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
    A = np.concatenate([M.copy().astype(np.uint8) & 1, np.eye(3, dtype=np.uint8)], axis=1)
    r = 0
    for c in range(3):
        piv = None
        for i in range(r, 3):
            if A[i, c]:
                piv = i
                break
        if piv is None:
            raise ValueError("singular")
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for i in range(3):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        r += 1
    return A[:, 3:]


def mm(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    return (A @ B) & 1


def generate_gl3() -> list[np.ndarray]:
    return [mat_from_mask(x) for x in range(512) if f2_rank_mat(mat_from_mask(x)) == 3]


# ---------- explicit subgroup generators ----------

def I3() -> np.ndarray:
    return np.eye(3, dtype=np.uint8)


def lower_right_swap() -> np.ndarray:
    M = I3()
    M[1, 1] = 0; M[2, 2] = 0; M[1, 2] = 1; M[2, 1] = 1
    return M


def lower_right_shear() -> np.ndarray:
    # embeds [[1,1],[0,1]] in rows/cols 1,2
    M = I3()
    M[1, 2] = 1
    return M


def P_row_stabilizer_generators() -> list[np.ndarray]:
    # Preserve row_0(P)=e0^T.  Lower-left shears plus GL2 on the lower block.
    g10 = I3(); g10[1, 0] = 1
    g20 = I3(); g20[2, 0] = 1
    return [g10, g20, lower_right_swap(), lower_right_shear()]


def Q_col_stabilizer_generators() -> list[np.ndarray]:
    # Preserve col_0(Q)=e0.  Upper-right shears plus GL2 on the lower block.
    g01 = I3(); g01[0, 1] = 1
    g02 = I3(); g02[0, 2] = 1
    return [g01, g02, lower_right_swap(), lower_right_shear()]


def subgroup_closure(generators: list[np.ndarray]) -> list[np.ndarray]:
    gens = [g.astype(np.uint8) & 1 for g in generators]
    gens += [mat_inv(g) for g in gens]
    ident = I3()
    seen = {mat_key(ident): ident}
    q = deque([ident])
    while q:
        A = q.popleft()
        for G in gens:
            for H in (mm(G, A), mm(A, G)):
                k = mat_key(H)
                if k not in seen:
                    seen[k] = H
                    q.append(H)
    return [seen[k] for k in sorted(seen)]


def direct_P_row_stabilizer(gl: list[np.ndarray]) -> list[np.ndarray]:
    e0 = np.array([1, 0, 0], dtype=np.uint8)
    return [G for G in gl if np.array_equal(G[0, :], e0)]


def direct_Q_col_stabilizer(gl: list[np.ndarray]) -> list[np.ndarray]:
    e0 = np.array([1, 0, 0], dtype=np.uint8)
    return [G for G in gl if np.array_equal(G[:, 0], e0)]


# ---------- quotient coordinates ----------

def quotient_mask_from_full_drop_bit0(full: int) -> int:
    q = 0
    k = 0
    for bit in range(9):
        if bit == 0:
            continue
        if (int(full) >> bit) & 1:
            q |= 1 << k
        k += 1
    return q


def full_mask_from_quotient_section(q: int) -> int:
    full = 0
    k = 0
    for bit in range(9):
        if bit == 0:
            continue
        if (int(q) >> k) & 1:
            full |= 1 << bit
        k += 1
    return full


def quotient_project_full(full: int) -> int:
    # Quotient by <E00>: delete bit 0.  No requirement that the representative has bit 0 zero.
    return quotient_mask_from_full_drop_bit0(full)


def apply_A_quotient(q: int, P: np.ndarray, Q: np.ndarray) -> int:
    M = mat_from_mask(full_mask_from_quotient_section(q))
    N = (P.T @ M @ mat_inv(Q).T) & 1
    return quotient_project_full(mask_from_mat(N))


def apply_A_quotient_from_full(full: int, P: np.ndarray, Q: np.ndarray) -> int:
    M = mat_from_mask(full)
    N = (P.T @ M @ mat_inv(Q).T) & 1
    return quotient_project_full(mask_from_mat(N))


def old_complement_action(q: int, P: np.ndarray, Q: np.ndarray) -> int:
    # Previous wrong action: preserved the chosen complement U00=0.
    M = mat_from_mask(full_mask_from_quotient_section(q))
    N = (P.T @ M @ mat_inv(Q).T) & 1
    if int(N[0, 0]) != 0:
        raise ValueError("not complement preserving")
    return quotient_mask_from_full_drop_bit0(mask_from_mat(N))


def perm_for_pair(P: np.ndarray, Q: np.ndarray) -> tuple[int, ...]:
    return tuple([0] + [apply_A_quotient(q, P, Q) for q in range(1, 256)])


def perm_compose(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    # p after q: x -> p[q[x]]
    return tuple(p[q[i]] for i in range(256))


def permutation_closure(generator_perms: list[tuple[int, ...]]) -> set[tuple[int, ...]]:
    ident = tuple(range(256))
    seen = {ident}
    q = deque([ident])
    gens = list(generator_perms)
    # Every generator is involutive or low-order; adding powers is cheap and robust.
    for g in list(generator_perms):
        h = g
        for _ in range(1, 8):
            h = perm_compose(g, h)
            gens.append(h)
            if h == ident:
                break
    while q:
        p = q.popleft()
        for g in gens:
            for h in (perm_compose(g, p), perm_compose(p, g)):
                if h not in seen:
                    seen.add(h)
                    q.append(h)
    return seen


# ---------- tensor preservation ----------

def build_e11_core() -> np.ndarray:
    T = np.zeros((8, 9, 9), dtype=np.uint8)
    # Full T entries are A_{ij}, B_{jk}, C_{ik}.  E11/A00 means omit A bit 0.
    for i in range(3):
        for j in range(3):
            a_full = 3 * i + j
            if a_full == 0:
                continue
            a_core = a_full - 1  # bit0 removed; for E11 all later bits shift by one
            for k in range(3):
                b = 3 * j + k
                c = 3 * i + k
                T[a_core, b, c] = 1
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


def transform_core_by_pair(core: np.ndarray, P: np.ndarray, Q: np.ndarray) -> np.ndarray:
    out = np.zeros_like(core)
    for a in range(core.shape[0]):
        q = 1 << a
        q2 = apply_A_quotient(q, P, Q)
        for b in range(core.shape[1]):
            vb = 1 << b
            v2 = apply_B(vb, Q)
            for c in range(core.shape[2]):
                if int(core[a, b, c]):
                    w2 = apply_W(1 << c, P)
                    add_outer(out, q2, v2, w2)
    return out


# ---------- orbit utilities ----------

def orbit_partition(perms: Iterable[tuple[int, ...]]) -> tuple[list[dict], dict[int, int]]:
    perms = list(perms)
    unseen = set(range(1, 256))
    orbits = []
    point_orbit = {}
    while unseen:
        seed = min(unseen)
        orb = {seed}
        frontier = [seed]
        while frontier:
            x = frontier.pop()
            for p in perms:
                y = p[x]
                if y not in orb:
                    orb.add(y)
                    frontier.append(y)
        idx = len(orbits)
        for x in orb:
            point_orbit[x] = idx
        unseen -= orb
        orbits.append(orbit_record(idx, seed, orb))
    return orbits, point_orbit


def orbit_record(idx: int, seed: int, orb: set[int]) -> dict:
    sigs = Counter(A_point_signature(q) for q in orb)
    ranks = Counter(sig[0] for sig in sigs for _ in range(sigs[sig]))
    weights = Counter(int(q).bit_count() for q in orb)
    reps = sorted(orb, key=lambda z: (z.bit_count(), z))[:20]
    return {
        "orbit": idx,
        "seed": seed,
        "size": len(orb),
        "reps": reps,
        "rank_counts": {str(k): v for k, v in sorted(ranks.items())},
        "signature_counts": {str(k): v for k, v in sorted(sigs.items())},
        "weight_counts": {str(k): v for k, v in sorted(weights.items())},
    }


def A_point_signature(q: int) -> tuple[int, int, int, int]:
    # Descriptors of the chosen U00=0 section representative: section rank, row0-tail
    # nonzero flag, col0-tail nonzero flag, and Hamming weight.  These need not be
    # constant on quotient orbits; they are recorded only to interpret the partition.
    M = mat_from_mask(full_mask_from_quotient_section(q))
    row0_tail = int(M[0, 1]) + 2 * int(M[0, 2])
    col0_tail = int(M[1, 0]) + 2 * int(M[2, 0])
    return (f2_rank_mat(M), 1 if row0_tail else 0, 1 if col0_tail else 0, int(q).bit_count())


def canonical_multiset(ms: Iterable[int], perms: Iterable[tuple[int, ...]]) -> tuple[int, ...]:
    base = tuple(sorted(int(x) for x in ms))
    best = base
    for p in perms:
        img = tuple(sorted(p[x] for x in base))
        if img < best:
            best = img
    return best


# ---------- main ----------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=Path("data/e11_quotient_action/e11_quotient_action_verification.json"))
    ap.add_argument("--save-perms", action="store_true")
    args = ap.parse_args()

    t0 = time.time()
    gl = generate_gl3()
    P_direct = direct_P_row_stabilizer(gl)
    Q_direct = direct_Q_col_stabilizer(gl)
    P_gen = subgroup_closure(P_row_stabilizer_generators())
    Q_gen = subgroup_closure(Q_col_stabilizer_generators())
    P_direct_keys = {mat_key(M) for M in P_direct}
    Q_direct_keys = {mat_key(M) for M in Q_direct}
    P_gen_keys = {mat_key(M) for M in P_gen}
    Q_gen_keys = {mat_key(M) for M in Q_gen}

    # Generating permutations: direct product generated by (P-generator,I) and (I,Q-generator).
    I = I3()
    gen_perms = [perm_for_pair(P, I) for P in P_row_stabilizer_generators()] + [perm_for_pair(I, Q) for Q in Q_col_stabilizer_generators()]
    perm_closure = permutation_closure(gen_perms)
    explicit_pair_perms = {perm_for_pair(P, Q) for P in P_direct for Q in Q_direct}

    # Basic permutation and quotient well-definedness checks.
    perm_bijections_ok = all(p[0] == 0 and set(p[1:]) == set(range(1, 256)) for p in explicit_pair_perms)
    well_defined_failures = []
    for P in P_direct:
        for Q in Q_direct:
            for q in range(256):
                full = full_mask_from_quotient_section(q)
                a = apply_A_quotient_from_full(full, P, Q)
                b = apply_A_quotient_from_full(full ^ 1, P, Q)
                if a != b:
                    well_defined_failures.append({"q": q, "P": mat_key(P), "Q": mat_key(Q), "image0": a, "image1": b})
                    break
            if well_defined_failures:
                break
        if well_defined_failures:
            break

    # Tensor preservation: all 576 pairs with R=I should preserve the E11 core tensor.
    core = build_e11_core()
    tensor_failures = []
    for P in P_direct:
        for Q in Q_direct:
            image = transform_core_by_pair(core, P, Q)
            if not np.array_equal(image, core):
                tensor_failures.append({"P": mat_key(P), "Q": mat_key(Q), "diff_count": int(np.sum(image ^ core))})
                if len(tensor_failures) >= 5:
                    break
        if len(tensor_failures) >= 5:
            break

    orbits, point_orbit = orbit_partition(explicit_pair_perms)
    orbit_sizes = sorted(o["size"] for o in orbits)

    # Old complement-preserving action for comparison only.
    e0 = np.array([1, 0, 0], dtype=np.uint8)
    P_old = [P for P in gl if np.array_equal(P[:, 0], e0)]
    Q_old = [Q for Q in gl if np.array_equal(mat_inv(Q).T[:, 0], e0)]
    old_perms = []
    old_bad = 0
    for P in P_old:
        for Q in Q_old:
            try:
                old_perms.append(tuple([0] + [old_complement_action(q, P, Q) for q in range(1, 256)]))
            except ValueError:
                old_bad += 1
    old_orbits, _ = orbit_partition(set(old_perms)) if old_perms else ([], {})

    result = {
        "purpose": "Resolve E11 quotient-action orbit partition and validate the common group action before orbit compression of A-multisets.",
        "field": "F2",
        "correct_action": "A quotient factors transform by q = [U] -> [P^T U Q^{-T}] modulo <E00>, with row0(P)=e0^T and col0(Q)=e0.",
        "subgroup_generation": {
            "GL3_size": len(gl),
            "P_row_stabilizer_direct_size": len(P_direct),
            "P_row_stabilizer_generator_closure_size": len(P_gen),
            "P_generator_closure_equals_direct": P_gen_keys == P_direct_keys,
            "Q_col_stabilizer_direct_size": len(Q_direct),
            "Q_col_stabilizer_generator_closure_size": len(Q_gen),
            "Q_generator_closure_equals_direct": Q_gen_keys == Q_direct_keys,
            "P_generators_keys": [mat_key(g) for g in P_row_stabilizer_generators()],
            "Q_generators_keys": [mat_key(g) for g in Q_col_stabilizer_generators()],
        },
        "quotient_action_checks": {
            "explicit_pair_count": len(P_direct) * len(Q_direct),
            "distinct_explicit_pair_permutations": len(explicit_pair_perms),
            "permutation_closure_from_explicit_generators_size": len(perm_closure),
            "generator_closure_equals_explicit_pairs": perm_closure == explicit_pair_perms,
            "all_explicit_perms_bijective_on_nonzero_points": perm_bijections_ok,
            "well_defined_mod_E00": len(well_defined_failures) == 0,
            "well_defined_failures_head": well_defined_failures[:5],
        },
        "tensor_preservation": {
            "core_shape": list(core.shape),
            "core_nnz": int(core.sum()),
            "tested_pairs_with_R_identity": len(P_direct) * len(Q_direct),
            "all_preserve_E11_core_tensor": len(tensor_failures) == 0,
            "failures_head": tensor_failures,
        },
        "point_orbits": {
            "num_orbits": len(orbits),
            "sizes_sorted": orbit_sizes,
            "matches_expected_sizes_3_3_9_36_36_36_36_96": orbit_sizes == [3, 3, 9, 36, 36, 36, 36, 96],
            "orbits": orbits,
        },
        "old_complement_action_for_comparison_only": {
            "description": "This is the previously used complement-preserving action P[:,0]=e0 and Q^{-T}[:,0]=e0; it acts on the chosen section U00=0 rather than on A/<E00> and should not be used for E11 quotient orbit compression.",
            "P_old_size": len(P_old),
            "Q_old_size": len(Q_old),
            "distinct_old_perms": len(set(old_perms)),
            "old_bad_pairs": old_bad,
            "old_orbit_sizes_sorted": sorted(o["size"] for o in old_orbits),
            "old_orbits": old_orbits,
        },
        "elapsed_sec": time.time() - t0,
    }

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "P_direct": len(P_direct),
        "Q_direct": len(Q_direct),
        "perm_closure": len(perm_closure),
        "explicit_perms": len(explicit_pair_perms),
        "well_defined": result["quotient_action_checks"]["well_defined_mod_E00"],
        "tensor_preservation": result["tensor_preservation"]["all_preserve_E11_core_tensor"],
        "orbit_sizes_sorted": orbit_sizes,
        "matches_expected": result["point_orbits"]["matches_expected_sizes_3_3_9_36_36_36_36_96"],
        "old_orbit_sizes_sorted": result["old_complement_action_for_comparison_only"]["old_orbit_sizes_sorted"],
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True))
    print(f"wrote {args.out}")

    if args.save_perms:
        import hashlib
        perm_path = args.out.with_suffix(".perms.npz")
        arr=np.array([list(p) for p in sorted(explicit_pair_perms)], dtype=np.uint16)
        np.savez_compressed(perm_path, perms=arr)
        digest=hashlib.sha256(arr.tobytes()).hexdigest()
        print(f"saved permutations {perm_path} shape={arr.shape} dtype={arr.dtype} sha256_raw={digest}")

    # Fail fast if the mathematical checks fail.
    assert P_gen_keys == P_direct_keys
    assert Q_gen_keys == Q_direct_keys
    assert perm_closure == explicit_pair_perms
    assert perm_bijections_ok
    assert not well_defined_failures
    assert not tensor_failures
    assert orbit_sizes == [3, 3, 9, 36, 36, 36, 36, 96]


if __name__ == "__main__":
    main()
