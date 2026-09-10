#!/usr/bin/env python3
"""
analysis: Compute the F2 orbit quotient span and check if q(T333) is reachable.

The Sym³ split says: in the 84-dim quotient E_inv / Sym³,
  - cubes contribute 0
  - each orbit contributes one vector
  - T333 maps to q(T333) ≠ 0 (HW = 8)

If the span of all orbit quotient images has dimension < 84 and q(T333)
is outside, then NO cyclic-invariant F2 decomposition of T333 exists at
ANY skeleton.  This would be a complete algebraic obstruction.

Even if the span is full, we learn the dimension and can build
a basis for more targeted searches.
"""

import json, time
import numpy as np
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
DATA_DIR = WS / 'data' / 'cyclic_sat'


def build_T333():
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for a in range(3):
        for b in range(3):
            for c in range(3):
                T[3*a+b, 3*b+c, 3*c+a] = 1
    return T


def compute_orbits_and_pairs():
    """Compute cyclic orbit structure and Sym³ quotient pairs."""
    seen = set()
    fixed, two_eq, all_diff = [], [], []
    for i in range(9):
        for j in range(9):
            for k in range(9):
                if (i, j, k) not in seen:
                    orb = set()
                    t = (i, j, k)
                    while t not in orb:
                        orb.add(t)
                        t = (t[1], t[2], t[0])
                    rep = min(orb)
                    seen |= orb
                    if rep[0] == rep[1] == rep[2]:
                        fixed.append(rep)
                    elif len({rep[0], rep[1], rep[2]}) < 3:
                        two_eq.append(rep)
                    else:
                        all_diff.append(rep)

    # Transpose pairs of all-different orbits
    seen_pairs = set()
    pairs = []
    for rep in all_diff:
        i, j, k = rep
        t_rep = min([(j, i, k), (i, k, j), (k, j, i)])
        pair = (min(rep, t_rep), max(rep, t_rep))
        if pair not in seen_pairs:
            seen_pairs.add(pair)
            pairs.append(pair)

    return fixed, two_eq, all_diff, pairs


def orbit_quotient_image(U, V, W, pairs):
    """Compute the 84-bit quotient image of orbit (U,V,W)."""
    q = np.zeros(len(pairs), dtype=np.uint8)
    for idx, (a, b) in enumerate(pairs):
        va = (U[a[0]]*V[a[1]]*W[a[2]] +
              V[a[0]]*W[a[1]]*U[a[2]] +
              W[a[0]]*U[a[1]]*V[a[2]]) % 2
        vb = (U[b[0]]*V[b[1]]*W[b[2]] +
              V[b[0]]*W[b[1]]*U[b[2]] +
              W[b[0]]*U[b[1]]*V[b[2]]) % 2
        q[idx] = va ^ vb
    return q


class F2RowEchelon:
    """Incremental row echelon form over F2."""

    def __init__(self, n):
        self.n = n
        self.basis = []
        self.pivots = []

    @property
    def rank(self):
        return len(self.basis)

    def try_add(self, v):
        """Try to add v; return True if rank increased."""
        w = v.copy()
        for row, p in zip(self.basis, self.pivots):
            if w[p]:
                w ^= row
        # Find first nonzero
        nz = np.nonzero(w)[0]
        if len(nz) == 0:
            return False
        self.basis.append(w)
        self.pivots.append(nz[0])
        return True

    def contains(self, v):
        """Check if v is in the row space."""
        w = v.copy()
        for row, p in zip(self.basis, self.pivots):
            if w[p]:
                w ^= row
        return np.all(w == 0)


def main():
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    T333 = build_T333()
    fixed, two_eq, all_diff, pairs = compute_orbits_and_pairs()

    print(f"Orbits: {len(fixed)} fixed, {len(two_eq)} two-equal, "
          f"{len(all_diff)} all-different")
    print(f"Transpose pairs: {len(pairs)}")

    # q(T333)
    q_T333 = np.array([T333[a[0], a[1], a[2]] ^ T333[b[0], b[1], b[2]]
                        for a, b in pairs], dtype=np.uint8)
    print(f"q(T333): HW={q_T333.sum()}, nonzero at {np.nonzero(q_T333)[0].tolist()}")

    # Phase 1: exhaustive enumeration of all 2^27 orbit quotient images
    print(f"\nEnumerating all 2^27 = {2**27} orbit quotient images...")
    t0 = time.time()

    re = F2RowEchelon(84)
    n_nonzero = 0
    n_unique_images = 0
    image_set = set()  # store as tuples for membership testing

    # Enumerate all (U,V,W) in F_2^{27}
    # For efficiency, iterate over packed integers
    for uv_int in range(2**27):
        # Unpack: U = bits 0-8, V = bits 9-17, W = bits 18-26
        U = np.array([(uv_int >> i) & 1 for i in range(9)], dtype=np.uint8)
        V = np.array([(uv_int >> (9 + i)) & 1 for i in range(9)], dtype=np.uint8)
        W = np.array([(uv_int >> (18 + i)) & 1 for i in range(9)], dtype=np.uint8)

        q_img = orbit_quotient_image(U, V, W, pairs)

        if np.any(q_img):
            n_nonzero += 1
            key = tuple(q_img)
            if key not in image_set:
                image_set.add(key)
                n_unique_images += 1
                re.try_add(q_img)

        # Progress
        if uv_int % (2**24) == 0 and uv_int > 0:
            elapsed = time.time() - t0
            pct = uv_int / 2**27 * 100
            print(f"  {pct:.0f}% ({uv_int}/{2**27}), "
                  f"rank={re.rank}, unique={n_unique_images}, "
                  f"elapsed={elapsed:.1f}s")
            if re.rank == 84:
                print("  -> Full rank reached, continuing for statistics...")

    elapsed = time.time() - t0
    print(f"\nDone in {elapsed:.1f}s")
    print(f"Nonzero images: {n_nonzero}/{2**27}")
    print(f"Unique quotient images: {n_unique_images}")
    print(f"Quotient image span rank: {re.rank}/84")

    # Check if q(T333) is in the span
    in_span = re.contains(q_T333)
    print(f"q(T333) in orbit quotient span: {in_span}")

    if not in_span:
        print("\n*** ALGEBRAIC OBSTRUCTION: q(T333) is NOT in the span ***")
        print("*** of orbit quotient images. No cyclic-invariant F2  ***")
        print("*** decomposition of T333 exists at ANY skeleton!      ***")
    else:
        print("\nq(T333) is reachable in the quotient. No obstruction from span alone.")
        print("Minimum orbit count for quotient reachability: see further analysis.")

    # Also check: what's the minimum number of orbits needed?
    # Use greedy: can q(T333) be reached with 1 orbit?
    single_match = q_T333_tuple = tuple(q_T333)
    if single_match in image_set:
        print("q(T333) is achievable with 1 orbit!")
    else:
        print("q(T333) NOT achievable with 1 orbit. Checking 2...")
        # For 2 orbits: q(T333) = img_1 XOR img_2, so img_2 = q(T333) XOR img_1
        found_2 = False
        for img in image_set:
            needed = tuple(q_T333 ^ np.array(img, dtype=np.uint8))
            if needed in image_set:
                found_2 = True
                break
        if found_2:
            print("q(T333) is achievable with 2 orbits!")
        else:
            print("q(T333) NOT achievable with 2 orbits.")

    result = {
        'quotient_dim': len(pairs),
        'total_orbit_triples': 2**27,
        'nonzero_images': n_nonzero,
        'unique_quotient_images': n_unique_images,
        'span_rank': re.rank,
        'q_T333_hw': int(q_T333.sum()),
        'q_T333_in_span': bool(in_span),
        'elapsed_sec': round(elapsed, 2),
    }

    out = DATA_DIR / 'quotient_span_analysis.json'
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(f"\nSaved: {out}")


if __name__ == '__main__':
    main()
