#!/usr/bin/env python3
"""Verify AG(3,2) plane-counting for the coset argument.

In AG(3,2) = F_2^3 \ {0} with 7 points, the affine planes are 3-element
subsets that form cosets of 1-dimensional subspaces.

Key claims to verify:
1. AG(3,2) has exactly 14 affine planes (= 7 linear planes + 7 translated).
   Actually: affine planes in AG(3,2) are sets {a, b, a+b} where a,b,a+b
   are all nonzero. There are C(7,2) = 21 pairs, but a+b might be 0 (only
   if a=b, impossible). So there are 21 pairs, each determining one plane;
   but each plane is determined by C(3,2) = 3 pairs, so 21/3 = 7 planes...
   Wait, let me count properly.

   The affine planes are the 2-dimensional affine subspaces of F_2^3 \ {0}.
   A 2-dim affine subspace is a coset of a 2-dim linear subspace.
   F_2^3 has 7 two-dimensional linear subspaces. Each 2-dim subspace V has
   3 nonzero elements, and 2 nontrivial cosets V+a (a not in V), but
   V+a has 4 elements, of which some might be 0.

   Actually in AG(3,2) the "planes" relevant to the coset argument are
   3-element subsets {a,b,c} with a+b+c = 0 (i.e., c = a+b).
   Number: C(7,2)/1 but divided by 3 since each triple {a,b,a+b} is
   counted 3 times as pairs... No.
   
   Actually: for each pair {a,b} with a,b nonzero and a != b,
   c = a+b is also nonzero (since a != b), giving triple {a,b,a+b}.
   C(7,2) = 21 such pairs. Each triple is counted C(3,2) = 3 times.
   So 21/3 = 7 triples... but the coset_exact_table_v3.json says 14 planes!

   The discrepancy: the coset has 8 points (including 0 = first-row zero),
   not 7. The affine planes IN THE COSET include planes that use the
   point at first-row = 0. Let me check: in the normalized column coset
   p + e_1 * F_2^3, the first-row labels run over all of F_2^3 including 0.
   The coset has 8 elements. The relevant "planes" for the AG argument are
   4-element subsets forming 2-dim affine subspaces of F_2^3 (since first-row
   labels are 3-bit vectors).

   Hmm, let me recount from the data: the coset_exact_table says
   ag3_plane_count_by_subset_size shows that 4-subsets have 0 or 1 planes,
   5-subsets have exactly 1 plane, etc. And there are 14 planes total.
   
   This matches AG(2, F_2) = the 2-dim affine geometry over F_2 in 3D space.
   Number of 2-dim affine subspaces of F_2^3:
   = number of 2-dim linear subspaces + their nontrivial cosets.
   There are 7 linear 2-dim subspaces (each is the kernel of a nonzero
   linear form). Each has 1 nontrivial coset (F_2^3 / V has order 2).
   So 7 * 2 = 14 affine planes. Each plane has |V| = 4 elements.
   
   But we're working in F_2^3 \ {0}, so planes that contain 0 lose one
   element and become 3-element sets. The 7 LINEAR planes each contain 0,
   giving 7 three-element planes in AG(3,2). The 7 COSET planes don't
   contain 0, staying as 4-element planes.

   For the cap argument: we need |H ∩ plane| <= 3 for 3-element planes
   (from dim-3 LB = 17, cap = 20-17 = 3) and |H ∩ plane'| <= ??? for
   4-element coset planes.

   Actually the "planes" in the proof are DIM-3 A-SUBSPACES, not just
   first-row coordinate planes. Each dim-3 subspace of the dim-4 coset
   span S corresponds to a 3-element or 4-element subset depending on
   whether it contains the "base point" p.

   Let me just verify the data directly.

This script directly verifies the plane-counting claims using the coset data.
"""
from __future__ import annotations
import json, sys, time, itertools
from pathlib import Path

OUT = Path("data/audit/ag32_planes.json")


def main():
    t0 = time.time()

    # The 7 nonzero elements of F_2^3
    pts = list(range(1, 8))

    # "Affine planes" in F_2^3 \ {0}: 3-element subsets {a,b,c} with a+b+c=0
    planes_3 = []
    for triple in itertools.combinations(pts, 3):
        a, b, c = triple
        if a ^ b ^ c == 0:
            planes_3.append(set(triple))

    print(f"3-element affine planes in F_2^3\\0: {len(planes_3)}")
    for p in sorted(planes_3, key=lambda s: sorted(s)):
        print(f"  {sorted(p)}")

    # Check: every k-subset for k=4,5,6,7 contains at least one plane
    plane_counts = {}
    for k in range(1, 8):
        counts = {}
        for subset in itertools.combinations(pts, k):
            s = set(subset)
            n_planes = sum(1 for p in planes_3 if p <= s)
            counts[n_planes] = counts.get(n_planes, 0) + 1
        plane_counts[k] = counts
        print(f"k={k}: plane count distribution = {dict(sorted(counts.items()))}")

    # Key claims:
    # - Every 5-subset contains at least one plane
    every_5_has_plane = all(n >= 1 for n in plane_counts[5].keys())
    # - Every 4-subset has 0 or 1 planes
    every_4_max_1 = all(n <= 1 for n in plane_counts[4].keys())
    # - Exactly 14 4-subsets contain a plane (= 2 * 7)
    n_4_with_plane = plane_counts[4].get(1, 0)

    # Now verify the key consequence: with cap 3 per plane,
    # no 5-subset is plane-free, so |H| <= 4.
    # And with |H| >= 4 from flattening, exactly |H| = 4.

    # Also verify: among the 8 elements of the full coset (including first-row=0),
    # the rank-3 elements form a plane?
    # In the rank-2 lower block coset: rank-2 are first-row labels r with r1=0 (4 elements),
    # rank-3 are r with r1=1 (4 elements). The rank-3 labels are {1,3,5,7}.
    rank3_labels = {1, 3, 5, 7}
    # Check if {1,3,5,7} contains a plane:
    rank3_planes = [p for p in planes_3 if p <= rank3_labels]
    print(f"\nRank-3 labels {sorted(rank3_labels)}: contains {len(rank3_planes)} planes")
    for p in rank3_planes:
        print(f"  {sorted(p)}: {sorted(p)[0]}^{sorted(p)[1]}^{sorted(p)[2]} = {sorted(p)[0] ^ sorted(p)[1] ^ sorted(p)[2]}")

    # Consequence: |H ∩ rank3_labels| <= 3 (no plane), so at most 3 rank-3 elements.
    # Combined with |H| = 4: exactly 1 rank-2 and 3 rank-3.

    # Also check: which 4-element subsets of {1..7} contain NO plane?
    no_plane_4 = [sorted(s) for s in itertools.combinations(pts, 4)
                  if not any(p <= set(s) for p in planes_3)]
    print(f"\n4-element subsets with no plane: {len(no_plane_4)}")
    for s in no_plane_4:
        # Check how many rank-3 (labels with bit 0 set) elements
        r3 = sum(1 for x in s if x & 1)
        print(f"  {s}: rank3_count={r3}")

    elapsed = time.time() - t0
    rec = {
        "schema": "ag32_planes_v1",
        "n_3_planes": len(planes_3),
        "planes": [sorted(p) for p in planes_3],
        "plane_counts_by_subset_size": {str(k): v for k, v in plane_counts.items()},
        "every_5_subset_has_plane": every_5_has_plane,
        "rank3_labels_contain_plane": len(rank3_planes) > 0,
        "no_plane_4_subsets": no_plane_4,
        "no_plane_4_count": len(no_plane_4),
        "elapsed_sec": elapsed,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: v for k, v in rec.items() if k != "planes" and k != "no_plane_4_subsets"}, indent=2))


if __name__ == "__main__":
    main()
