#!/usr/bin/env python3
"""Verify the AG(3,2) cap theorem for the coset argument.

In the 8-element coset (F_2^3 in first-row coordinates), the relevant
"planes" for the Wang constraint are 4-element 2-dimensional affine
subspaces {a, a+v, a+w, a+v+w}.

Key claim: every 5-element subset of F_2^3 contains a 4-element affine plane.
Equivalently, the cap number of AG(3,2) (maximum set with no 4-element plane) is 4.

This means |H| <= 4 in the coset argument.
"""
from __future__ import annotations
import json, itertools, time
from pathlib import Path

OUT = Path("data/audit/ag32_cap.json")


def main():
    t0 = time.time()

    # F_2^3 = {0, 1, 2, 3, 4, 5, 6, 7} using standard binary representation
    pts = list(range(8))

    # Enumerate all 4-element 2-dimensional affine subspaces of F_2^3
    planes_4 = []
    for a in pts:
        for v in range(1, 8):
            for w in range(v + 1, 8):
                # Check v, w linearly independent over F_2
                if v ^ w == 0:
                    continue
                plane = frozenset({a, a ^ v, a ^ w, a ^ v ^ w})
                if len(plane) == 4 and all(0 <= p <= 7 for p in plane):
                    planes_4.append(plane)

    # Remove duplicates
    planes_4 = list(set(planes_4))
    print(f"4-element affine planes in F_2^3: {len(planes_4)}")
    for p in sorted(planes_4, key=lambda s: sorted(s)):
        print(f"  {sorted(p)}")

    # Check cap theorem: for each subset size k, count how many k-subsets
    # contain NO 4-element plane
    cap_free = {}
    for k in range(1, 9):
        no_plane_count = 0
        total = 0
        no_plane_examples = []
        for subset in itertools.combinations(pts, k):
            s = frozenset(subset)
            total += 1
            contains_plane = any(p <= s for p in planes_4)
            if not contains_plane:
                no_plane_count += 1
                if len(no_plane_examples) < 10:
                    no_plane_examples.append(sorted(subset))
        cap_free[k] = {
            "total": total,
            "plane_free": no_plane_count,
            "has_plane": total - no_plane_count,
            "examples": no_plane_examples if no_plane_examples else None,
        }
        print(f"k={k}: total={total}, plane-free={no_plane_count}, has_plane={total - no_plane_count}")
        if no_plane_examples and k <= 5:
            for ex in no_plane_examples[:3]:
                print(f"    example: {ex}")

    # The cap number is the largest k with plane-free subsets
    cap_number = max(k for k, v in cap_free.items() if v["plane_free"] > 0)
    every_5_has_plane = cap_free.get(5, {}).get("plane_free", 0) == 0

    print(f"\nCap number of AG(3,2): {cap_number}")
    print(f"Every 5-element subset contains a 4-element plane: {every_5_has_plane}")

    # Verify: the plane-free 4-subsets -- are they exactly the "no-plane" configurations?
    print(f"\nPlane-free 4-element subsets: {cap_free[4]['plane_free']}")
    for ex in (cap_free[4].get("examples") or []):
        # Check rank pattern in the coset
        rank_2_labels = {0, 2, 4, 6}  # first-row bit 0 = 0 -> rank 2
        rank_3_labels = {1, 3, 5, 7}  # first-row bit 0 = 1 -> rank 3
        r2 = sum(1 for x in ex if x in rank_2_labels)
        r3 = sum(1 for x in ex if x in rank_3_labels)
        print(f"  {ex}: r2={r2}, r3={r3}")

    elapsed = time.time() - t0
    rec = {
        "schema": "ag32_cap_v1",
        "n_4_planes": len(planes_4),
        "cap_number": cap_number,
        "every_5_has_plane": every_5_has_plane,
        "cap_free_by_k": cap_free,
        "elapsed_sec": elapsed,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "n_4_planes": rec["n_4_planes"],
        "cap_number": rec["cap_number"],
        "every_5_has_plane": rec["every_5_has_plane"],
    }, indent=2))


if __name__ == "__main__":
    main()
