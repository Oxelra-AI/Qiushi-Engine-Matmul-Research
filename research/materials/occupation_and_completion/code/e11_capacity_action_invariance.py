#!/usr/bin/env python3
"""Check that corrected E11 quotient action preserves Wang occupation capacities.

This verifies compatibility between the 576 quotient permutations used for
A-multiset canonicalization and the complete E11 occupation cache derived from
Wang's full T-level lower-bound LUT.  It is not needed for fixed-U SAT invariance
(which follows from core-tensor preservation), but it checks that the occupation
search surface itself respects the same action.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path

SCRIPTS_A01 = Path("scripts")
SCRIPTS_A02 = Path("scripts")
for P in (SCRIPTS_A01, SCRIPTS_A02):
    if str(P) not in sys.path:
        sys.path.insert(0, str(P))

from wang_capacity_lazy import unpack_basis, pack_basis, rref_basis  # noqa: E402
from e11_quotient_action_verify import (  # noqa: E402
    I3, P_row_stabilizer_generators, Q_col_stabilizer_generators, perm_for_pair
)


def transform_key8(key: int, perm: tuple[int, ...]) -> int:
    rows = unpack_basis(key)
    return pack_basis(rref_basis([perm[r] for r in rows], n=8))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cache", type=Path, default=Path("data/e11_capacity_sat/e11_capacity_cache.pkl"))
    ap.add_argument("--out", type=Path, default=Path("data/e11_quotient_action/e11_capacity_action_invariance.json"))
    ap.add_argument("--all-perms", type=Path, default=Path("data/e11_quotient_action/e11_quotient_action_verification.perms.npz"))
    ap.add_argument("--check-all-perms", action="store_true")
    args = ap.parse_args()
    t0 = time.time()
    cache = pickle.load(args.cache.open("rb"))
    key_to_pos = {int(k): i for i, k in enumerate(cache["keys8"])}

    I = I3()
    gen_perms = [perm_for_pair(P, I) for P in P_row_stabilizer_generators()] + [perm_for_pair(I, Q) for Q in Q_col_stabilizer_generators()]
    perms = gen_perms
    perm_source = "8 explicit subgroup generator permutations"
    if args.check_all_perms:
        import numpy as np
        arr = np.load(args.all_perms)["perms"]
        perms = [tuple(int(x) for x in row.tolist()) for row in arr]
        perm_source = "all 576 saved quotient permutations"

    failures = []
    checked = 0
    dim_move_counter = Counter()
    for pi, perm in enumerate(perms):
        for idx, key in enumerate(cache["keys8"]):
            img_key = transform_key8(int(key), perm)
            j = key_to_pos.get(img_key)
            if j is None:
                failures.append({"perm_index": pi, "key8": int(key), "image_key8": int(img_key), "failure": "image key missing"})
                break
            if cache["caps"][idx] != cache["caps"][j] or cache["Ls"][idx] != cache["Ls"][j]:
                failures.append({
                    "perm_index": pi,
                    "key8": int(key),
                    "image_key8": int(img_key),
                    "dim8": int(cache["dims"][idx]),
                    "image_dim8": int(cache["dims"][j]),
                    "cap": int(cache["caps"][idx]),
                    "image_cap": int(cache["caps"][j]),
                    "L": int(cache["Ls"][idx]),
                    "image_L": int(cache["Ls"][j]),
                })
                break
            dim_move_counter[(int(cache["dims"][idx]), int(cache["dims"][j]))] += 1
            checked += 1
        if failures:
            break
        print(f"checked perm {pi+1}/{len(perms)}")

    # Singleton cap constancy by correct point orbit using all saved perms.
    singleton_caps = {}
    for i, (key, dim) in enumerate(zip(cache["keys8"], cache["dims"])):
        if int(dim) == 1:
            row = unpack_basis(int(key))[0]
            singleton_caps[row] = int(cache["caps"][i])
    import numpy as np
    all_arr = np.load(args.all_perms)["perms"]
    unseen = set(range(1, 256))
    point_orbit_caps = []
    while unseen:
        seed = min(unseen)
        orb = {int(row[seed]) for row in all_arr}
        # close in case sorted rows do not enumerate action in composition order; one pass under a group is enough.
        unseen -= orb
        point_orbit_caps.append({"seed": seed, "size": len(orb), "caps": dict(Counter(singleton_caps[x] for x in orb)), "points": sorted(orb)})

    result = {
        "purpose": "Verify Wang occupation cache invariance under the corrected E11 quotient action used for orbit compression.",
        "cache": str(args.cache),
        "perm_source": perm_source,
        "permutations_checked": len(perms),
        "subspaces_per_permutation": len(cache["keys8"]),
        "total_subspace_images_checked": checked,
        "all_checked_cap_and_L_preserved": len(failures) == 0,
        "failures_head": failures[:10],
        "dim_move_counter": {str(k): v for k, v in dim_move_counter.items()},
        "point_orbit_cap_counts": point_orbit_caps,
        "elapsed_sec": time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "perms_checked": len(perms),
        "total_images_checked": checked,
        "ok": result["all_checked_cap_and_L_preserved"],
        "point_orbit_cap_counts": [{"size": r["size"], "caps": r["caps"]} for r in point_orbit_caps],
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True))
    print(f"wrote {args.out}")
    if failures:
        raise SystemExit("capacity action invariance failed")


if __name__ == "__main__":
    main()
