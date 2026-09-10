#!/usr/bin/env python3
r"""
analysis: bounded near-seed search in the canonical F_2 rank-one-span quotient.

This is a search for a 13-dimensional quotient subspace H < E/L such that the
rank-one matrices with quotient in H span Q^{-1}(H), i.e. qrank=13, xspan=22,
and hidden L-intersection dimension 9.  It does NOT prove nonexistence if it
fails.

Search neighborhoods tested:
  1. hyperplanes inside each rank-23 seed quotient H14 (already exact in the
     oracle file, repeated here only to extract basis states);
  2. one-ARTIFACT swaps from the best seed hyperplanes: replace one basis vector by
     a random rank-one quotient point outside the span of the remaining 12;
  3. random codimension-2 cores K < H14 extended by one random outside rank-one
     quotient point.

The target is constructional: find an F_2 rank-22 witness, or learn whether the
known rank-23 seed neighborhoods contain any canonical span candidate.
"""
from __future__ import annotations

import argparse
import json
import random
import time
from pathlib import Path
from typing import Dict, List, Tuple

import f2_span_oracle as o


def span_values(basis: List[int]) -> List[int]:
    vals = [0]
    for q in basis:
        vals += [v ^ q for v in vals]
    return vals


def canonical_basis(vecs: List[int], target: int = 13) -> List[int] | None:
    inds = o.select_independent_indices(vecs, target)
    if len(inds) < target:
        return None
    return [vecs[i] for i in inds[:target]]


def hyperplane_basis(q_basis14: List[int], f: int) -> List[int]:
    assert len(q_basis14) == 14 and f != 0
    j = (f & -f).bit_length() - 1
    hb = []
    for k in range(14):
        if k == j:
            continue
        coord = 1 << k
        if (f >> k) & 1:
            coord ^= 1 << j
        # convert coord to q vector
        q = 0
        for i in range(14):
            if (coord >> i) & 1:
                q ^= q_basis14[i]
        hb.append(q)
    assert o.gf2_rank(hb) == 13
    return hb


def random_subspace_basis_inside(q_basis: List[int], dim: int, rng: random.Random) -> List[int]:
    # Random linear combinations, then reduce to requested dimension.
    vals = span_values(q_basis)
    while True:
        cand = [rng.choice(vals[1:]) for _ in range(dim * 3)]
        inds = o.select_independent_indices(cand, dim)
        if len(inds) == dim:
            return [cand[i] for i in inds]


def eval_H(q_basis13: List[int], q_to_x: Dict[int, List[int]]) -> Dict:
    vals = span_values(q_basis13)
    xs: List[int] = []
    qs: List[int] = []
    for q in vals:
        hit = q_to_x.get(q)
        if hit:
            # quotient injection was verified, but keep loop for safety
            for x in hit:
                qs.append(q); xs.append(x)
    qrank = o.gf2_rank(qs)
    xrank = o.gf2_rank(xs)
    return {"rankone_count": len(xs), "qrank": qrank, "xspan_rank": xrank, "l_intersection_dim": xrank - qrank}


def better_key(rec: Dict) -> Tuple[int, int, int, int]:
    # Prioritize actual target proximity: xspan, then L hidden rank, then qrank/count.
    return (rec["xspan_rank"], rec["l_intersection_dim"], rec["qrank"], rec["rankone_count"])


def seed_qbasis(qmm_path: Path, qrows: List[int]) -> List[int]:
    xs, _, _ = o.load_qmm_uv_ints(qmm_path)
    qs = [o.q_of_x(x, qrows) for x in xs]
    inds = o.select_independent_indices(qs, 14)
    assert len(inds) == 14
    return [qs[i] for i in inds]


def search_seed(name: str, qmm_path: Path, qrows: List[int], q_to_x: Dict[int, List[int]], rank_one_qs: List[int], rng: random.Random, swaps: int, core_ext: int) -> Dict:
    q14 = seed_qbasis(qmm_path, qrows)
    # Exact hyperplane scan with bases retained.
    best_h = []
    successes = []
    for f in range(1, 1 << 14):
        hb = hyperplane_basis(q14, f)
        rec = eval_H(hb, q_to_x)
        rec.update({"kind": "seed_hyperplane", "functional_mask": f})
        if rec["qrank"] == 13 and rec["xspan_rank"] == 22 and rec["l_intersection_dim"] == 9:
            successes.append(rec)
        if len(best_h) < 20:
            best_h.append((better_key(rec), f, hb, rec)); best_h.sort(reverse=True, key=lambda z: z[0])
        elif better_key(rec) > best_h[-1][0]:
            best_h[-1] = (better_key(rec), f, hb, rec); best_h.sort(reverse=True, key=lambda z: z[0])
    best_records = [r for _, _, _, r in best_h[:10]]
    all_rankone_qs_nonzero = [q for q in rank_one_qs if q != 0]
    # One-ARTIFACT swaps from the top hyperplanes.
    best_swap = []
    swap_success = []
    for _, f, hb, base_rec in best_h[:5]:
        for t in range(swaps // 5):
            drop = rng.randrange(13)
            core = [hb[i] for i in range(13) if i != drop]
            core_basis = o.gf2_basis_with_coords(core)
            # choose outside q
            for _ in range(200):
                q = rng.choice(all_rankone_qs_nonzero)
                rem, _ = o.gf2_reduce_with_coeff(core_basis, q)
                if rem != 0:
                    cand = core + [q]
                    if o.gf2_rank(cand) == 13:
                        break
            else:
                continue
            rec = eval_H(cand, q_to_x)
            rec.update({"kind": "one_swap", "from_functional_mask": f, "dropped_basis_pos": drop})
            if rec["qrank"] == 13 and rec["xspan_rank"] == 22 and rec["l_intersection_dim"] == 9:
                swap_success.append(rec)
            if len(best_swap) < 20:
                best_swap.append((better_key(rec), rec)); best_swap.sort(reverse=True, key=lambda z: z[0])
            elif better_key(rec) > best_swap[-1][0]:
                best_swap[-1] = (better_key(rec), rec); best_swap.sort(reverse=True, key=lambda z: z[0])
    # Random 12D cores in seed H14 plus one random outside rank-one q.
    best_core = []
    core_success = []
    q14_solver = o.gf2_basis_with_coords(q14)
    for t in range(core_ext):
        core = random_subspace_basis_inside(q14, 12, rng)
        core_solver = o.gf2_basis_with_coords(core)
        # make sure it is truly 12D inside H14
        for _ in range(200):
            q = rng.choice(all_rankone_qs_nonzero)
            rem_core, _ = o.gf2_reduce_with_coeff(core_solver, q)
            if rem_core == 0:
                continue
            # prefer q outside the full seed H14, not merely outside core.
            rem_seed, _ = o.gf2_reduce_with_coeff(q14_solver, q)
            if rem_seed != 0:
                cand = core + [q]
                if o.gf2_rank(cand) == 13:
                    break
        else:
            continue
        rec = eval_H(cand, q_to_x)
        rec.update({"kind": "core12_plus_outside", "trial": t})
        if rec["qrank"] == 13 and rec["xspan_rank"] == 22 and rec["l_intersection_dim"] == 9:
            core_success.append(rec)
        if len(best_core) < 20:
            best_core.append((better_key(rec), rec)); best_core.sort(reverse=True, key=lambda z: z[0])
        elif better_key(rec) > best_core[-1][0]:
            best_core[-1] = (better_key(rec), rec); best_core.sort(reverse=True, key=lambda z: z[0])
    return {
        "seed": name,
        "qmm_path": str(qmm_path),
        "hyperplane_successes": len(successes),
        "best_hyperplanes": best_records,
        "one_swap_trials": swaps,
        "one_swap_successes": len(swap_success),
        "best_one_swaps": [r for _, r in best_swap[:10]],
        "core12_plus_outside_trials": core_ext,
        "core12_plus_outside_successes": len(core_success),
        "best_core12_plus_outside": [r for _, r in best_core[:10]],
        "success_examples": (successes + swap_success + core_success)[:5],
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--swaps-per-seed", type=int, default=5000)
    ap.add_argument("--core-ext-per-seed", type=int, default=5000)
    ap.add_argument("--seed", type=int, default=2026090529)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    t0 = time.time()
    ws = Path(__file__).resolve().parent.parent
    outdir = ws / "data/f2_span_oracle"
    outdir.mkdir(parents=True, exist_ok=True)
    qrows = o.quotient_row_masks()
    print("Enumerating rank-one points...")
    rank_one_xs, rank_one_qs, q_to_x = o.enumerate_rank_one(qrows)
    seeds = [
        ("cn122", ws / "data/cn122_r23_reproduce/scheme.qmm"),
        ("serendipitous_8d34", ws / "data/fmm_r23_schemes/serendipitous_8d34.qmm"),
        ("naive_c88", ws / "data/fmm_r23_schemes/naive_c88.qmm"),
    ]
    results = []
    for name, path in seeds:
        print(f"\n=== {name} near-seed search ===")
        rec = search_seed(name, path, qrows, q_to_x, rank_one_qs, rng, args.swaps_per_seed, args.core_ext_per_seed)
        results.append(rec)
        print(f"  hyperplane successes {rec['hyperplane_successes']}; best {rec['best_hyperplanes'][:2]}")
        print(f"  one-swap successes {rec['one_swap_successes']}/{rec['one_swap_trials']}; best {rec['best_one_swaps'][:2]}")
        print(f"  core+outside successes {rec['core12_plus_outside_successes']}/{rec['core12_plus_outside_trials']}; best {rec['best_core12_plus_outside'][:2]}")
    total_success = sum(r["hyperplane_successes"] + r["one_swap_successes"] + r["core12_plus_outside_successes"] for r in results)
    result = {
        "purpose": "Bounded construction search for an F2 rank-22 canonical rank-one-span subspace near known rank-23 quotient spans.",
        "not_a_global_lower_bound": True,
        "target_condition": "qrank=13, xspan_rank=22, l_intersection_dim=9 for rank-one locus inside H.",
        "parameters": {"swaps_per_seed": args.swaps_per_seed, "core_ext_per_seed": args.core_ext_per_seed, "seed": args.seed},
        "total_successes": total_success,
        "seed_results": results,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    out = outdir / "near_seed_search.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(f"\nTotal successes {total_success}; saved {out}; elapsed {result['elapsed_sec']}s")


if __name__ == "__main__":
    main()
