#!/usr/bin/env python3
r"""
analysis: exact star-neighborhood search for the F_2 canonical span problem.

For a 13D quotient subspace H < E/L, define R(H) as the rank-one matrices whose
quotient lies in H.  H gives a rank-22 F_2 algorithm exactly when R(H) spans a
22D space with 9 hidden L directions: qrank(R(H))=13 and xrank(R(H))=22.

This script strengthens the bounded near-seed search by exhaustive enumeration
of all 13D H containing selected 12D cores K.  The cores K are obtained by
removing one basis vector from the best hyperplanes inside each known rank-23
seed quotient span.  For each K, all rank-one quotient points are grouped by
coset modulo K; each nonzero coset gives one candidate H=K+<q>.  This is exact
for these star neighborhoods and remains a local computation, not a global
lower bound.
"""
from __future__ import annotations

import argparse
import json
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Tuple

import f2_span_oracle as o
import f2_near_seed_search as ns


def canonical_mod_subspace(v: int, basis: Dict[int, Tuple[int, int]]) -> int:
    """Canonical residual of v modulo a reduced GF(2) basis.

    Unlike gf2_reduce_with_coeff, this must continue through lower pivots even
    when the current highest bit is not a pivot.  It is used only to group
    quotient-space cosets, not to recover basis coordinates.
    """
    for p in sorted(basis.keys(), reverse=True):
        bv, _ = basis[p]
        if (v >> p) & 1:
            v ^= bv
    return v


def coset_groups_for_K(rank_one_qs: List[int], rank_one_xs: List[int], K: List[int]):
    solver = o.gf2_basis_with_coords(K)
    groups: Dict[int, List[Tuple[int, int]]] = defaultdict(list)
    base: List[Tuple[int, int]] = []
    for q, x in zip(rank_one_qs, rank_one_xs):
        res = canonical_mod_subspace(q, solver)
        if res == 0:
            base.append((q, x))
        else:
            groups[res].append((q, x))
    return base, groups


def eval_member_pairs(pairs: List[Tuple[int, int]]) -> Dict:
    qs = [q for q, _ in pairs]
    xs = [x for _, x in pairs]
    qrank = o.gf2_rank(qs)
    xrank = o.gf2_rank(xs)
    return {"rankone_count": len(pairs), "qrank": qrank, "xspan_rank": xrank, "l_intersection_dim": xrank - qrank}


def key(rec: Dict) -> Tuple[int, int, int, int]:
    return (rec["xspan_rank"], rec["l_intersection_dim"], rec["qrank"], rec["rankone_count"])


def top_seed_hyperplanes(q14: List[int], q_to_x: Dict[int, List[int]], top_n: int) -> List[Tuple[int, List[int], Dict]]:
    best: List[Tuple[Tuple[int, int, int, int], int, List[int], Dict]] = []
    for f in range(1, 1 << 14):
        hb = ns.hyperplane_basis(q14, f)
        rec = ns.eval_H(hb, q_to_x)
        rec["functional_mask"] = f
        k = key(rec)
        if len(best) < top_n:
            best.append((k, f, hb, rec)); best.sort(reverse=True, key=lambda z: z[0])
        elif k > best[-1][0]:
            best[-1] = (k, f, hb, rec); best.sort(reverse=True, key=lambda z: z[0])
    return [(f, hb, rec) for _, f, hb, rec in best]


def scan_core(seed_name: str, functional_mask: int, drop_pos: int, K: List[int], rank_one_qs: List[int], rank_one_xs: List[int], min_count: int = 22) -> Dict:
    base, groups = coset_groups_for_K(rank_one_qs, rank_one_xs, K)
    base_rec = eval_member_pairs(base)
    candidates_seen = 0
    evaluated = 0
    count_hist = Counter()
    best: List[Tuple[Tuple[int, int, int, int], Dict]] = []
    successes: List[Dict] = []
    for res, gpairs in groups.items():
        cnt = len(base) + len(gpairs)
        count_hist[cnt] += 1
        candidates_seen += 1
        if cnt < min_count:
            continue
        pairs = base + gpairs
        rec = eval_member_pairs(pairs)
        rec.update({"seed": seed_name, "functional_mask": functional_mask, "drop_pos": drop_pos, "coset_residual": res, "base_rankone_count": len(base), "coset_rankone_count": len(gpairs)})
        evaluated += 1
        if rec["qrank"] == 13 and rec["xspan_rank"] == 22 and rec["l_intersection_dim"] == 9:
            successes.append(rec)
        k = key(rec)
        if len(best) < 8:
            best.append((k, rec)); best.sort(reverse=True, key=lambda z: z[0])
        elif k > best[-1][0]:
            best[-1] = (k, rec); best.sort(reverse=True, key=lambda z: z[0])
    return {
        "seed": seed_name,
        "functional_mask": functional_mask,
        "drop_pos": drop_pos,
        "K_rank": o.gf2_rank(K),
        "base_in_K": base_rec,
        "cosets_seen": candidates_seen,
        "cosets_evaluated_count_ge_min": evaluated,
        "count_hist_ge_18": {str(k): v for k, v in sorted(count_hist.items()) if k >= 18},
        "success_count": len(successes),
        "success_examples": successes[:3],
        "best_candidates": [r for _, r in best],
    }


def scan_seed(name: str, qmm_path: Path, rank_one_qs: List[int], rank_one_xs: List[int], q_to_x: Dict[int, List[int]], qrows: List[int], top_hyperplanes: int) -> Dict:
    q14 = ns.seed_qbasis(qmm_path, qrows)
    tops = top_seed_hyperplanes(q14, q_to_x, top_hyperplanes)
    core_results = []
    for f, hb, hrec in tops:
        print(f"    hyperplane f={f}: {hrec}")
        for drop in range(13):
            K = [hb[i] for i in range(13) if i != drop]
            crec = scan_core(name, f, drop, K, rank_one_qs, rank_one_xs)
            core_results.append(crec)
            if crec["success_count"]:
                print(f"      SUCCESS at drop {drop}: {crec['success_examples'][0]}")
    total_success = sum(c["success_count"] for c in core_results)
    best_all = []
    for c in core_results:
        for r in c["best_candidates"]:
            k = key(r)
            if len(best_all) < 10:
                best_all.append((k, r)); best_all.sort(reverse=True, key=lambda z: z[0])
            elif k > best_all[-1][0]:
                best_all[-1] = (k, r); best_all.sort(reverse=True, key=lambda z: z[0])
    return {
        "seed": name,
        "qmm_path": str(qmm_path),
        "top_hyperplanes": [{"functional_mask": f, **rec} for f, _, rec in tops],
        "cores_scanned": len(core_results),
        "total_success_count": total_success,
        "best_candidates_over_cores": [r for _, r in best_all],
        "core_results": core_results,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--top-hyperplanes", type=int, default=2)
    args = ap.parse_args()
    t0 = time.time()
    ws = Path(__file__).resolve().parent.parent
    outdir = ws / "data/f2_span_oracle"
    outdir.mkdir(parents=True, exist_ok=True)
    qrows = o.quotient_row_masks()
    print("Enumerating rank-one set...")
    rank_one_xs, rank_one_qs, q_to_x = o.enumerate_rank_one(qrows)
    seeds = [
        ("cn122", ws / "data/cn122_r23_reproduce/scheme.qmm"),
        ("serendipitous_8d34", ws / "data/fmm_r23_schemes/serendipitous_8d34.qmm"),
        ("naive_c88", ws / "data/fmm_r23_schemes/naive_c88.qmm"),
    ]
    seed_results = []
    for name, path in seeds:
        print(f"\n=== exact star scan {name} ===")
        rec = scan_seed(name, path, rank_one_qs, rank_one_xs, q_to_x, qrows, args.top_hyperplanes)
        seed_results.append(rec)
        print(f"  cores={rec['cores_scanned']} successes={rec['total_success_count']} best={rec['best_candidates_over_cores'][:2]}")
    result = {
        "purpose": "Exact local star-neighborhood search in the canonical F2 rank-one-span quotient.",
        "not_a_global_lower_bound": True,
        "top_hyperplanes_per_seed": args.top_hyperplanes,
        "target_condition": "rank-one locus in H has qrank=13, xspan_rank=22, l_intersection_dim=9.",
        "seed_results": seed_results,
        "total_success_count": sum(r["total_success_count"] for r in seed_results),
        "elapsed_sec": round(time.time() - t0, 3),
    }
    out = outdir / "exact_star_neighborhood.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(f"\nTotal successes {result['total_success_count']}; saved {out}; elapsed {result['elapsed_sec']}s")


if __name__ == "__main__":
    main()
