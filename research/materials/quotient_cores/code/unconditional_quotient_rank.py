#!/usr/bin/env python3
r"""analysis: Unconditional quotient-rank inequalities.

Mathematical result (dimension bound):
For any rank-s decomposition T = sum_t a_t ⊗ b_t ⊗ c_t and a set of source
contractions S={q1,...,qk}, define:
  w_q = #{t : q(a_t) = 1}  (contraction weight, linear in multiplicities)
  r_q = rank L(q)           (contraction rank, data of the tensor)
  W   = sum_{q in S} col L(q)  (sum of source B-column spaces)
  R   = rank(pi_W L(target))   (projected target rank modulo W)
  N_out = #{t : target(a_t)=1 and q(a_t)=0 for all q in S}

Then for any decomposition (no saturation requirement):
    N_out + sum_{q in S} (w_q - r_q) >= R.

Proof: B-factors of q-participants span V_q of dim <= w_q, containing col L(q)
of dim r_q.  So dim(V_q mod W) <= w_q - r_q.  Target projected rank
R <= dim(outside B-span mod W) + sum dim(V_q mod W) <= N_out + sum(w_q - r_q).

As a linear constraint in multiplicity variables x_p:
    sum_{p: target(p)=1, q(p)=0 for all q in S} x_p
    + sum_{q in S} (sum_{p: q(p)=1} x_p - r_q)
    >= R

This is purely linear, eliminates saturation-guard Booleans entirely.

This script:
1. Validates on cn122 E11 core control (including nonsaturated sources)
2. Evaluates on all known candidate supports
3. Compares guarded vs unconditional strength
"""
from __future__ import annotations
import argparse, json, sys, time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence, Tuple
import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (
    col_space_basis, contraction_matrix, gf2_rank_rows,
    mat_rank_f2, read_qmm_terms, restrict_terms_f2,
    rref_basis, row_space_basis, vec_to_mask, verify_terms,
)
from complete_core_and_transversal import ROOT
from quotient_rank_cuts import (
    build_contractions, counts_from_A, load_candidate_As,
    point_mask_for_q, projection_rank_mod_space, sum_basis,
)

OUTDIR = ROOT / "workspace/data/unconditional_qcuts"
ALLMASK = (1 << 255) - 1


def unconditional_cut_check(
    A_cols: Sequence[int],
    contractions: Dict[int, dict],
    masks: Dict[int, int],
    side: str,
    sources: Sequence[int],
    target: int,
) -> dict:
    """Evaluate the unconditional quotient-rank inequality on a concrete A-list."""
    counts = counts_from_A(A_cols)
    side_key = "B_space" if side == "B" else "C_space"

    # Source data
    source_info = []
    for q in sources:
        rk = int(contractions[q]["rank"])
        wq = sum(int(counts.get(p, 0)) for p in range(1, 256) if ((q & p).bit_count() & 1))
        source_info.append({"q": int(q), "rank": rk, "weight": wq, "excess": wq - rk})

    # W = sum of source column spaces
    W = sum_basis([contractions[q][side_key] for q in sources], 9)
    Wdim = len(W)

    # Projected target rank
    target_space = contractions[target][side_key]
    R = projection_rank_mod_space(target_space, W, 9)

    # Outside: target-participating but not in any source
    source_union = 0
    for q in sources:
        source_union |= masks[q]
    outside_mask = masks[target] & (~source_union) & ALLMASK

    N_out = sum(int(counts.get(p, 0)) for p in range(1, 256) if (outside_mask >> (p - 1)) & 1)

    # Unconditional LHS = N_out + sum(w_q - r_q)
    excess_sum = sum(si["excess"] for si in source_info)
    uncond_lhs = N_out + excess_sum

    # Guarded check (old): only when all sources saturated
    all_sat = all(si["weight"] == si["rank"] for si in source_info)
    guarded_violates = all_sat and (N_out < R)

    return {
        "side": side,
        "sources": [int(q) for q in sources],
        "target": int(target),
        "W_dim": Wdim,
        "projected_rank_R": R,
        "outside_point_count": int(outside_mask.bit_count()),
        "N_out": N_out,
        "source_info": source_info,
        "excess_sum": excess_sum,
        "unconditional_lhs": uncond_lhs,
        "unconditional_requirement": R,
        "unconditional_satisfied": uncond_lhs >= R,
        "unconditional_slack": uncond_lhs - R,
        "all_sources_saturated": all_sat,
        "guarded_N_out_check": N_out >= R if all_sat else None,
        "guarded_violates": guarded_violates,
    }


def load_extended_candidates() -> Dict[str, List[int]]:
    """Load all known candidate A-lists."""
    candidates = load_candidate_As()

    # analysis v3 long run
    p = ROOT / "workspace/data/core_complete_transversal/core_e11_saturation_v3_complete_long.json"
    if p.exists():
        d = json.loads(p.read_text())
        for r in d.get("rounds", []):
            if r.get("status") in ("OPTIMAL", "FEASIBLE") and "support" in r:
                candidates[f"v3_long_round{r['round']}"] = [int(x) for x in r["support"]]

    return candidates


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--concrete-only", action="store_true")
    args = ap.parse_args()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()

    T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
    contractions = build_contractions(T_core)
    masks = {q: point_mask_for_q(q) for q in contractions}
    rank_dist = Counter(c["rank"] for c in contractions.values())
    print(f"E11 core contraction rank distribution: {dict(sorted(rank_dist.items()))}")

    candidates = load_extended_candidates()
    print(f"Loaded {len(candidates)} candidate/control A-lists")

    # 1) CONCRETE INSTANCE: sources 150,176, target 107, B side
    print("\n=== Concrete instance: sources [150,176], target 107, B side ===")
    concrete_evals = {}
    for name, A in sorted(candidates.items()):
        ev = unconditional_cut_check(A, contractions, masks, "B", [150, 176], 107)
        concrete_evals[name] = ev
        sat_label = "SAT" if ev["all_sources_saturated"] else "NONSAT"
        print(f"  {name}: uncond_lhs={ev['unconditional_lhs']} R={ev['projected_rank_R']} "
              f"slack={ev['unconditional_slack']} N_out={ev['N_out']} excess={ev['excess_sum']} "
              f"{sat_label} guarded_viol={ev['guarded_violates']}")

    # 2) SYSTEMATIC PAIR-SOURCE SCAN on all candidates
    if not args.concrete_only:
        print("\n=== Systematic unconditional pair-source scan ===")
        nonzero_q = [q for q, c in contractions.items() if int(c["rank"]) > 0]
        # For efficiency, precompute contraction weights for each candidate
        cand_weights = {}
        for name, A in candidates.items():
            counts = counts_from_A(A)
            wts = {}
            for q in nonzero_q:
                wts[q] = sum(int(counts.get(p, 0)) for p in range(1, 256) if ((q & p).bit_count() & 1))
            cand_weights[name] = (counts, wts)

        # Scan pair sources
        scan_results = {name: {"unconditional_violations": 0, "guarded_violations": 0,
                                "uncond_by_side": Counter(), "guard_by_side": Counter(),
                                "uncond_violations_head": []}
                        for name in candidates}
        total_nontrivial = 0
        for i, q1 in enumerate(nonzero_q):
            for q2 in nonzero_q[i + 1:]:
                source_union = masks[q1] | masks[q2]
                for side in ("B", "C"):
                    side_key = "B_space" if side == "B" else "C_space"
                    W = sum_basis([contractions[q1][side_key], contractions[q2][side_key]], 9)
                    if len(W) >= 9:
                        continue
                    for target in nonzero_q:
                        req = projection_rank_mod_space(contractions[target][side_key], W, 9)
                        if req <= 0:
                            continue
                        total_nontrivial += 1
                        outside = masks[target] & (~source_union) & ALLMASK
                        rq1 = int(contractions[q1]["rank"])
                        rq2 = int(contractions[q2]["rank"])
                        for name, (counts, wts) in cand_weights.items():
                            wq1 = wts[q1]; wq2 = wts[q2]
                            N_out = sum(int(counts.get(p, 0)) for p in range(1, 256) if (outside >> (p - 1)) & 1)
                            # Unconditional check
                            uncond_lhs = N_out + (wq1 - rq1) + (wq2 - rq2)
                            if uncond_lhs < req:
                                sr = scan_results[name]
                                sr["unconditional_violations"] += 1
                                sr["uncond_by_side"][side] += 1
                                if len(sr["uncond_violations_head"]) < 20:
                                    sr["uncond_violations_head"].append({
                                        "side": side, "sources": [q1, q2],
                                        "target": target, "W_dim": len(W),
                                        "req": req, "N_out": N_out,
                                        "wq1": wq1, "wq2": wq2,
                                        "rq1": rq1, "rq2": rq2,
                                        "uncond_lhs": uncond_lhs,
                                    })
                            # Guarded check
                            if wq1 == rq1 and wq2 == rq2 and N_out < req:
                                scan_results[name]["guarded_violations"] += 1
                                scan_results[name]["guard_by_side"][side] += 1

        print(f"Total nontrivial pair-source cut instances: {total_nontrivial}")
        for name in sorted(candidates.keys()):
            sr = scan_results[name]
            print(f"  {name}: uncond_viol={sr['unconditional_violations']} "
                  f"guarded_viol={sr['guarded_violations']} "
                  f"uncond_by_side={dict(sr['uncond_by_side'])}")

    # 3) Save results
    result = {
        "schema": "unconditional_quotient_rank_v1",
        "field": "F2",
        "core": "E11",
        "mathematical_statement": (
            "For sources S, target t: "
            "N_out + sum_{q in S}(w_q - r_q) >= rank(pi_W L(t)), "
            "where N_out = sum of x_p for target-active outside points, "
            "w_q = contraction weight (sum of x_p for q-active points), "
            "r_q = contraction rank. "
            "This is unconditional: no saturation guards needed."
        ),
        "concrete_instance_150_176_107_B": concrete_evals,
        "rank_distribution": {str(k): int(v) for k, v in sorted(rank_dist.items())},
    }
    if not args.concrete_only:
        result["pair_source_scan"] = {
            "total_nontrivial": total_nontrivial,
            "candidate_evaluations": {
                name: {
                    "unconditional_violations": sr["unconditional_violations"],
                    "guarded_violations": sr["guarded_violations"],
                    "uncond_by_side": dict(sr["uncond_by_side"]),
                    "guard_by_side": dict(sr["guard_by_side"]),
                    "uncond_violations_head": sr["uncond_violations_head"],
                }
                for name, sr in sorted(scan_results.items())
            },
        }
    result["total_elapsed_sec"] = round(time.time() - t0, 3)
    out = OUTDIR / "unconditional_quotient_rank_validation.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"\nSaved {out}")


if __name__ == "__main__":
    main()
