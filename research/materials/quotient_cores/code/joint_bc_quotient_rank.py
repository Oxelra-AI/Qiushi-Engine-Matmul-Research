#!/usr/bin/env python3
r"""analysis: Joint B+C unconditional quotient-rank inequalities.

By Sylvester's rank inequality for L(q) = B_q C_q^T:
    dim V_q^B + dim V_q^C <= w_q + r_q

This gives the JOINT inequality:
    R_B + R_C <= 2*N_out + sum_{q in S}(w_q - r_q)

which is strictly stronger than adding two separate-side inequalities
(which would give 2*sum(w_q - r_q) instead of sum(w_q - r_q)).

As a linear constraint in x_p:
    2*sum_{p outside} x_p + sum_q sum_{p: q(p)=1} x_p >= R_B + R_C + sum r_q

Coefficient of x_p:
    2 if p is outside (target-active, not in any source)
    1 if p is in exactly one source
    2 if p is in two sources
    0 if p is nowhere
"""
from __future__ import annotations
import argparse, json, sys, time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence
import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (
    col_space_basis, contraction_matrix, mat_rank_f2,
    read_qmm_terms, restrict_terms_f2, rref_basis,
    row_space_basis, vec_to_mask, verify_terms,
)
from complete_core_and_transversal import ROOT
from quotient_rank_cuts import (
    build_contractions, counts_from_A, load_candidate_As,
    point_mask_for_q, projection_rank_mod_space, sum_basis,
)

OUTDIR = ROOT / "workspace/data/unconditional_qcuts"
ALLMASK = (1 << 255) - 1


def load_extended_candidates():
    candidates = load_candidate_As()
    for name, path in [
        ("v3_long", ROOT / "workspace/data/core_complete_transversal/core_e11_saturation_v3_complete_long.json"),
        ("fresh", ROOT / "workspace/data/unconditional_qcuts/fresh_uncond_sep_10r.json"),
    ]:
        if path.exists():
            d = json.loads(path.read_text())
            for r in d.get("rounds", []):
                if r.get("status") in ("OPTIMAL", "FEASIBLE") and "support" in r:
                    candidates[f"{name}_round{r['round']}"] = [int(x) for x in r["support"]]
    return candidates


def joint_quotient_check(
    A_cols: Sequence[int],
    contractions: Dict[int, dict],
    masks: Dict[int, int],
    sources: Sequence[int],
    target: int,
) -> dict:
    """Evaluate the joint B+C unconditional inequality."""
    counts = counts_from_A(A_cols)
    source_union = 0
    total_rank = 0
    total_excess = 0
    source_info = []
    for q in sources:
        source_union |= masks[q]
        rk = int(contractions[q]["rank"])
        wq = sum(int(counts.get(p, 0)) for p in range(1, 256) if ((q & p).bit_count() & 1))
        total_rank += rk
        total_excess += wq - rk
        source_info.append({"q": q, "rank": rk, "weight": wq, "excess": wq - rk})

    outside_mask = masks[target] & (~source_union) & ALLMASK
    N_out = sum(int(counts.get(p, 0)) for p in range(1, 256) if (outside_mask >> (p - 1)) & 1)

    # B-side: W_B = sum col L(q), R_B = rank(pi_{W_B} col L(target))
    W_B = sum_basis([contractions[q]["B_space"] for q in sources], 9)
    R_B = projection_rank_mod_space(contractions[target]["B_space"], W_B, 9)

    # C-side: W_C = sum row L(q), R_C = rank(pi_{W_C} row L(target))
    W_C = sum_basis([contractions[q]["C_space"] for q in sources], 9)
    R_C = projection_rank_mod_space(contractions[target]["C_space"], W_C, 9)

    # Separate B: N_out + total_excess >= R_B
    sep_B_lhs = N_out + total_excess
    sep_B_sat = sep_B_lhs >= R_B

    # Separate C: N_out + total_excess >= R_C
    sep_C_lhs = N_out + total_excess
    sep_C_sat = sep_C_lhs >= R_C

    # Joint: 2*N_out + total_excess >= R_B + R_C
    joint_lhs = 2 * N_out + total_excess
    joint_rhs = R_B + R_C
    joint_sat = joint_lhs >= joint_rhs

    return {
        "sources": [int(q) for q in sources],
        "target": int(target),
        "source_info": source_info,
        "N_out": N_out,
        "total_excess": total_excess,
        "total_source_rank": total_rank,
        "W_B_dim": len(W_B),
        "W_C_dim": len(W_C),
        "R_B": R_B,
        "R_C": R_C,
        "separate_B_satisfied": sep_B_sat,
        "separate_B_slack": sep_B_lhs - R_B,
        "separate_C_satisfied": sep_C_sat,
        "separate_C_slack": sep_C_lhs - R_C,
        "joint_lhs": joint_lhs,
        "joint_rhs": joint_rhs,
        "joint_satisfied": joint_sat,
        "joint_slack": joint_lhs - joint_rhs,
        "joint_strictly_stronger": (not joint_sat) and (sep_B_sat and sep_C_sat),
    }


def scan_joint_violations(
    A_cols: Sequence[int],
    contractions: Dict[int, dict],
    masks: Dict[int, int],
    points: List[int],
) -> dict:
    """Scan all pair-source, single-target joint B+C violations."""
    counts = counts_from_A(A_cols)
    nonzero_q = [q for q, c in contractions.items() if int(c['rank']) > 0]

    # Precompute weights
    weights = {}
    for q in nonzero_q:
        weights[q] = sum(int(counts.get(p, 0)) for p in range(1, 256) if ((q & p).bit_count() & 1))

    joint_viol = 0
    sep_only_viol = 0  # violations caught by separate but not joint
    joint_only_viol = 0  # violations caught by joint but not separate
    both_viol = 0
    total_nontrivial = 0
    joint_violations_head = []

    for i, q1 in enumerate(nonzero_q):
        for q2 in nonzero_q[i + 1:]:
            rq1 = int(contractions[q1]['rank'])
            rq2 = int(contractions[q2]['rank'])
            wq1 = weights[q1]
            wq2 = weights[q2]
            excess = (wq1 - rq1) + (wq2 - rq2)
            source_union = masks[q1] | masks[q2]

            # Precompute W_B, W_C
            W_B = sum_basis([contractions[q1]['B_space'], contractions[q2]['B_space']], 9)
            W_C = sum_basis([contractions[q1]['C_space'], contractions[q2]['C_space']], 9)
            if len(W_B) >= 9 and len(W_C) >= 9:
                continue

            for target in nonzero_q:
                R_B = projection_rank_mod_space(contractions[target]['B_space'], W_B, 9) if len(W_B) < 9 else 0
                R_C = projection_rank_mod_space(contractions[target]['C_space'], W_C, 9) if len(W_C) < 9 else 0
                if R_B <= 0 and R_C <= 0:
                    continue
                total_nontrivial += 1

                outside = masks[target] & (~source_union) & ALLMASK
                N_out = sum(int(counts.get(p, 0)) for p in range(1, 256) if (outside >> (p - 1)) & 1)

                # Separate checks
                sep_B_fail = (N_out + excess < R_B) if R_B > 0 else False
                sep_C_fail = (N_out + excess < R_C) if R_C > 0 else False
                sep_fail = sep_B_fail or sep_C_fail

                # Joint check
                joint_lhs = 2 * N_out + excess
                joint_rhs = R_B + R_C
                joint_fail = joint_lhs < joint_rhs

                if sep_fail and joint_fail:
                    both_viol += 1
                elif sep_fail and not joint_fail:
                    sep_only_viol += 1  # shouldn't happen; joint is stronger
                elif joint_fail and not sep_fail:
                    joint_only_viol += 1
                    if len(joint_violations_head) < 40:
                        joint_violations_head.append({
                            'sources': [q1, q2], 'target': target,
                            'rq1': rq1, 'rq2': rq2, 'wq1': wq1, 'wq2': wq2,
                            'excess': excess, 'N_out': N_out,
                            'R_B': R_B, 'R_C': R_C,
                            'joint_lhs': joint_lhs, 'joint_rhs': joint_rhs,
                            'joint_deficit': joint_rhs - joint_lhs,
                            'sep_B_slack': N_out + excess - R_B,
                            'sep_C_slack': N_out + excess - R_C,
                        })

    return {
        'total_nontrivial': total_nontrivial,
        'both_violations': both_viol,
        'separate_only_violations': sep_only_viol,
        'joint_only_violations': joint_only_viol,
        'joint_strictly_new': joint_only_viol,
        'joint_violations_head': joint_violations_head,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--full-scan", action="store_true")
    args = ap.parse_args()
    OUTDIR.mkdir(parents=True, exist_ok=True)

    T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
    contractions = build_contractions(T_core)
    masks = {q: point_mask_for_q(q) for q in contractions}
    points = list(range(1, 256))

    candidates = load_extended_candidates()
    print(f"Loaded {len(candidates)} candidates")

    # Test concrete instance
    print("\n=== Joint B+C check: sources [150,176], target 107 ===")
    for name in ["cn122_E11_core_rank21_genuine", "v2_round5", "fresh_round8"]:
        if name in candidates:
            r = joint_quotient_check(candidates[name], contractions, masks, [150, 176], 107)
            print(f"  {name}: R_B={r['R_B']} R_C={r['R_C']} N_out={r['N_out']} "
                  f"excess={r['total_excess']} joint_lhs={r['joint_lhs']} joint_rhs={r['joint_rhs']} "
                  f"joint_sat={r['joint_satisfied']} sep_B_sat={r['separate_B_satisfied']} "
                  f"joint_strictly_stronger={r['joint_strictly_stronger']}")

    # Scan key candidates for joint-only violations
    if args.full_scan:
        print("\n=== Full joint B+C scan on key candidates ===")
        key_candidates = [n for n in candidates if n.startswith(("cn122", "v2_round5",
                          "v3_long_round12", "fresh_round8",
                          "v3_long_round14", "fresh_round4",
                          "fresh_round9"))]
    else:
        key_candidates = [n for n in candidates if n in (
            "cn122_E11_core_rank21_genuine", "v2_round5",
            "v3_long_round12", "fresh_round8", "fresh_round9")]

    print(f"\n=== Joint B+C violation scan for {len(key_candidates)} candidates ===")
    scan_results = {}
    for name in sorted(key_candidates):
        if name not in candidates:
            continue
        t0 = time.time()
        sr = scan_joint_violations(candidates[name], contractions, masks, points)
        elapsed = time.time() - t0
        scan_results[name] = sr
        print(f"  {name}: both={sr['both_violations']} sep_only={sr['separate_only_violations']} "
              f"joint_only={sr['joint_strictly_new']} sec={elapsed:.1f}")
        for v in sr['joint_violations_head'][:3]:
            print(f"    joint-only: src=[{v['sources'][0]},{v['sources'][1]}] tgt={v['target']} "
                  f"R_B={v['R_B']} R_C={v['R_C']} N_out={v['N_out']} excess={v['excess']} "
                  f"deficit={v['joint_deficit']}")

    out = OUTDIR / "joint_bc_quotient_rank.json"
    out.write_text(json.dumps({
        "schema": "joint_bc_quotient_rank_v1",
        "mathematical_statement": "2*N_out + sum(w_q - r_q) >= R_B + R_C. Joint B+C bound from Sylvester.",
        "scan_results": {name: {k: v for k, v in sr.items() if k != 'joint_violations_head'}
                         for name, sr in scan_results.items()},
        "joint_violations_sample": {name: sr['joint_violations_head'][:10]
                                     for name, sr in scan_results.items()
                                     if sr['joint_strictly_new'] > 0},
    }, indent=2, sort_keys=True) + "\n")
    print(f"\nSaved {out}")


if __name__ == "__main__":
    main()
