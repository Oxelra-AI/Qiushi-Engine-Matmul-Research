#!/usr/bin/env python3
r"""analysis: quotient-rank aggregate cuts from saturated source contractions.

If source contractions S are saturated, every term participating in any source
q in S has its B-factor in the sum W_B(S) of the source column spaces (and
similarly C-factor in W_C(S)).  Projecting a target contraction L(t) modulo W
therefore gives a rank lower bound on the number of target-participating terms
outside the source union:

    all q in S saturated  ==>  sum_{p: t(p)=1 and q(p)=0 for all q in S} x_p
                                >= rank(pi_W L(t)).

This script independently checks the concrete E11-core witness from analysis:
B-side sources 150 and 176, target 107.  It also scans pair-source aggregate
cuts on the canonical E11 core and evaluates them on current candidate supports.
The cuts are conditional search constraints, not proof-producing lower bounds by
themselves.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (  # noqa: E402
    col_space_basis,
    contraction_matrix,
    gf2_rank_rows,
    in_span,
    mat_rank_f2,
    read_qmm_terms,
    restrict_terms_f2,
    rref_basis,
    row_space_basis,
    vec_to_mask,
    verify_terms,
)
from complete_core_and_transversal import ROOT  # noqa: E402

OUTDIR = ROOT / "workspace/data/quotient_rank_cuts"


def sum_basis(spaces: Sequence[Sequence[int]], n: int = 9) -> Tuple[int, ...]:
    rows: List[int] = []
    for sp in spaces:
        rows.extend(int(x) for x in sp)
    return rref_basis(rows, n)


def projection_rank_mod_space(target_space: Sequence[int], W: Sequence[int], n: int = 9) -> int:
    """rank of target_space after quotienting by W."""
    rw = gf2_rank_rows(W, n)
    return gf2_rank_rows(list(W) + list(target_space), n) - rw


def point_mask_for_q(q: int, npoints: int = 255) -> int:
    mask = 0
    for p in range(1, npoints + 1):
        if ((int(q) & p).bit_count() & 1):
            mask |= 1 << (p - 1)
    return mask


def count_on_mask(counts: Dict[int, int], mask: int) -> int:
    return sum(int(c) for p, c in counts.items() if (mask >> (int(p) - 1)) & 1)


def counts_from_A(A: Sequence[int]) -> Dict[int, int]:
    return {int(k): int(v) for k, v in Counter(int(a) for a in A).items()}


def build_contractions(T: np.ndarray) -> Dict[int, dict]:
    out: Dict[int, dict] = {}
    for q in range(1, 1 << T.shape[0]):
        M = contraction_matrix(T, q)
        rk = mat_rank_f2(M)
        out[q] = {
            "q": int(q),
            "rank": int(rk),
            "B_space": tuple(int(x) for x in col_space_basis(M)),
            "C_space": tuple(int(x) for x in row_space_basis(M)),
        }
    return out


def source_saturated(counts: Dict[int, int], q: int, masks: Dict[int, int], contractions: Dict[int, dict]) -> bool:
    return count_on_mask(counts, masks[q]) == int(contractions[q]["rank"])


def quotient_cut_instance(
    contractions: Dict[int, dict],
    masks: Dict[int, int],
    side: str,
    sources: Sequence[int],
    target: int,
) -> dict:
    side_key = "B_space" if side == "B" else "C_space"
    W = sum_basis([contractions[q][side_key] for q in sources], 9)
    target_space = contractions[target][side_key]
    req = projection_rank_mod_space(target_space, W, 9)
    union = 0
    for q in sources:
        union |= masks[q]
    outside = masks[target] & (~union) & ((1 << 255) - 1)
    return {
        "side": side,
        "sources": [int(q) for q in sources],
        "source_ranks": {str(q): int(contractions[q]["rank"]) for q in sources},
        "source_side_bases": {str(q): list(contractions[q][side_key]) for q in sources},
        "source_side_dims": {str(q): len(contractions[q][side_key]) for q in sources},
        "W_basis": list(W),
        "W_dim": len(W),
        "target": int(target),
        "target_rank": int(contractions[target]["rank"]),
        "target_side_basis": list(target_space),
        "target_side_dim": len(target_space),
        "projected_rank_requirement": int(req),
        "outside_point_count": int(outside.bit_count()),
        "outside_points_head": [p for p in range(1, 256) if (outside >> (p - 1)) & 1][:80],
        "outside_mask_hex": hex(outside),
        "source_union_point_count": int(union.bit_count()),
    }


def evaluate_cut_on_A(cut: dict, A_cols: Sequence[int], masks: Dict[int, int], contractions: Dict[int, dict]) -> dict:
    counts = counts_from_A(A_cols)
    union = 0
    for q in cut["sources"]:
        union |= masks[int(q)]
    outside = masks[int(cut["target"])] & (~union) & ((1 << 255) - 1)
    source_weights = {str(q): count_on_mask(counts, masks[int(q)]) for q in cut["sources"]}
    source_ranks = {str(q): int(contractions[int(q)]["rank"]) for q in cut["sources"]}
    guard_true = all(source_weights[str(q)] == source_ranks[str(q)] for q in cut["sources"])
    lhs = count_on_mask(counts, outside)
    req = int(cut["projected_rank_requirement"])
    return {
        "term_count": len(A_cols),
        "distinct_A_points": len(counts),
        "multiplicity_hist": {str(k): int(v) for k, v in sorted(Counter(counts.values()).items())},
        "source_weights": source_weights,
        "source_ranks": source_ranks,
        "source_saturation_guard_true": bool(guard_true),
        "outside_lhs": int(lhs),
        "requirement": req,
        "violates_when_guard_true": bool(guard_true and lhs < req),
        "target_weight": count_on_mask(counts, masks[int(cut["target"])]),
        "target_rank": int(contractions[int(cut["target"])]["rank"]),
        "target_saturated": count_on_mask(counts, masks[int(cut["target"])]) == int(contractions[int(cut["target"])]["rank"]),
    }


def load_candidate_As() -> Dict[str, List[int]]:
    candidates: Dict[str, List[int]] = {}
    # Genuine cn122 E11 core with multiplicities retained.
    qmm = ROOT / "workspace/data/cn122_3x3_r23_repro/scheme.qmm"
    T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
    terms = read_qmm_terms(qmm)
    core_terms = restrict_terms_f2(terms, 1)
    assert verify_terms(T_core, core_terms), "cn122 E11 core control failed exact verification"
    candidates["cn122_E11_core_rank21_genuine"] = [vec_to_mask(t["u"]) for t in core_terms]

    # analysis short v2 run candidates.
    p = ROOT / "workspace/data/dual_ruling/core_e11_saturation_v2.json"
    if p.exists():
        d = json.loads(p.read_text())
        for r in d.get("rounds", []):
            if r.get("status") in ("OPTIMAL", "FEASIBLE") and "support" in r:
                candidates[f"v2_round{r['round']}"] = [int(x) for x in r["support"]]

    # analysis long v2 candidates.
    p = ROOT / "workspace/data/dual_ruling/core_e11_saturation_v2_long.json"
    if p.exists():
        d = json.loads(p.read_text())
        for r in d.get("rounds", []):
            if r.get("status") in ("OPTIMAL", "FEASIBLE") and "support" in r:
                candidates[f"v2_long_round{r['round']}"] = [int(x) for x in r["support"]]

    # analysis complete distinct pilot.
    p = ROOT / "workspace/data/core_complete_transversal/core_e11_saturation_v3_complete.json"
    if p.exists():
        d = json.loads(p.read_text())
        for r in d.get("rounds", []):
            if r.get("status") in ("OPTIMAL", "FEASIBLE") and "support" in r:
                candidates[f"v3_round{r['round']}"] = [int(x) for x in r["support"]]
    return candidates


def scan_pair_cuts(
    contractions: Dict[int, dict],
    masks: Dict[int, int],
    candidate_As: Dict[str, List[int]],
    store_limit: int = 80,
) -> dict:
    nonzero_q = [q for q, c in contractions.items() if int(c["rank"]) > 0]
    cand_counts = {name: counts_from_A(A) for name, A in candidate_As.items()}
    cand_results = {
        name: {
            "guard_true_cuts": 0,
            "violated_guard_true_cuts": 0,
            "violations_by_side": Counter(),
            "violations_by_requirement": Counter(),
            "violations_head": [],
        }
        for name in candidate_As
    }
    summary = {
        "source_pair_count": 0,
        "nontrivial_cut_count": 0,
        "by_side": Counter(),
        "by_Wdim_req": Counter(),
        "by_target_rank_req": Counter(),
        "by_outside_size_req": Counter(),
        "sample_cuts": [],
    }
    t0 = time.time()
    allmask = (1 << 255) - 1
    for i, q1 in enumerate(nonzero_q):
        for q2 in nonzero_q[i + 1:]:
            summary["source_pair_count"] += 1
            source_union = masks[q1] | masks[q2]
            for side in ("B", "C"):
                side_key = "B_space" if side == "B" else "C_space"
                W = sum_basis([contractions[q1][side_key], contractions[q2][side_key]], 9)
                Wdim = len(W)
                if Wdim >= 9:
                    continue
                for target in nonzero_q:
                    target_space = contractions[target][side_key]
                    req = projection_rank_mod_space(target_space, W, 9)
                    if req <= 0:
                        continue
                    outside = masks[target] & (~source_union) & allmask
                    if outside.bit_count() < req:
                        # Then the source guards alone would be impossible; keep it too.
                        pass
                    summary["nontrivial_cut_count"] += 1
                    summary["by_side"][side] += 1
                    summary["by_Wdim_req"][(Wdim, req)] += 1
                    summary["by_target_rank_req"][(int(contractions[target]["rank"]), req)] += 1
                    summary["by_outside_size_req"][(outside.bit_count(), req)] += 1
                    if len(summary["sample_cuts"]) < store_limit and req >= 3:
                        summary["sample_cuts"].append({
                            "side": side,
                            "sources": [q1, q2],
                            "source_ranks": [int(contractions[q1]["rank"]), int(contractions[q2]["rank"])],
                            "W_dim": Wdim,
                            "target": target,
                            "target_rank": int(contractions[target]["rank"]),
                            "requirement": int(req),
                            "outside_point_count": int(outside.bit_count()),
                        })
                    for name, counts in cand_counts.items():
                        w1 = count_on_mask(counts, masks[q1])
                        w2 = count_on_mask(counts, masks[q2])
                        if w1 == int(contractions[q1]["rank"]) and w2 == int(contractions[q2]["rank"]):
                            cr = cand_results[name]
                            cr["guard_true_cuts"] += 1
                            lhs = count_on_mask(counts, outside)
                            if lhs < req:
                                cr["violated_guard_true_cuts"] += 1
                                cr["violations_by_side"][side] += 1
                                cr["violations_by_requirement"][req] += 1
                                if len(cr["violations_head"]) < 40:
                                    cr["violations_head"].append({
                                        "side": side,
                                        "sources": [q1, q2],
                                        "source_ranks": [int(contractions[q1]["rank"]), int(contractions[q2]["rank"])],
                                        "source_weights": [w1, w2],
                                        "W_dim": Wdim,
                                        "target": target,
                                        "target_rank": int(contractions[target]["rank"]),
                                        "requirement": int(req),
                                        "outside_lhs": int(lhs),
                                        "outside_point_count": int(outside.bit_count()),
                                    })
    # Convert Counters with tuple keys to readable dicts.
    scan = {
        "elapsed_sec": round(time.time() - t0, 3),
        "source_pair_count": summary["source_pair_count"],
        "nontrivial_cut_count": summary["nontrivial_cut_count"],
        "by_side": dict(summary["by_side"]),
        "by_Wdim_req": {f"W{wdim}_req{req}": int(v) for (wdim, req), v in sorted(summary["by_Wdim_req"].items())},
        "by_target_rank_req": {f"rank{rk}_req{req}": int(v) for (rk, req), v in sorted(summary["by_target_rank_req"].items())},
        "by_outside_size_req_head": {f"outside{os}_req{req}": int(v) for (os, req), v in sorted(summary["by_outside_size_req"].items())[:120]},
        "sample_cuts": summary["sample_cuts"],
        "candidate_evaluations": {},
    }
    for name, cr in cand_results.items():
        scan["candidate_evaluations"][name] = {
            "guard_true_cuts": int(cr["guard_true_cuts"]),
            "violated_guard_true_cuts": int(cr["violated_guard_true_cuts"]),
            "violations_by_side": dict(cr["violations_by_side"]),
            "violations_by_requirement": {str(k): int(v) for k, v in sorted(cr["violations_by_requirement"].items())},
            "violations_head": cr["violations_head"],
        }
    return scan


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-pair-scan", action="store_true")
    ap.add_argument("--store-limit", type=int, default=80)
    ap.add_argument("--out", type=Path, default=OUTDIR / "quotient_rank_cuts_core_pair_scan.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

    t0 = time.time()
    T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
    contractions = build_contractions(T_core)
    masks = {q: point_mask_for_q(q) for q in contractions}
    rank_dist = Counter(c["rank"] for c in contractions.values())
    print(f"E11 core contraction rank distribution: {dict(sorted(rank_dist.items()))}")

    candidates = load_candidate_As()
    print(f"Loaded {len(candidates)} candidate/control A-lists")

    instance = quotient_cut_instance(contractions, masks, "B", [150, 176], 107)
    instance_evals = {name: evaluate_cut_on_A(instance, A, masks, contractions) for name, A in candidates.items()}
    print("Concrete instance B-side sources [150,176] -> target 107:")
    print(json.dumps({
        "source_ranks": instance["source_ranks"],
        "W_dim": instance["W_dim"],
        "target_rank": instance["target_rank"],
        "requirement": instance["projected_rank_requirement"],
        "outside_point_count": instance["outside_point_count"],
        "round5_eval": instance_evals.get("v2_round5"),
        "cn122_eval": instance_evals.get("cn122_E11_core_rank21_genuine"),
    }, sort_keys=True))

    scan = None
    if not args.no_pair_scan:
        scan = scan_pair_cuts(contractions, masks, candidates, store_limit=int(args.store_limit))
        print("Pair-source aggregate scan summary:")
        # Print compact candidate highlights.
        highlights = {}
        for name, ev in scan["candidate_evaluations"].items():
            if ev["violated_guard_true_cuts"] or name in ("cn122_E11_core_rank21_genuine", "v2_round5"):
                highlights[name] = {
                    "guard_true_cuts": ev["guard_true_cuts"],
                    "violated": ev["violated_guard_true_cuts"],
                    "by_side": ev["violations_by_side"],
                    "by_req": ev["violations_by_requirement"],
                }
        print(json.dumps({
            "nontrivial_cut_count": scan["nontrivial_cut_count"],
            "by_side": scan["by_side"],
            "elapsed_sec": scan["elapsed_sec"],
            "candidate_highlights": highlights,
        }, sort_keys=True))

    result = {
        "schema": "quotient_rank_cuts_v1",
        "field": "F2",
        "core": "E11",
        "mathematical_rule": "If all source contractions S are saturated, terms participating in their union have B/C factors in W=sum side spaces. Projecting a target contraction modulo W gives a conditional lower bound on the multiplicity outside the source union.",
        "rank_distribution": {str(k): int(v) for k, v in sorted(rank_dist.items())},
        "concrete_instance_sources_150_176_target_107_B": instance,
        "concrete_instance_evaluations": instance_evals,
        "pair_source_scan": scan,
        "comparison_to_guarded_transversal_witnesses": {
            "old_minimized_witness_meaning": "The analysis transversality witness excluded a candidate when q_star and source contractions were all saturated and a named subset of A-points had domains spanning too small a space.",
            "quotient_rank_strengthening": "The aggregate cut keeps only the source-saturation guards and replaces the named subset by a lower bound on all target-active A-directions outside the source union; the target contraction need not be saturated.",
            "concrete_core_instance": "For sources 150 and 176 on the B side, W has dimension 6 and target 107 has quotient rank 3, so source saturation implies at least three multiplicities among p with 107(p)=1 and 150(p)=176(p)=0.",
        },
        "total_elapsed_sec": round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Saved {args.out}")


if __name__ == "__main__":
    main()
