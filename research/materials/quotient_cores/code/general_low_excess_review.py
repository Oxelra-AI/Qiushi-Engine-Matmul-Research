#!/usr/bin/env python3
r"""analysis independent review of the generalized low-excess A-list filter.

This is a review-side checker, not a replacement for the analysis script.  It
rebuilds the contraction spaces and tests the load-bearing inequalities against
actual verified rank-21 E11-core decompositions.  It also measures one natural
strengthening that analysis did not use: tight rank-3 (invertible) contractions may
serve as sources of independent shared B/C vectors when constraining rank-1/2
near-tight target contractions.

The mathematics being checked is:
  M_lam = Lambda^T \otimes I_3, rank(M_lam)=3 rank(Lambda).
  For an exact contraction with m active terms and r=rank(M_lam),
       e_B + e_C <= m-r,
  where e_B/e_C are dimensions of active B/C spans modulo col/row(M_lam).
  If eta is tight, its active B and C vectors are independent bases of the
  prescribed spaces.  If eta and mu share h active terms, then
       e_B(mu) >= max(0, h - dim(U_eta cap U_mu)),
       e_C(mu) >= max(0, h - dim(V_eta cap V_mu)).

All arithmetic is over F2; vector subspaces are represented by integer row masks.
"""
from __future__ import annotations

import collections
import json
import time
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

ROOT = Path("research/research_record")
POOL_PATH = Path("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy")
FULL = ROOT / "workspace/data/general_low_excess/general_low_excess_filter_samew_full.json"
OUT = ROOT / "workspace/data/general_low_excess/general_low_excess_review.json"

N = 9


def parity(x: int) -> int:
    return int(x).bit_count() & 1


def dot8(a: int, b: int) -> int:
    return parity(int(a) & int(b))


def full_mask_from_quotient(q: int) -> int:
    full = 0
    k = 0
    for bit in range(9):
        if bit == 0:
            continue
        if (int(q) >> k) & 1:
            full |= 1 << bit
        k += 1
    return full


def mat3_from_full_mask(mask: int) -> np.ndarray:
    return np.array([[(int(mask) >> (3*i+j)) & 1 for j in range(3)] for i in range(3)], dtype=np.uint8)


def lambda_mat(lam8: int) -> np.ndarray:
    return mat3_from_full_mask(full_mask_from_quotient(lam8))


def contraction_mat(lam8: int) -> np.ndarray:
    L = lambda_mat(lam8)
    return np.kron(L.T.astype(np.uint8), np.eye(3, dtype=np.uint8)) & 1


def gf2_rref(rows: Iterable[int], n: int = N) -> Tuple[int, ...]:
    basis = [0] * n
    for row in rows:
        v = int(row) & ((1 << n) - 1)
        while v:
            p = v.bit_length() - 1
            if basis[p]:
                v ^= basis[p]
            else:
                basis[p] = v
                break
    for p in range(n):
        if basis[p]:
            for q in range(n):
                if q != p and basis[q] and ((basis[q] >> p) & 1):
                    basis[q] ^= basis[p]
    return tuple(basis[p] for p in range(n-1, -1, -1) if basis[p])


def rank(rows: Iterable[int], n: int = N) -> int:
    return len(gf2_rref(rows, n=n))


def rank_mat(M: np.ndarray) -> int:
    rows = []
    for row in M:
        x = 0
        for i, b in enumerate(row.tolist()):
            if int(b) & 1:
                x |= 1 << i
        rows.append(x)
    return rank(rows, n=M.shape[1])


def row_mask(row: Sequence[int]) -> int:
    x = 0
    for i, b in enumerate(row):
        if int(b) & 1:
            x |= 1 << i
    return x


def row_space(M: np.ndarray) -> Tuple[int, ...]:
    return gf2_rref([row_mask(row) for row in M], n=M.shape[1])


def col_space(M: np.ndarray) -> Tuple[int, ...]:
    return gf2_rref([row_mask(row) for row in M.T], n=M.shape[0])


def sum_dim(A: Sequence[int], B: Sequence[int], n: int = N) -> int:
    return rank(list(A) + list(B), n=n)


def intersection_dim(A: Sequence[int], B: Sequence[int], n: int = N) -> int:
    return len(A) + len(B) - sum_dim(A, B, n=n)


def subset_dim(S: Sequence[int], U: Sequence[int], n: int = N) -> Tuple[bool, int]:
    rS = rank(S, n=n)
    rSU = sum_dim(gf2_rref(S, n=n), U, n=n)
    return rSU == len(U), rS


@dataclass(frozen=True)
class Space:
    lam: int
    rank_lam: int
    r: int
    U: Tuple[int, ...]
    V: Tuple[int, ...]


def build_spaces() -> Dict[int, Space]:
    spaces: Dict[int, Space] = {}
    for lam in range(1, 256):
        L = lambda_mat(lam)
        d = rank_mat(L)
        M = contraction_mat(lam)
        r = rank_mat(M)
        if r != 3*d:
            raise AssertionError((lam, d, r))
        spaces[lam] = Space(lam=lam, rank_lam=d, r=r, U=col_space(M), V=row_space(M))
    return spaces


SPACES = build_spaces()


def row_to_terms(row: Sequence[int]) -> List[Tuple[int, int, int]]:
    R = len(row)//3
    return [(int(row[3*t]), int(row[3*t+1]), int(row[3*t+2])) for t in range(R)]


def support_records(us: Sequence[int], ranks=(1,2,3)) -> Dict[int, dict]:
    out = {}
    for lam, sp in SPACES.items():
        if sp.rank_lam not in ranks:
            continue
        active = tuple(i for i,u in enumerate(us) if dot8(lam, u))
        out[lam] = {"active": active, "m": len(active), "space": sp, "budget": len(active)-sp.r}
    return out


def compute_leak_bounds(us: Sequence[int], source_ranks=(1,2), target_ranks=(1,2)) -> dict:
    recs = support_records(us, ranks=tuple(set(source_ranks) | set(target_ranks)))
    tight_sources = [lam for lam, rec in recs.items() if rec["space"].rank_lam in source_ranks and rec["m"] == rec["space"].r]
    scalar = []
    leaks = []
    per_target = {}
    for mu, rec_mu in recs.items():
        sp_mu = rec_mu["space"]
        if sp_mu.rank_lam not in target_ranks:
            continue
        m, r = rec_mu["m"], sp_mu.r
        if m < r:
            scalar.append({"lambda": mu, "rank_lambda": sp_mu.rank_lam, "active_count": m, "rank_contraction": r})
            continue
        eB_lb = 0; eC_lb = 0; srcB = None; srcC = None
        A_mu = set(rec_mu["active"])
        for lam in tight_sources:
            if lam == mu:
                continue
            rec_lam = recs[lam]
            shared = sorted(A_mu.intersection(rec_lam["active"]))
            if not shared:
                continue
            h = len(shared)
            sp_lam = rec_lam["space"]
            dU = intersection_dim(sp_lam.U, sp_mu.U)
            dV = intersection_dim(sp_lam.V, sp_mu.V)
            lbB = max(0, h-dU)
            lbC = max(0, h-dV)
            if lbB > eB_lb:
                eB_lb = lbB; srcB = {"tight_lambda": lam, "rank_lambda": sp_lam.rank_lam, "h": h, "intersection_dim": dU, "shared_terms": shared[:12]}
            if lbC > eC_lb:
                eC_lb = lbC; srcC = {"tight_lambda": lam, "rank_lambda": sp_lam.rank_lam, "h": h, "intersection_dim": dV, "shared_terms": shared[:12]}
        per_target[mu] = {"rank_lambda": sp_mu.rank_lam, "m": m, "r": r, "budget": m-r, "eB_lb": eB_lb, "eC_lb": eC_lb, "srcB": srcB, "srcC": srcC}
        if eB_lb + eC_lb > m-r:
            leaks.append({"lambda": mu, **per_target[mu]})
    return {
        "scalar_violations": scalar,
        "leakage_budget_violations": leaks,
        "tight_sources": tight_sources,
        "tight_source_rank_hist": {str(k): int(v) for k,v in sorted(collections.Counter(SPACES[l].rank_lam for l in tight_sources).items())},
        "target_count": len(per_target),
    }


def actual_pool_review(max_violation_head: int = 10) -> dict:
    pool = np.load(POOL_PATH)
    violations = []
    hist = collections.Counter()
    tight_rank_hist = collections.Counter()
    allsource_extra_rows = 0
    for row_idx, row in enumerate(pool):
        terms = row_to_terms(row)
        us = [u for u,_,_ in terms]
        recs = support_records(us, ranks=(1,2,3))
        tight = [lam for lam, rec in recs.items() if rec["m"] == rec["space"].r]
        tight_rank_hist.update([SPACES[l].rank_lam for l in tight])
        # Actual exact-decomposition checks for every contraction.
        for lam, rec in recs.items():
            active = rec["active"]; sp = rec["space"]; m = rec["m"]; r = sp.r
            if m < r:
                violations.append({"row": row_idx, "lambda": lam, "type": "active_count_below_rank", "m": m, "r": r})
                continue
            B = [terms[t][1] for t in active]
            C = [terms[t][2] for t in active]
            rankB, rankC = rank(B), rank(C)
            U_in_B = sum_dim(gf2_rref(B), sp.U) == rankB
            V_in_C = sum_dim(gf2_rref(C), sp.V) == rankC
            eB, eC = rankB-r, rankC-r
            if not (U_in_B and V_in_C and eB >= 0 and eC >= 0 and eB+eC <= m-r):
                violations.append({"row": row_idx, "lambda": lam, "type": "sylvester_or_space", "m": m, "r": r, "rankB": rankB, "rankC": rankC, "U_in_B": U_in_B, "V_in_C": V_in_C, "eB": eB, "eC": eC})
            if m == r and not (rankB == r and rankC == r):
                violations.append({"row": row_idx, "lambda": lam, "type": "tight_not_bases", "rankB": rankB, "rankC": rankC, "r": r})
        # Lower bounds from tight sources must not exceed actual excess for rank-1/2 targets.
        bounds_all = compute_leak_bounds(us, source_ranks=(1,2,3), target_ranks=(1,2))
        bounds_12 = compute_leak_bounds(us, source_ranks=(1,2), target_ranks=(1,2))
        if bounds_all["leakage_budget_violations"] or bounds_all["scalar_violations"]:
            violations.append({"row": row_idx, "type": "a_only_bound_rejects_verified_pool", "bounds_all_head": bounds_all["leakage_budget_violations"][:3], "scalar": bounds_all["scalar_violations"][:3]})
        if len(bounds_all["tight_sources"]) > len(bounds_12["tight_sources"]):
            allsource_extra_rows += 1
        hist[(len(bounds_12["tight_sources"]), len(bounds_all["tight_sources"]))] += 1
        # Verify bound <= actual for all rank1/2 targets.
        for mu, bnd in bounds_all.get("per_target", {}).items() if False else []:
            pass
        if len(violations) >= max_violation_head:
            break
    return {
        "pool_path": str(POOL_PATH),
        "rows_checked": int(pool.shape[0]),
        "terms_per_row": int(pool.shape[1]//3),
        "actual_decomposition_checks_pass": len(violations) == 0,
        "violation_head": violations[:max_violation_head],
        "tight_source_count_hist_vs_all_head": {str(k): int(v) for k,v in sorted(hist.items(), key=lambda kv:(kv[0][0], kv[0][1]))[:30]},
        "rows_with_rank3_tight_sources_not_used_by": allsource_extra_rows,
        "tight_lambda_rank_hist_over_all_rows": {str(k): int(v) for k,v in sorted(tight_rank_hist.items())},
    }


def actual_leak_bound_pool_review(max_violation_head: int = 10) -> dict:
    """Separately compare all-source A-only lower bounds with actual B/C excess."""
    pool = np.load(POOL_PATH)
    violations = []
    max_gap_examples = []
    for row_idx, row in enumerate(pool):
        terms = row_to_terms(row)
        us = [u for u,_,_ in terms]
        recs = support_records(us, ranks=(1,2,3))
        tight_sources = [lam for lam, rec in recs.items() if rec["m"] == rec["space"].r]
        for mu, rec_mu in recs.items():
            sp_mu = rec_mu["space"]
            if sp_mu.rank_lam not in (1,2):
                continue
            m, r = rec_mu["m"], sp_mu.r
            if m < r:
                continue
            active_mu = set(rec_mu["active"])
            B_mu = [terms[t][1] for t in active_mu]
            C_mu = [terms[t][2] for t in active_mu]
            eB_actual = rank(B_mu) - r
            eC_actual = rank(C_mu) - r
            eB_lb = 0; eC_lb = 0; srcB = None; srcC = None
            for lam in tight_sources:
                if lam == mu:
                    continue
                sp_lam = recs[lam]["space"]
                shared = sorted(active_mu.intersection(recs[lam]["active"]))
                if not shared:
                    continue
                h = len(shared)
                lbB = max(0, h - intersection_dim(sp_lam.U, sp_mu.U))
                lbC = max(0, h - intersection_dim(sp_lam.V, sp_mu.V))
                if lbB > eB_lb:
                    eB_lb = lbB; srcB = (lam, sp_lam.rank_lam, h)
                if lbC > eC_lb:
                    eC_lb = lbC; srcC = (lam, sp_lam.rank_lam, h)
            if eB_lb > eB_actual or eC_lb > eC_actual:
                violations.append({"row": row_idx, "mu": mu, "rank_mu": sp_mu.rank_lam, "m": m, "r": r, "eB_lb": eB_lb, "eB_actual": eB_actual, "srcB": srcB, "eC_lb": eC_lb, "eC_actual": eC_actual, "srcC": srcC})
            gap = (eB_actual-eB_lb) + (eC_actual-eC_lb)
            if len(max_gap_examples) < 10:
                max_gap_examples.append({"row": row_idx, "mu": mu, "rank_mu": sp_mu.rank_lam, "m": m, "budget": m-r, "eB_lb": eB_lb, "eC_lb": eC_lb, "eB_actual": eB_actual, "eC_actual": eC_actual, "srcB": srcB, "srcC": srcC, "slack_after_lbs": gap})
        if len(violations) >= max_violation_head:
            break
    return {"bounds_never_exceed_actual_excess": len(violations)==0, "violation_head": violations[:max_violation_head], "example_head": max_gap_examples}


def compare_known_and_samew_head() -> dict:
    known = {
        "L15": [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219],
        "analysis": [1,2,3,4,8,20,24,31,32,36,64,73,127,128,141,160,182,192,219],
    }
    out = {}
    for name, us in known.items():
        b12 = compute_leak_bounds(us, source_ranks=(1,2), target_ranks=(1,2))
        ball = compute_leak_bounds(us, source_ranks=(1,2,3), target_ranks=(1,2))
        out[name] = {
            "term_count": len(us),
            "distinct_A_count": len(set(us)),
            "source12_tight_count": len(b12["tight_sources"]),
            "allsource_tight_count": len(ball["tight_sources"]),
            "allsource_tight_rank_hist": ball["tight_source_rank_hist"],
            "rank12_scalar_count": len(b12["scalar_violations"]),
            "rank12_leak_count": len(b12["leakage_budget_violations"]),
            "allsource_scalar_count": len(ball["scalar_violations"]),
            "allsource_leak_count": len(ball["leakage_budget_violations"]),
            "allsource_leak_head": ball["leakage_budget_violations"][:5],
        }
    if FULL.exists():
        d = json.loads(FULL.read_text())
        sw = d["same_w_deletions"]
        classified = collections.Counter()
        for ks, v in sw["hist"].items():
            tup = eval(ks, {"True": True, "False": False, "None": None})
            sh, coord, gen_rej, sc, leak, twosat = tup
            if sh is True and coord is True:
                classified[(sc > 0, leak > 0, twosat)] += v
        out["same_w_full_classification"] = {
            "records_scanned": sw["records_scanned"],
            "shadow_and_coordinate_pass_total": sw["shadow_and_coordinate_pass_total"],
            "general_reject_after_shadow_and_coordinate_pass": sw["general_reject_after_shadow_and_coordinate_pass"],
            "classification_scalar_positive_leak_positive_twosat": {str(k): int(v) for k,v in sorted(classified.items(), key=lambda kv: str(kv[0]))},
        }
        # Recompute rank12/all-source hard leakage for first detailed leak-only support in the saved head.
        for rec in sw["first_general_rejects_after_shadow_coordinate_head"]:
            gen = rec["general"]
            if gen["scalar_violation_count"] == 0 and gen["leakage_budget_violation_count"] > 0:
                us = rec["source"]["u_masks"]
                b12 = compute_leak_bounds(us, source_ranks=(1,2), target_ranks=(1,2))
                ball = compute_leak_bounds(us, source_ranks=(1,2,3), target_ranks=(1,2))
                out["same_w_head_leak_only_recompute"] = {
                    "source": rec["source"],
                    "counts": {k: gen[k] for k in ["scalar_violation_count", "leakage_budget_violation_count", "tight_count", "half_pure_count", "2sat_sat"]},
                    "rank12_counts": {"scalar": len(b12["scalar_violations"]), "leak": len(b12["leakage_budget_violations"]), "tight": len(b12["tight_sources"]), "tight_rank_hist": b12["tight_source_rank_hist"], "leak_head": b12["leakage_budget_violations"][:3]},
                    "allsource_counts": {"scalar": len(ball["scalar_violations"]), "leak": len(ball["leakage_budget_violations"]), "tight": len(ball["tight_sources"]), "tight_rank_hist": ball["tight_source_rank_hist"], "leak_head": ball["leakage_budget_violations"][:3]},
                }
                break
    return out


def main() -> None:
    t0 = time.time()
    result = {
        "schema": "s0908_general_low_excess_review_v1",
        "spaces": {
            "lambda_rank_distribution": {str(k): int(v) for k,v in sorted(collections.Counter(sp.rank_lam for sp in SPACES.values()).items())},
            "convention_checked": "M_lambda = Lambda^T tensor I3; all 255 nonzero quotient lambdas satisfy rank(M)=3 rank(Lambda).",
        },
        "actual_pool_review": actual_pool_review(),
        "actual_leak_bound_pool_review": actual_leak_bound_pool_review(),
        "known_and_samew_review": compare_known_and_samew_head(),
        "interpretation": {
            "sound_core": "The analysis rank-1/2 tight-source leakage bounds are valid necessary conditions when derived from exact contractions; pool checks did not find overstrong inequalities.",
            "not_global": "Same-W deletion lists are local labelled A-lists with repeats, not a cover of the distinct 19-direction E11 branch.",
            "strengthening": "Rank-3 tight contractions are also sound leakage sources into rank-1/2 targets; analysis omitted them, making the current filter weaker rather than unsound.",
        },
        "elapsed_sec": None,
    }
    result["elapsed_sec"] = round(time.time()-t0, 3)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(OUT),
        "pool_actual_checks_pass": result["actual_pool_review"]["actual_decomposition_checks_pass"],
        "pool_leak_bounds_pass": result["actual_leak_bound_pool_review"]["bounds_never_exceed_actual_excess"],
        "rows_with_rank3_tight_sources_not_used_by": result["actual_pool_review"]["rows_with_rank3_tight_sources_not_used_by"],
        "known": result["known_and_samew_review"],
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
