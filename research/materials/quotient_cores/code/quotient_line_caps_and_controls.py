#!/usr/bin/env python3
"""Line-cap and quotient-control diagnostics for three pivot quotients.

This script addresses two soundness issues in the three-orbit quotient route:
  1. For each pivot p, compute the cap of every quotient line at target n=19,
     i.e. every 2-dimensional original subspace containing p. This determines
     whether distinct-only enumeration covers all multisets.
  2. Transform a verified full rank-23 decomposition so that a rank-2 or rank-3
     A-factor becomes the chosen pivot, project the remaining terms, and verify
     the resulting rank-22 quotient tensor decomposition and Wang admissibility
     at n=22.

All arithmetic is over F2. Bit order is row-major 3*i+j.
"""
from __future__ import annotations
import argparse
import json
import os
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, List, Tuple, Dict, Optional

import numpy as np

SCRIPT_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
SESSION = SCRIPT_DIR.parent.parent
S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import rref_basis, pack_basis, unpack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore
from extract_known_supports import parse_rank23_txt  # type: ignore

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
RANK23_SRC = Path("data/flip_cpd_inspect/src/khoruzhii-flip-cpd-9eeb17f/data/schemes_paper/gg-333-rank23-rec-0-0-0-z.txt")
OUTDIR = SESSION / "workspace/data/wang_native/three_orbit_controls"

PIVOTS = {
    "rank1": 1,
    "rank2": 17,
    "rank3": 273,
}


def bits_to_mat(mask: int) -> np.ndarray:
    return np.array([[(mask >> (3*i+j)) & 1 for j in range(3)] for i in range(3)], dtype=np.uint8)


def mat_to_bits(M: np.ndarray) -> int:
    M = np.asarray(M, dtype=np.uint8) & 1
    out = 0
    for i in range(3):
        for j in range(3):
            if int(M[i, j]) & 1:
                out |= 1 << (3*i+j)
    return out


def gf2_rank_mat(M: np.ndarray) -> int:
    A = (np.asarray(M, dtype=np.uint8) & 1).copy()
    m, n = A.shape
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i, c]:
                piv = i; break
        if piv is None:
            continue
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for i in range(m):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        r += 1
        if r == m:
            break
    return int(r)


def gf2_inv(A: np.ndarray) -> np.ndarray:
    A = (np.asarray(A, dtype=np.uint8) & 1).copy()
    n = A.shape[0]
    aug = np.concatenate([A, np.eye(n, dtype=np.uint8)], axis=1)
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, n):
            if aug[i, c]:
                piv = i; break
        if piv is None:
            raise ValueError("singular")
        if piv != r:
            aug[[r, piv]] = aug[[piv, r]]
        for i in range(n):
            if i != r and aug[i, c]:
                aug[i] ^= aug[r]
        r += 1
    return aug[:, n:]


def gl3() -> List[np.ndarray]:
    out = []
    for x in range(1 << 9):
        M = bits_to_mat(x)
        if gf2_rank_mat(M) == 3:
            out.append(M)
    assert len(out) == 168
    return out


def transform_term(term: Tuple[int,int,int], P: np.ndarray, Q: np.ndarray, R: Optional[np.ndarray]=None) -> Tuple[int,int,int]:
    """Apply MM tensor stabilizer with A'=P^T A Q^{-T}, B'=Q^T B R^{-T}, C'=P^{-1} C R.

    We use R=I by default. This convention matches the verified E11 quotient
    stabilizer action on the A factor.
    """
    if R is None:
        R = np.eye(3, dtype=np.uint8)
    Pinv = gf2_inv(P)
    Qinv = gf2_inv(Q)
    Rinv = gf2_inv(R)
    A = bits_to_mat(term[0])
    B = bits_to_mat(term[1])
    C = bits_to_mat(term[2])
    A2 = (P.T @ A @ Qinv.T) & 1  # P^T A Q^{-T}
    B2 = (Q.T @ B @ Rinv.T) & 1  # Q^T B R^{-T}
    C2 = (Pinv @ C @ R) & 1      # P^{-1} C R
    return mat_to_bits(A2), mat_to_bits(B2), mat_to_bits(C2)


def build_t333() -> np.ndarray:
    T = np.zeros((9,9,9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] ^= 1
    return T


def vec(mask: int, n: int) -> np.ndarray:
    return np.array([(mask >> i) & 1 for i in range(n)], dtype=np.uint8)


def recon_full(terms: List[Tuple[int,int,int]]) -> np.ndarray:
    T = np.zeros((9,9,9), dtype=np.uint8)
    for a,b,c in terms:
        T ^= (vec(a,9).reshape(9,1,1) * vec(b,9).reshape(1,9,1) * vec(c,9).reshape(1,1,9)).astype(np.uint8)
    return T


def quotient_project(a: int, pivot: int) -> int:
    if a == 0 or a == pivot:
        return 0
    h = pivot.bit_length() - 1
    if (a >> h) & 1:
        a ^= pivot
    low = a & ((1 << h) - 1)
    high = (a >> (h + 1)) << h
    return low | high


def quotient_tensor(pivot: int) -> np.ndarray:
    T = build_t333()
    Q = np.zeros((8,9,9), dtype=np.uint8)
    for ai in range(9):
        q = quotient_project(1 << ai, pivot)
        if q == 0:
            continue
        # The image of an original coordinate vector can be a non-basis quotient
        # vector when the pivot has several bits (e.g. pivot=I_3).  Since the
        # quotient map is linear, add the original slice to every quotient
        # coordinate appearing in q.
        m = q
        while m:
            lb = m & -m
            qi = lb.bit_length() - 1
            Q[qi] ^= T[ai]
            m ^= lb
    return Q


def recon_quotient(terms: List[Tuple[int,int,int]], pivot: int, drop_zero: bool=True) -> np.ndarray:
    T = np.zeros((8,9,9), dtype=np.uint8)
    for a,b,c in terms:
        q = quotient_project(a, pivot)
        if q == 0:
            if drop_zero:
                continue
            else:
                raise AssertionError("zero quotient term")
        T ^= (vec(q,8).reshape(8,1,1) * vec(b,9).reshape(1,9,1) * vec(c,9).reshape(1,1,9)).astype(np.uint8)
    return T


def in_span(point: int, basis_vecs: Iterable[int]) -> bool:
    x = point
    for b in sorted([int(v) for v in basis_vecs if int(v)], key=lambda v: -v.bit_length()):
        if x == 0:
            return True
        hb = b.bit_length() - 1
        if (x >> hb) & 1:
            x ^= b
    return x == 0


def rref_key_from_vecs(vecs: Iterable[int]) -> int:
    return int(pack_basis(rref_basis(tuple(int(v) for v in vecs if int(v)))))


def all_subspace_points_from_basis(basis: List[int]) -> List[int]:
    pts = []
    d = len(basis)
    for m in range(1, 1 << d):
        x = 0
        for i,b in enumerate(basis):
            if (m >> i) & 1:
                x ^= b
        pts.append(x)
    return pts


def line_caps_for_pivot(lut: Dict[int,int], pivot: int, target: int=19) -> Dict:
    records = []
    cap_hist = Counter(); lb_hist = Counter(); rank_hist = Counter()
    repeatable = []
    for q in range(1, 256):
        # Lift quotient q to a 9-bit representative with pivot's high bit absent.
        h = pivot.bit_length() - 1
        low = q & ((1 << h) - 1)
        high = (q >> h) << (h + 1)
        lift = low | high
        key = rref_key_from_vecs([pivot, lift])
        lb = int(lut[key])
        cap = target - lb
        full_rank = gf2_rank_mat(bits_to_mat(lift))
        rec = {"q": q, "lift": lift, "lb": lb, "cap": cap, "lift_matrix_rank": full_rank}
        records.append(rec)
        cap_hist[cap] += 1; lb_hist[lb] += 1; rank_hist[full_rank] += 1
        if cap >= 2:
            repeatable.append(rec)
    return {
        "pivot": pivot,
        "target": target,
        "line_count": len(records),
        "all_lb_ge_18": all(r["lb"] >= 18 for r in records),
        "all_cap_le_1": all(r["cap"] <= 1 for r in records),
        "cap_hist": dict(sorted((int(k), int(v)) for k,v in cap_hist.items())),
        "lb_hist": dict(sorted((int(k), int(v)) for k,v in lb_hist.items())),
        "lift_rank_hist": dict(sorted((int(k), int(v)) for k,v in rank_hist.items())),
        "repeatable_count": len(repeatable),
        "repeatable": repeatable,
    }


def wang_violations_for_quotient_multiset(lut: Dict[int,int], pivot: int, q_multiset: List[int], target: int) -> Dict:
    """Check projected multiset against every LUT row containing pivot at quotient target."""
    violations = []
    binding = 0; total = 0
    max_excess = 0
    cap_hist = Counter()
    for key9, lb0 in lut.items():
        key9_int = int(key9)
        basis = list(unpack_basis(key9_int))
        if not in_span(pivot, basis):
            continue
        total += 1
        lb = int(lb0)
        cap = target - lb
        if cap < 0:
            # impossible row; any support violates
            cnt = len(q_multiset)
        else:
            # Project the original subspace into quotient and count nonzero q in it.
            qpts = set()
            for x in all_subspace_points_from_basis(basis):
                q = quotient_project(x, pivot)
                if q:
                    qpts.add(q)
            cnt = sum(1 for q in q_multiset if q in qpts)
        if 0 <= cap < target:
            binding += 1
            cap_hist[cap] += 1
        if cnt > cap:
            excess = cnt - cap
            max_excess = max(max_excess, excess)
            if len(violations) < 20:
                violations.append({"key": key9_int, "lb": lb, "cap": cap, "count": cnt, "excess": excess, "dim9": len(basis), "dim8": len(basis)-1})
    return {
        "total_containing_rows": total,
        "binding_rows": binding,
        "cap_hist_binding": dict(sorted((int(k), int(v)) for k,v in cap_hist.items())),
        "violations": len(violations),
        "violation_head": violations,
        "max_excess_seen_head_limited": max_excess,
        "passed": len(violations) == 0,
        "note": "violations count is head-limited; passed is exact only if zero head violations after full scan",
    }


def wang_check_exact(lut: Dict[int,int], pivot: int, q_multiset: List[int], target: int) -> Dict:
    # Same as above but exact violation count and excess hist; optimize by recomputing qpts per row only once.
    violations_head = []
    viol_count = 0; excess_total = 0; max_excess = 0; total = 0; binding = 0
    cap_hist = Counter(); dim_hist = Counter()
    for key9, lb0 in lut.items():
        key9_int = int(key9)
        basis = list(unpack_basis(key9_int))
        if not in_span(pivot, basis):
            continue
        total += 1
        lb = int(lb0); cap = target - lb; dim8 = len(basis)-1
        if 0 <= cap < target:
            binding += 1; cap_hist[cap] += 1; dim_hist[dim8] += 1
        qpts = set()
        for x in all_subspace_points_from_basis(basis):
            q = quotient_project(x, pivot)
            if q:
                qpts.add(q)
        cnt = sum(1 for q in q_multiset if q in qpts)
        if cnt > cap:
            viol_count += 1
            excess = cnt - cap
            excess_total += excess
            max_excess = max(max_excess, excess)
            if len(violations_head) < 20:
                violations_head.append({"key": key9_int, "lb": lb, "cap": cap, "count": cnt, "excess": excess, "dim9": len(basis), "dim8": dim8})
    return {
        "passed": viol_count == 0,
        "violation_count": viol_count,
        "excess_total": excess_total,
        "max_excess": max_excess,
        "total_containing_rows": total,
        "binding_rows": binding,
        "cap_hist_binding": dict(sorted((int(k), int(v)) for k,v in cap_hist.items())),
        "dim_hist_binding": dict(sorted((int(k), int(v)) for k,v in dim_hist.items())),
        "violation_head": violations_head,
    }


def find_mapping(term_a: int, target: int, G: List[np.ndarray]) -> Optional[Tuple[int,int,np.ndarray,np.ndarray]]:
    A = bits_to_mat(term_a)
    T = bits_to_mat(target)
    Q_invs_T = []
    # Need P^T A Q^{-T} = T. Brute force is small.
    for qi, Q in enumerate(G):
        QinvT = gf2_inv(Q).T
        AQ = (A @ QinvT) & 1
        Q_invs_T.append((qi, Q, AQ))
    for pi, P in enumerate(G):
        PT = P.T
        for qi, Q, AQ in Q_invs_T:
            if np.array_equal((PT @ AQ) & 1, T):
                return pi, qi, P, Q
    return None


def control_for_pivot(lut: Dict[int,int], pivot_name: str, pivot: int, terms: List[Tuple[int,int,int]], G: List[np.ndarray]) -> Dict:
    target_rank = gf2_rank_mat(bits_to_mat(pivot))
    candidates = []
    for idx, (a,b,c) in enumerate(terms):
        if gf2_rank_mat(bits_to_mat(a)) == target_rank:
            candidates.append((idx, a))
    records = []
    best = None
    for idx, a in candidates:
        mp = find_mapping(a, pivot, G)
        if mp is None:
            records.append({"term_index": idx, "a": a, "mapping_found": False})
            continue
        pi, qi, P, Q = mp
        trans_terms = [transform_term(t, P, Q) for t in terms]
        full_ok = np.array_equal(recon_full(trans_terms), build_t333())
        transformed_a = trans_terms[idx][0]
        zero_terms = [j for j,t in enumerate(trans_terms) if quotient_project(t[0], pivot) == 0]
        q_terms = [(quotient_project(t[0], pivot), t[1], t[2]) for t in trans_terms if quotient_project(t[0], pivot) != 0]
        q_multiset = [q for q,_,_ in q_terms]
        q_recon_ok = np.array_equal(recon_quotient(trans_terms, pivot), quotient_tensor(pivot))
        distinct_count = len(set(q_multiset))
        # Wang check can take ~10-20s; do it for controls that otherwise verify.
        wang = wang_check_exact(lut, pivot, q_multiset, target=22) if (full_ok and q_recon_ok and len(q_terms)==22) else {"passed": False, "skipped": True}
        rec = {
            "term_index": idx,
            "original_a": int(a),
            "mapping_found": True,
            "P_index": pi,
            "Q_index": qi,
            "transformed_selected_a": int(transformed_a),
            "full_tensor_still_verified": bool(full_ok),
            "zero_quotient_term_indices": zero_terms,
            "quotient_terms": len(q_terms),
            "quotient_terms_full": [[int(q), int(b), int(c)] for q, b, c in q_terms],
            "quotient_reconstruction_verified": bool(q_recon_ok),
            "quotient_a_multiset": [int(x) for x in q_multiset],
            "quotient_a_distinct_count": distinct_count,
            "quotient_a_duplicate_count": len(q_multiset) - distinct_count,
            "wang_n22": wang,
        }
        records.append(rec)
        if full_ok and q_recon_ok and len(q_terms) == 22 and wang.get("passed", False):
            # Prefer distinct controls for current distinct DFS; otherwise keep first valid multiset.
            if best is None or (rec["quotient_a_duplicate_count"] < best["quotient_a_duplicate_count"]):
                best = rec
                if rec["quotient_a_duplicate_count"] == 0:
                    break
    return {
        "pivot_name": pivot_name,
        "pivot": pivot,
        "pivot_rank": target_rank,
        "candidate_terms_with_matching_rank": len(candidates),
        "best_control": best,
        "records_head": records[:12],
        "records_count": len(records),
        "success": best is not None,
        "distinct_force_control_available": bool(best and best["quotient_a_duplicate_count"] == 0),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--skip-controls", action="store_true")
    args = ap.parse_args()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    print("Loading LUT...")
    lut, _ = load_lut(LUT_PATH)
    print(f"  LUT entries: {len(lut)}")

    line_results = {}
    for name,p in PIVOTS.items():
        line_results[name] = line_caps_for_pivot(lut, p, target=19)
        print(f"{name}: cap_hist={line_results[name]['cap_hist']}, repeatable={line_results[name]['repeatable_count']}")

    controls = {}
    if not args.skip_controls:
        terms = parse_rank23_txt(RANK23_SRC)
        terms = [(int(a),int(b),int(c)) for a,b,c in terms]
        assert np.array_equal(recon_full(terms), build_t333()), "source rank23 scheme does not verify"
        G = gl3()
        # rank1 controls already exist from E11 pool; here focus rank2/rank3, but rank1 is cheap too.
        for name in ["rank2", "rank3"]:
            print(f"Building control for {name}...")
            controls[name] = control_for_pivot(lut, name, PIVOTS[name], terms, G)
            print(f"  success={controls[name]['success']} distinct={controls[name]['distinct_force_control_available']}")
            best = controls[name].get("best_control")
            if best:
                cpath = OUTDIR / f"{name}_quotient_rank22_control.json"
                cpath.write_text(json.dumps(best, indent=2, sort_keys=True) + "\n")

    out = {
        "status": "ok",
        "source_rank23_scheme": str(RANK23_SRC),
        "line_caps_n19": line_results,
        "controls_from_rank23": controls,
    }
    out_path = OUTDIR / "quotient_line_caps_and_controls.json"
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "status": "ok",
        "out": str(out_path),
        "line_summary": {k: {"cap_hist": v["cap_hist"], "repeatable_count": v["repeatable_count"], "all_cap_le_1": v["all_cap_le_1"]} for k,v in line_results.items()},
        "control_summary": {k: {"success": v["success"], "distinct": v["distinct_force_control_available"], "dup": (v.get("best_control") or {}).get("quotient_a_duplicate_count")} for k,v in controls.items()},
    }, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
