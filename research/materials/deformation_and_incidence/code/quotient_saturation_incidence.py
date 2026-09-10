#!/usr/bin/env python3
"""Self-contained codimension-one saturation analysis for quotient tensors.

Mathematical content (no Wang LUT needed):

Let Q_p in F2^{8x9x9} be the quotient of T<3,3,3> by the line spanned by an
A-factor pivot p.  Suppose Q_p = sum_{t=1}^{n} u_t (x) v_t (x) w_t with u_t in
F2^8.  For a dual functional lambda in F2^8\{0} set

    M_lambda = sum_s lambda_s Q_p[s]  in F2^{9x9},   r_lambda = rank M_lambda.

Contracting the decomposition with lambda gives

    M_lambda = sum_{t : lambda . u_t = 1} v_t w_t^T,

so by rank subadditivity

    #active(lambda) = #{t : lambda . u_t = 1} >= r_lambda.                (1)

With multiplicities m_q = #{t : u_t = q} and sum_q m_q = n this is exactly the
codimension-one occupation inequality

    sum_{q in ker lambda} m_q <= n - r_lambda.                            (2)

Hence the 255 codim-1 Wang rows are elementary rank facts, not certificate
content.  We call lambda TIGHT for a support when equality holds in (1); then
the active terms are a MINIMAL rank decomposition of M_lambda, which is the
hypothesis of the independent-verification-record filter.

Incidence counting.  For a rank value r let
    K_r = #{lambda : r_lambda = r},   N_r(q) = #{lambda : r_lambda = r, lambda.q = 1}.
Summing (1) over all lambda of rank r,
    sum_{lambda : r_lambda=r} #active(lambda) = sum_q m_q N_r(q),
while each non-tight lambda contributes at least r+1.  Therefore

    #tight_r >= (r+1) K_r - sum_q m_q N_r(q).                             (3)

Maximizing sum_q m_q N_r(q) over the polytope {m >= 0, sum m = n, (2)} gives an
UNCONDITIONAL lower bound on the number of tight rank-r contractions that every
n-term quotient decomposition must have.  The LP relaxation suffices (it is an
upper bound on the integer maximum, hence a valid lower bound in (3)).

Outputs a JSON report; optionally checks a given support.
"""
from __future__ import annotations

import argparse
import json
import time
from collections import Counter
from pathlib import Path

import numpy as np


def full_tensor() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3 * i + j, 3 * j + k, 3 * i + k] = 1
    return T


def quotient_tensor(pivot: int) -> np.ndarray:
    T = full_tensor()
    h = int(pivot).bit_length() - 1
    Q = np.zeros((8, 9, 9), dtype=np.uint8)
    for a_bit in range(9):
        qa = 1 << a_bit
        if (qa >> h) & 1:
            qa ^= int(pivot)
        low = qa & ((1 << h) - 1)
        high = (qa >> (h + 1)) << h
        q_idx = low | high
        if q_idx:
            for qb in range(8):
                if (q_idx >> qb) & 1:
                    Q[qb] ^= T[a_bit]
    return Q


def mat_rank(M: np.ndarray) -> int:
    A = (M.copy() & 1).astype(np.uint8)
    m, n = A.shape
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i, c]:
                piv = i
                break
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


def codim1_ranks(Q: np.ndarray) -> dict[int, int]:
    out = {}
    for lam in range(1, 256):
        M = np.zeros((9, 9), dtype=np.uint8)
        for s in range(8):
            if (lam >> s) & 1:
                M ^= Q[s]
        out[lam] = mat_rank(M)
    return out


def lp_max_incidence(ranks: dict[int, int], target_r: int, n: int) -> dict:
    """Maximize sum_q m_q N_r(q) over LP relaxation of {m>=0, sum m=n, codim-1 caps}."""
    from scipy.optimize import linprog

    pts = list(range(1, 256))
    idx = {q: i for i, q in enumerate(pts)}
    Nr = np.zeros(len(pts))
    for lam, r in ranks.items():
        if r != target_r:
            continue
        for q in pts:
            if (lam & q).bit_count() & 1:
                Nr[idx[q]] += 1
    # constraints: for each lambda, sum_{q in ker lambda} m_q <= n - r_lambda
    A_ub = []
    b_ub = []
    for lam, r in ranks.items():
        row = np.zeros(len(pts))
        for q in pts:
            if not ((lam & q).bit_count() & 1):
                row[idx[q]] = 1.0
        A_ub.append(row)
        b_ub.append(float(n - r))
    A_eq = [np.ones(len(pts))]
    b_eq = [float(n)]
    res = linprog(-Nr, A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                  A_eq=np.array(A_eq), b_eq=np.array(b_eq),
                  bounds=[(0, None)] * len(pts), method="highs")
    return {
        "target_rank": target_r,
        "K_r": int(sum(1 for r in ranks.values() if r == target_r)),
        "max_N_per_point": float(Nr.max()),
        "lp_status": res.status,
        "lp_success": bool(res.success),
        "lp_max_incidence": float(-res.fun) if res.success else None,
        "naive_bound_n_times_maxN": float(n * Nr.max()),
    }


def forced_tight_bound(ranks: dict[int, int], n: int) -> dict:
    out = {"per_rank": [], "n": n}
    rank_hist = Counter(ranks.values())
    out["codim1_rank_hist"] = dict(sorted(rank_hist.items()))
    total_forced = 0
    for r in sorted(rank_hist):
        if r == 0:
            continue
        info = lp_max_incidence(ranks, r, n)
        Kr = info["K_r"]
        lp = info["lp_max_incidence"]
        naive = info["naive_bound_n_times_maxN"]
        best_upper = lp if lp is not None else naive
        forced_lp = (r + 1) * Kr - best_upper
        forced_naive = (r + 1) * Kr - naive
        info["forced_tight_lower_bound_lp"] = forced_lp
        info["forced_tight_lower_bound_naive"] = forced_naive
        out["per_rank"].append(info)
        if forced_lp > 0:
            total_forced += forced_lp
    out["total_forced_tight_lower_bound"] = total_forced
    return out


def support_tight_profile(Q: np.ndarray, ranks: dict[int, int], support: list[int]) -> dict:
    tight = []
    slack_hist = Counter()
    for lam in range(1, 256):
        active = sum(1 for u in support if ((lam & u).bit_count() & 1))
        r = ranks[lam]
        slack = active - r
        slack_hist[slack] += 1
        if slack == 0 and r > 0:
            tight.append({"lambda": lam, "rank": r})
    return {
        "support": support,
        "support_size": len(support),
        "tight_count": len(tight),
        "tight_rank_hist": dict(sorted(Counter(t["rank"] for t in tight).items())),
        "slack_hist": dict(sorted(slack_hist.items())),
        "negative_slack_rows": [t for t in tight if t["rank"] < 0],
        "infeasible_rows": sum(1 for lam in range(1, 256)
                               if sum(1 for u in support if ((lam & u).bit_count() & 1)) < ranks[lam]),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot", type=int, required=True)
    ap.add_argument("--pivot-name", default="")
    ap.add_argument("--n", type=int, default=19)
    ap.add_argument("--support", default="")
    ap.add_argument("--lut", default="")
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()

    t0 = time.time()
    Q = quotient_tensor(args.pivot)
    ranks = codim1_ranks(Q)
    result = {
        "schema": "quotient_saturation_incidence_v1",
        "pivot": args.pivot,
        "pivot_name": args.pivot_name,
        "n": args.n,
        "quotient_nnz": int(Q.sum()),
        "quotient_slice_ranks": [mat_rank(Q[s]) for s in range(8)],
    }
    result.update(forced_tight_bound(ranks, args.n))

    if args.support:
        p = Path(args.support)
        if p.exists():
            data = json.loads(p.read_text())
            sup = None
            if isinstance(data, list):
                sup = [int(x) for x in data]
            else:
                for key in ["support", "solution", "best_support", "a_multiset"]:
                    if key in data:
                        sup = [int(x) for x in data[key]]
                        break
                if sup is None and "rounds" in data:
                    for r in reversed(data["rounds"]):
                        if r.get("fully_admissible") and r.get("solution"):
                            sup = [int(x) for x in r["solution"]]
                            break
        else:
            sup = [int(x) for x in args.support.replace(" ", ",").split(",") if x.strip()]
        result["support_profile"] = support_tight_profile(Q, ranks, sup)

    result["elapsed_sec"] = time.time() - t0
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "per_rank"}, indent=2, sort_keys=True))
    print("\nper_rank:")
    for info in result["per_rank"]:
        print(json.dumps(info, sort_keys=True))
    print(f"\nSaved {args.out}")


if __name__ == "__main__":
    main()
