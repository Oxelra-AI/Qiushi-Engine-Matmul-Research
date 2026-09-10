#!/usr/bin/env python3
"""3x3 block-trace shadow filter for fixed E11-core A-supports over F2.

For a fixed list of quotient A masks u_t in F2^8, relax X_t = v_t w_t^T to
arbitrary 9x9 matrices.  The E11 tensor equations are
    sum_t u_t[s] X_t = core_slice_s.
Project each 9x9 matrix to its 3x3 block-trace shadow Y_t by
    Y_t[j,i] = trace( X_t block(j,i) ) over F2.
This gives 72 linear equations in 9*r variables.

If an A-dual contraction lambda has invertible matrix Lambda (with Lambda_00=0)
and is tight, i.e. exactly 9 support terms have lambda(u_t)=1, then the dual-basis
condition implies for each active term t:
    trace(M_lambda^{-1} X_t) = 1,
where M_lambda = Lambda^T tensor I_3.  In the shadow variables, following the
corrected row-major convention used by research_record/research_record, this is
    sum_{j,i} (Lambda^{-1})[j,i] * Y_t[j,i] = 1.

Inconsistency of this small linear system rejects the fixed A-support before any
rank-one B/C solve.  Consistency is only a necessary condition.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
from typing import List, Tuple

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent


def mat_from_mask_full(x: int) -> np.ndarray:
    return np.array([[(int(x) >> (3 * i + j)) & 1 for j in range(3)] for i in range(3)], dtype=np.uint8)


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


def quotient_vec(mask: int) -> np.ndarray:
    return np.array([(int(mask) >> i) & 1 for i in range(8)], dtype=np.uint8)


def dot8(a: int, b: int) -> int:
    return (int(a) & int(b)).bit_count() & 1


def gf2_rref_aug(A: np.ndarray, b: np.ndarray | None = None) -> Tuple[int, bool]:
    A = A.copy().astype(np.uint8) & 1
    if b is not None:
        b = b.copy().astype(np.uint8).reshape(-1, 1) & 1
        M = np.concatenate([A, b], axis=1)
    else:
        M = A
    rows, cols_aug = M.shape
    cols = cols_aug - (1 if b is not None else 0)
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, c]:
                piv = i
                break
        if piv is None:
            continue
        if piv != r:
            M[[r, piv]] = M[[piv, r]]
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] ^= M[r]
        r += 1
    if b is None:
        return r, True
    inconsistent = False
    for i in range(rows):
        if not M[i, :cols].any() and M[i, cols]:
            inconsistent = True
            break
    # augmented rank = r + number of independent all-zero-left nonzero rows, which is r+1 if inconsistent after RREF
    return r + (1 if inconsistent else 0), not inconsistent


def gf2_rank(A: np.ndarray) -> int:
    return gf2_rref_aug(A, None)[0]


def gf2_rank_aug(A: np.ndarray, b: np.ndarray) -> Tuple[int, int, bool]:
    rA = gf2_rank(A)
    rAug, ok = gf2_rref_aug(A, b)
    return rA, rAug, ok


def mat_inv(M: np.ndarray) -> np.ndarray:
    A = np.concatenate([M.copy().astype(np.uint8) & 1, np.eye(3, dtype=np.uint8)], axis=1)
    r = 0
    for c in range(3):
        piv = None
        for i in range(r, 3):
            if A[i, c]:
                piv = i
                break
        if piv is None:
            raise ValueError("singular")
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for i in range(3):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        r += 1
    return A[:, 3:]


def build_core_shadow_target() -> np.ndarray:
    # target[s,j,i]=1 for A_full=(i,j)!=00; quotient s=a_full-1.
    target = np.zeros((8, 3, 3), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            a = 3 * i + j
            if a == 0:
                continue
            target[a - 1, j, i] = 1  # block row j, block col i; trace(I3)=1 mod2
    return target


def build_tensor_shadow_rows(support: List[int]) -> Tuple[List[List[int]], List[int]]:
    r = len(support)
    rows: List[List[int]] = []
    rhs: List[int] = []
    target = build_core_shadow_target()
    for s in range(8):
        for j in range(3):
            for i in range(3):
                row = [0] * (9 * r)
                for t, u in enumerate(support):
                    if (int(u) >> s) & 1:
                        row[9 * t + 3 * j + i] = 1
                rows.append(row)
                rhs.append(int(target[s, j, i]))
    return rows, rhs


def invertible_lambda_masks() -> List[int]:
    out = []
    for lam in range(1, 256):
        M = mat_from_mask_full(full_mask_from_quotient(lam))
        if gf2_rank(M) == 3:
            out.append(lam)
    return out


def tight_rank9_lambdas(support: List[int]) -> List[int]:
    out = []
    for lam in invertible_lambda_masks():
        active = sum(dot8(lam, u) for u in support)
        if active == 9:
            out.append(lam)
    return out


def lambda_coeffs(lam: int, transpose_coeff: bool = False) -> np.ndarray:
    L = mat_from_mask_full(full_mask_from_quotient(lam))
    Linv = mat_inv(L)
    C = Linv.T if transpose_coeff else Linv
    return C.astype(np.uint8) & 1


def add_trace_rows(support: List[int], lambdas: List[int], transpose_coeff: bool = False) -> Tuple[List[List[int]], List[int]]:
    r = len(support)
    rows: List[List[int]] = []
    rhs: List[int] = []
    for lam in lambdas:
        C = lambda_coeffs(lam, transpose_coeff=transpose_coeff)
        for t, u in enumerate(support):
            if dot8(lam, u):
                row = [0] * (9 * r)
                for j in range(3):
                    for i in range(3):
                        if C[j, i]:
                            row[9 * t + 3 * j + i] = 1
                rows.append(row)
                rhs.append(1)
    return rows, rhs


def analyze_support(support: List[int], subset: List[int] | None = None, min_subset: bool = False,
                    transpose_coeff: bool = False) -> dict:
    tensor_rows, tensor_rhs = build_tensor_shadow_rows(support)
    tight = tight_rank9_lambdas(support)
    lambdas = tight if subset is None else [int(x) for x in subset]
    trace_rows, trace_rhs = add_trace_rows(support, lambdas, transpose_coeff=transpose_coeff)
    A0 = np.array(tensor_rows, dtype=np.uint8)
    b0 = np.array(tensor_rhs, dtype=np.uint8)
    A = np.array(tensor_rows + trace_rows, dtype=np.uint8)
    b = np.array(tensor_rhs + trace_rhs, dtype=np.uint8)
    r0, r0a, ok0 = gf2_rank_aug(A0, b0)
    rA, rAug, ok = gf2_rank_aug(A, b)
    result = {
        "support": support,
        "support_size": len(support),
        "shadow_variables": 9 * len(support),
        "tensor_equations": len(tensor_rows),
        "tensor_rank": r0,
        "tensor_augmented_rank": r0a,
        "tensor_consistent": ok0,
        "tight_rank9_lambdas": tight,
        "tight_rank9_count": len(tight),
        "used_lambdas": lambdas,
        "trace_equations": len(trace_rows),
        "full_equations": len(tensor_rows) + len(trace_rows),
        "full_shadow_rank": rA,
        "full_shadow_augmented_rank": rAug,
        "full_shadow_consistent": ok,
        "coeff_convention": "coeff[j,i]=Lambda^{-1}[j,i]" if not transpose_coeff else "coeff[j,i]=Lambda^{-1}[i,j]",
        "inverse_mask_rank": None,
    }
    if tight:
        coeff_rows = [lambda_coeffs(lam, transpose_coeff=transpose_coeff).reshape(9) for lam in tight]
        result["inverse_mask_rank"] = gf2_rank(np.array(coeff_rows, dtype=np.uint8))
    if min_subset and tight:
        min_info = {"found": False, "size": None, "examples": [], "checked_by_size": {}, "total_inconsistent_at_min": 0}
        for k in range(1, len(tight) + 1):
            checked = 0
            bad = []
            for comb in itertools.combinations(tight, k):
                checked += 1
                tr, tb = add_trace_rows(support, list(comb), transpose_coeff=transpose_coeff)
                AA = np.array(tensor_rows + tr, dtype=np.uint8)
                bb = np.array(tensor_rhs + tb, dtype=np.uint8)
                _, _, okay = gf2_rank_aug(AA, bb)
                if not okay:
                    bad.append(list(comb))
                    if len(bad) > 20 and k != len(tight):
                        # count all at the first size only if it is reasonably small; for current L15 k=8 is fine.
                        pass
            min_info["checked_by_size"][str(k)] = checked
            if bad:
                min_info["found"] = True
                min_info["size"] = k
                min_info["examples"] = bad[:20]
                min_info["total_inconsistent_at_min"] = len(bad)
                break
        result["min_inconsistent_subset"] = min_info
    return result


def parse_support(s: str) -> List[int]:
    if not s:
        raise ValueError("empty support")
    if Path(s).exists():
        data = json.loads(Path(s).read_text())
        if isinstance(data, list):
            return [int(x) for x in data]
        for key in ["support", "A_support", "u_support"]:
            if key in data:
                return [int(x) for x in data[key]]
        raise ValueError(f"no support key in {s}")
    return [int(x) for x in s.replace(";", ",").replace(" ", ",").split(",") if x.strip()]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--support", required=True, help="comma-separated support or JSON file containing support")
    ap.add_argument("--subset", default="", help="optional comma-separated tight lambda subset")
    ap.add_argument("--transpose-coeff", action="store_true", help="use coefficient transpose for comparison")
    ap.add_argument("--min-subset", action="store_true")
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    support = parse_support(args.support)
    subset = parse_support(args.subset) if args.subset else None
    result = analyze_support(support, subset=subset, min_subset=args.min_subset, transpose_coeff=args.transpose_coeff)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "status": "ok",
        "out": str(args.out),
        "support_size": result["support_size"],
        "tight_rank9_count": result["tight_rank9_count"],
        "tight_rank9_lambdas": result["tight_rank9_lambdas"],
        "full_shadow_consistent": result["full_shadow_consistent"],
        "rank_aug": [result["full_shadow_rank"], result["full_shadow_augmented_rank"]],
        "inverse_mask_rank": result["inverse_mask_rank"],
        "min_inconsistent_subset": result.get("min_inconsistent_subset"),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
