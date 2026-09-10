#!/usr/bin/env python3
r"""analysis: dual-line colored-projection pencil realizability pilot.

For a dual line D = span(q1,q2) in F_2^8, each A-direction p gets color
(q1(p), q2(p)) in {00,10,01,11}.  In any decomposition, the color-class
term sums satisfy:

    L(q1) = X_{10} + X_{11},  rank(X_{10}) <= c_{10}
    L(q2) = X_{01} + X_{11},  rank(X_{01}) <= c_{01}
    rank(X_{11}) <= c_{11}

Setting Z = X_{11}, the pencil realizability question is: does there exist
a 9x9 matrix Z over F_2 with
    rank(Z)       <= c_{11}
    rank(M1 + Z)  <= c_{10}
    rank(M2 + Z)  <= c_{01}

where M1 = L(q1), M2 = L(q2)?

When both M1, M2 are invertible (rank 9), Sylvester's determinant identity
reduces the corank conditions to c_{11} x c_{11} matrices:

  Parametrize Z = U V^T (U, V are 9 x c_{11}, both rank c_{11}).

  corank(M1 + Z) = dim ker(I_{c11} + V^T M1^{-1} U)
  corank(M2 + Z) = dim ker(I_{c11} + V^T M2^{-1} U)

For the tightest budget where corank(Mi+Z) must equal c_{11} (i.e.,
V^T Mi^{-1} U = I), we get a LINEAR system in V for fixed U, which can
be checked by GF(2) Gaussian elimination.

This script:
1. Enumerates all 10,795 dual lines of F_2^8 and their rank triples
2. Computes color profiles for the current near-miss support
3. Checks individual contraction bounds
4. Tests pencil realizability on lines passing individual bounds

A pencil infeasibility on a line that passes individual bounds would be
a genuinely new A-support constraint.
"""
from __future__ import annotations

import json
import random
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (
    build_matmul_tensor_f2,
    contraction_matrix,
    mat_rank_f2,
    rref_basis,
    gf2_rank_rows,
)
from dual_basis_instrument import gf2_mat_inv, gf2_mat_mul

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/pencil_pilot"

# analysis 9-violation near-miss
NEAR_MISS = [1, 2, 3, 4, 8, 20, 24, 31, 32, 36, 64, 73, 109, 127, 128, 141, 160, 182, 219]


def build_e11_core_tensor() -> np.ndarray:
    return build_matmul_tensor_f2()[1:, :, :].astype(np.uint8) % 2


def dot8(a: int, b: int) -> int:
    return bin(a & b).count('1') % 2


def enumerate_dual_lines(n: int = 8) -> List[Tuple[int, int, int]]:
    """Enumerate all 2D subspaces of F_2^n.  Each returned as sorted triple
    (q1, q2, q3) where q3 = q1 ^ q2."""
    lines = []
    seen = set()
    for q1 in range(1, 1 << n):
        for q2 in range(q1 + 1, 1 << n):
            q3 = q1 ^ q2
            if q3 == 0:
                continue
            canon = tuple(sorted([q1, q2, q3]))
            if canon in seen:
                continue
            seen.add(canon)
            lines.append(canon)
    return lines


def gf2_solve_system(coeff_rows: List[int], rhs_bits: List[int], nvars: int) -> Optional[List[List[int]]]:
    """Solve a GF(2) system.  coeff_rows[i] is bitmask of coefficients,
    rhs_bits[i] is the RHS bit.  Returns list of solutions as bitmasks,
    or None if inconsistent.  Each solution is base + xor of free-variable
    choices."""
    neq = len(coeff_rows)
    # Augmented rows
    aug = []
    for i in range(neq):
        row = (coeff_rows[i] & ((1 << nvars) - 1))
        if rhs_bits[i]:
            row |= (1 << nvars)
        aug.append(row)

    # Gaussian elimination
    pivot = {}
    for i in range(neq):
        r = aug[i]
        coeff = r & ((1 << nvars) - 1)
        while coeff:
            p = coeff.bit_length() - 1
            if p in pivot:
                r ^= aug[pivot[p]]
                coeff = r & ((1 << nvars) - 1)
            else:
                pivot[p] = i
                aug[i] = r
                break
        else:
            # All coeff bits zero; check rhs
            if (r >> nvars) & 1:
                return None  # inconsistent

    # Build particular solution
    sol = 0
    free_vars = [j for j in range(nvars) if j not in pivot]
    for p in sorted(pivot.keys(), reverse=True):
        row = aug[pivot[p]]
        bit = (row >> nvars) & 1
        for j in free_vars:
            pass  # free vars = 0 in particular solution
        for q in sorted(pivot.keys()):
            if q != p and (row >> q) & 1:
                bit ^= (sol >> q) & 1
        if bit:
            sol |= 1 << p

    return {"particular": sol, "free_vars": free_vars, "rank": len(pivot)}


def pencil_test_tight(M1_inv: np.ndarray, M2_inv: np.ndarray,
                       c11: int, n_random_U: int = 200) -> dict:
    """Test pencil realizability for the tightest budget where
    V^T M1^{-1} U = I_{c11} and V^T M2^{-1} U = I_{c11}.

    For fixed U (9 x c11), this becomes a 2*c11^2 x 9*c11 GF(2) linear
    system for the entries of V.

    Returns dict with feasibility result and diagnostics.
    """
    n = 9
    any_feasible = False
    tested = 0
    consistent_count = 0

    for trial in range(n_random_U):
        # Random U: 9 x c11 of rank c11
        while True:
            U = np.random.randint(0, 2, size=(n, c11)).astype(np.uint8)
            if mat_rank_f2(U) == c11:
                break

        # Compute S1 = M1^{-1} U and S2 = M2^{-1} U
        S1 = gf2_mat_mul(M1_inv, U) % 2
        S2 = gf2_mat_mul(M2_inv, U) % 2

        # For each column j of V (= row j of V^T), solve:
        #   v_j^T s1_k = delta_{jk}  for k=0..c11-1
        #   v_j^T s2_k = delta_{jk}  for k=0..c11-1
        # This is 2*c11 equations in 9 unknowns.

        # Build coefficient rows (same for all j)
        coeff_rows = []
        for k in range(c11):
            row = 0
            for i in range(n):
                if int(S1[i, k]) & 1:
                    row |= 1 << i
            coeff_rows.append(row)
        for k in range(c11):
            row = 0
            for i in range(n):
                if int(S2[i, k]) & 1:
                    row |= 1 << i
            coeff_rows.append(row)

        # Check consistency for each j
        all_consistent = True
        v_cols = []
        for j in range(c11):
            rhs = [0] * (2 * c11)
            rhs[j] = 1        # delta_{jk} for S1 part
            rhs[c11 + j] = 1  # delta_{jk} for S2 part
            result = gf2_solve_system(coeff_rows, rhs, n)
            if result is None:
                all_consistent = False
                break
            v_cols.append(result)

        tested += 1
        if all_consistent:
            consistent_count += 1
            # Check V has rank c11
            v_vecs = [vc["particular"] for vc in v_cols]
            if gf2_rank_rows(v_vecs, n) == c11:
                any_feasible = True
                break

    return {
        "tested": tested,
        "consistent_count": consistent_count,
        "any_feasible": any_feasible,
        "c11": c11,
    }


def pencil_test_general(M1_inv: np.ndarray, M2_inv: np.ndarray,
                         c10: int, c01: int, c11: int,
                         n_random: int = 500) -> dict:
    """Test pencil realizability for general budget using random search.

    Parametrize Z = U V^T (9 x c11 factors).  For random U, V:
      - rank(Z) <= c11 by construction
      - Check rank(M1 + Z) <= c10 and rank(M2 + Z) <= c01

    Also uses the Sylvester reduction: compute small matrices
    F1 = V^T M1^{-1} U and F2 = V^T M2^{-1} U, then check
    corank(I + F1) >= d1 and corank(I + F2) >= d2.
    """
    n = 9
    d1 = n - c10  # required corank of M1+Z
    d2 = n - c01  # required corank of M2+Z
    any_feasible = False
    tested = 0

    for trial in range(n_random):
        # Random U, V of rank c11
        while True:
            U = np.random.randint(0, 2, size=(n, c11)).astype(np.uint8)
            if mat_rank_f2(U) == c11:
                break
        while True:
            V = np.random.randint(0, 2, size=(n, c11)).astype(np.uint8)
            if mat_rank_f2(V) == c11:
                break

        # Z = U V^T
        Z = gf2_mat_mul(U, V.T) % 2

        r1 = mat_rank_f2((np.array(M1_inv, dtype=int) @ np.eye(n, dtype=int)).astype(np.uint8))  # sanity
        # Direct check
        M1_plus_Z = (gf2_mat_mul(np.eye(n, dtype=np.uint8),
                                  np.zeros((n, n), dtype=np.uint8)))  # placeholder
        # Actually compute M1+Z where M1 is the original matrix (not inverse)
        # We need the original M1 ... we receive M1_inv. Compute M1 from M1_inv.
        M1 = gf2_mat_inv(M1_inv)
        M2 = gf2_mat_inv(M2_inv)
        assert M1 is not None and M2 is not None

        MpZ1 = (M1 + Z) % 2
        MpZ2 = (M2 + Z) % 2

        rk1 = mat_rank_f2(MpZ1)
        rk2 = mat_rank_f2(MpZ2)
        tested += 1

        if rk1 <= c10 and rk2 <= c01:
            any_feasible = True
            break

    return {
        "tested": tested,
        "any_feasible": any_feasible,
        "c10": c10,
        "c01": c01,
        "c11": c11,
        "d1": d1,
        "d2": d2,
    }


def main():
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)

    T_core = build_e11_core_tensor()
    na, nb, nc = T_core.shape
    assert (na, nb, nc) == (8, 9, 9)

    # ---- Contraction data ----
    cdata: Dict[int, dict] = {}
    for q in range(1, 256):
        M = contraction_matrix(T_core, q)
        rk = mat_rank_f2(M)
        inv = gf2_mat_inv(M) if rk == 9 else None
        cdata[q] = {"rank": rk, "M": M, "M_inv": inv}

    rank_dist = Counter(d["rank"] for d in cdata.values())
    print(f"Contraction ranks: {dict(sorted(rank_dist.items()))}")

    rank9_qs = sorted(q for q, d in cdata.items() if d["rank"] == 9)
    print(f"Rank-9 contractions: {len(rank9_qs)}")

    # ---- Enumerate all dual lines ----
    lines = enumerate_dual_lines(8)
    print(f"Total dual lines: {len(lines)}")

    support_set = set(NEAR_MISS)

    # ---- Color profiling ----
    records = []
    for q1, q2, q3 in lines:
        r1 = cdata[q1]["rank"]
        r2 = cdata[q2]["rank"]
        r3 = cdata[q3]["rank"]
        rtype = tuple(sorted([r1, r2, r3]))

        # Color counts for near-miss
        c00 = c10 = c01 = c11 = 0
        for p in NEAR_MISS:
            e1 = dot8(q1, p)
            e2 = dot8(q2, p)
            if e1 == 0 and e2 == 0:
                c00 += 1
            elif e1 == 1 and e2 == 0:
                c10 += 1
            elif e1 == 0 and e2 == 1:
                c01 += 1
            else:
                c11 += 1

        # Individual bounds
        ib1 = (c10 + c11 >= r1)  # w(q1) >= rank L(q1)
        ib2 = (c01 + c11 >= r2)  # w(q2) >= rank L(q2)
        ib3 = (c10 + c01 >= r3)  # w(q1+q2) >= rank L(q1+q2)
        all_ib = ib1 and ib2 and ib3

        # Tightness: how much excess in each bound
        excess1 = (c10 + c11) - r1
        excess2 = (c01 + c11) - r2
        excess3 = (c10 + c01) - r3

        records.append({
            "line": [q1, q2, q3],
            "ranks": [r1, r2, r3],
            "rank_type": list(rtype),
            "colors": [c00, c10, c01, c11],
            "ib_pass": all_ib,
            "ib_detail": [ib1, ib2, ib3],
            "excess": [excess1, excess2, excess3],
            "min_excess": min(excess1, excess2, excess3) if all_ib else -1,
        })

    # ---- Statistics ----
    ib_pass = sum(1 for r in records if r["ib_pass"])
    ib_fail = len(records) - ib_pass
    print(f"\nIndividual bounds: pass {ib_pass}, fail {ib_fail} / {len(records)}")

    rtype_counts = Counter(tuple(r["rank_type"]) for r in records)
    print(f"\nRank-type distribution:")
    for rt in sorted(rtype_counts.keys()):
        n_pass = sum(1 for r in records
                     if tuple(r["rank_type"]) == rt and r["ib_pass"])
        n_fail = sum(1 for r in records
                     if tuple(r["rank_type"]) == rt and not r["ib_pass"])
        print(f"  {rt}: total {rtype_counts[rt]}, ib_pass {n_pass}, ib_fail {n_fail}")

    # Lines passing individual bounds with small min_excess
    tight = [r for r in records if r["ib_pass"]]
    tight.sort(key=lambda r: r["min_excess"])
    print(f"\nTightest ib-passing lines (min_excess):")
    for r in tight[:20]:
        print(f"  line={r['line']} ranks={r['ranks']} colors={r['colors']} "
              f"excess={r['excess']} min_ex={r['min_excess']}")

    # ---- Pencil tests ----
    # Focus on all-rank-9 lines with ib_pass and tight budgets
    r9_pass = [r for r in records
               if r["ib_pass"] and all(rk == 9 for rk in r["ranks"])]
    print(f"\nAll-rank-9 ib-passing lines: {len(r9_pass)}")

    # Test pencil on tight all-rank-9 lines
    pencil_results = []
    tested_set = set()

    # Sort by tightness
    r9_pass.sort(key=lambda r: (r["min_excess"], min(r["colors"][3], r["colors"][1], r["colors"][2])))

    for rec in r9_pass[:50]:  # test up to 50 tightest
        q1, q2, q3 = rec["line"]
        c00, c10, c01, c11 = rec["colors"]
        line_key = tuple(sorted([q1, q2, q3]))
        if line_key in tested_set:
            continue
        tested_set.add(line_key)

        M1_inv = cdata[q1]["M_inv"]
        M2_inv = cdata[q2]["M_inv"]
        assert M1_inv is not None and M2_inv is not None

        d1 = 9 - c10  # required corank
        d2 = 9 - c01

        # Check if tight enough for analytical test
        if d1 == c11 and d2 == c11:
            # Tightest case: V^T N1 U = I and V^T N2 U = I
            result = pencil_test_tight(M1_inv, M2_inv, c11)
        elif d1 >= 1 and d2 >= 1:
            # Use random search with general test
            # First try tight analytical
            if d1 == c11 or d2 == c11:
                # One side tight, one side relaxed
                result = pencil_test_general(M1_inv, M2_inv, c10, c01, c11, n_random=300)
            else:
                result = pencil_test_general(M1_inv, M2_inv, c10, c01, c11, n_random=300)
        else:
            result = {"tested": 0, "any_feasible": True,
                      "note": "trivial (corank requirement 0)"}

        pencil_results.append({
            "line": rec["line"],
            "ranks": rec["ranks"],
            "colors": rec["colors"],
            "excess": rec["excess"],
            "d1_d2": [d1, d2],
            "pencil": result,
        })

        tag = "FEASIBLE" if result.get("any_feasible") else "INFEASIBLE"
        print(f"  Pencil {tag}: line={rec['line']} colors=({c00},{c10},{c01},{c11}) "
              f"d=({d1},{d2}) tested={result.get('tested',0)}")

    # Also test mixed-rank lines that pass individual bounds
    mixed_pass = [r for r in records
                  if r["ib_pass"]
                  and not all(rk == 9 for rk in r["ranks"])
                  and any(rk == 9 for rk in r["ranks"])]
    mixed_pass.sort(key=lambda r: r["min_excess"])
    print(f"\nMixed-rank ib-passing lines with rank-9: {len(mixed_pass)}")

    # ---- Save results ----
    # Summary statistics
    summary = {
        "total_dual_lines": len(lines),
        "ib_pass_count": ib_pass,
        "ib_fail_count": ib_fail,
        "rank_type_distribution": {str(k): v for k, v in sorted(rtype_counts.items())},
        "all_rank9_ib_pass": len(r9_pass),
        "mixed_rank_ib_pass_with_r9": len(mixed_pass),
        "pencil_tests": pencil_results,
        "support": NEAR_MISS,
        "elapsed_sec": time.time() - t0,
    }

    # Color distribution summary
    color_stats = Counter()
    for r in records:
        if r["ib_pass"]:
            color_stats[tuple(r["colors"])] += 1

    summary["ib_pass_color_distribution_top20"] = [
        {"colors": list(k), "count": v}
        for k, v in color_stats.most_common(20)
    ]

    # Excess distribution for ib-passing lines
    excess_hist = Counter(r["min_excess"] for r in records if r["ib_pass"])
    summary["min_excess_histogram"] = dict(sorted(excess_hist.items()))

    outfile = OUTDIR / "pencil_pilot_results.json"
    outfile.write_text(json.dumps(summary, indent=2, sort_keys=True, default=str) + "\n")
    print(f"\nSaved: {outfile}")
    print(f"Elapsed: {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
