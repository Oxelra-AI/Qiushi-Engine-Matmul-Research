#!/usr/bin/env python3
r"""analysis: validate pencil constraints on cn122 positive control and
exhaustively verify selected infeasible lines.

1. cn122 core (21 terms) must be pencil-feasible on ALL rank-9 dual lines
   (since an actual decomposition exists).
2. For selected infeasible lines of the near-miss, verify with exhaustive
   search at small c11 or extremely large random sample.
"""
from __future__ import annotations

import json, sys, time, random
from collections import Counter
from pathlib import Path
import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (
    build_matmul_tensor_f2, contraction_matrix, mat_rank_f2,
    gf2_rank_rows, read_qmm_terms, restrict_terms_f2, vec_to_mask,
)
from dual_basis_instrument import gf2_mat_inv, gf2_mat_mul

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/pencil_pilot"

NEAR_MISS = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]


def build_e11_core_tensor():
    return build_matmul_tensor_f2()[1:,:,:].astype(np.uint8) % 2


def dot8(a, b):
    return bin(a & b).count('1') % 2


def get_cn122_core_support():
    """Get the E11 core A-support from cn122 rank-23 decomposition."""
    terms = read_qmm_terms(ROOT / "workspace/data/cn122_3x3_r23_repro/scheme.qmm")
    core_terms = restrict_terms_f2(terms, 1)  # restrict by E11
    A_cols = [vec_to_mask(t["u"]) for t in core_terms]
    return sorted(set(A_cols))  # unique projected A-directions


def pencil_test_direct(M1, M2, c10, c01, c11, n_trials=5000):
    """Direct random search for Z = UV^T satisfying all three rank bounds."""
    n = 9
    for trial in range(n_trials):
        while True:
            U = np.random.randint(0, 2, size=(n, c11)).astype(np.uint8)
            if mat_rank_f2(U) == c11:
                break
        while True:
            V = np.random.randint(0, 2, size=(n, c11)).astype(np.uint8)
            if mat_rank_f2(V) == c11:
                break
        Z = gf2_mat_mul(U, V.T) % 2
        r1 = mat_rank_f2((M1 + Z) % 2)
        r2 = mat_rank_f2((M2 + Z) % 2)
        if r1 <= c10 and r2 <= c01:
            return {"feasible": True, "trial": trial, "r1": int(r1), "r2": int(r2)}
    return {"feasible": False, "n_trials": n_trials}


def pencil_test_exhaustive_small_c11(M1, M2, c10, c01, c11):
    """For very small c11 (1-3), enumerate ALL possible Z of rank <= c11."""
    n = 9
    # For c11=1: Z = u v^T, 2^9 * 2^9 = 262144 pairs, minus rank-0
    # For c11=2: too large for direct enumeration
    # Use the UV^T parametrization but enumerate all rank-c11 U, V
    count = 0
    feasible = False
    best_ranks = (9, 9)

    if c11 == 0:
        # Z = 0
        r1 = mat_rank_f2(M1)
        r2 = mat_rank_f2(M2)
        if r1 <= c10 and r2 <= c01:
            return {"feasible": True, "count": 1, "method": "exhaustive_c0"}
        return {"feasible": False, "count": 1, "method": "exhaustive_c0"}

    if c11 == 1:
        # Z = u * v^T, rank 0 or 1
        # Enumerate all nonzero u, v in F_2^9
        for u_mask in range(1, 1 << n):
            u = np.array([(u_mask >> i) & 1 for i in range(n)], dtype=np.uint8).reshape(n, 1)
            for v_mask in range(1, 1 << n):
                v = np.array([(v_mask >> i) & 1 for i in range(n)], dtype=np.uint8).reshape(1, n)
                Z = (u @ v) % 2
                r1 = mat_rank_f2((M1 + Z) % 2)
                r2 = mat_rank_f2((M2 + Z) % 2)
                count += 1
                if r1 <= c10 and r2 <= c01:
                    return {"feasible": True, "count": count, "method": "exhaustive_c1",
                            "r1": int(r1), "r2": int(r2)}
                if r1 + r2 < best_ranks[0] + best_ranks[1]:
                    best_ranks = (int(r1), int(r2))
        # Also test Z = 0
        r1 = mat_rank_f2(M1)
        r2 = mat_rank_f2(M2)
        if r1 <= c10 and r2 <= c01:
            return {"feasible": True, "count": count+1, "method": "exhaustive_c1"}
        return {"feasible": False, "count": count+1, "method": "exhaustive_c1",
                "best_ranks": list(best_ranks)}

    # For c11 >= 2, use large random sample
    return pencil_test_direct(M1, M2, c10, c01, c11, n_trials=20000)


def main():
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    np.random.seed(123)

    T_core = build_e11_core_tensor()

    cdata = {}
    for q in range(1, 256):
        M = contraction_matrix(T_core, q)
        rk = mat_rank_f2(M)
        cdata[q] = {"rank": rk, "M": M, "M_inv": gf2_mat_inv(M) if rk == 9 else None}

    # ---- cn122 positive control ----
    cn122_support = get_cn122_core_support()
    print(f"cn122 core support: {len(cn122_support)} unique directions, support={cn122_support}")

    # Find all-rank-9 lines
    seen = set()
    r9_lines = []
    for q1 in range(1, 256):
        for q2 in range(q1+1, 256):
            q3 = q1 ^ q2
            if q3 == 0: continue
            canon = tuple(sorted([q1, q2, q3]))
            if canon in seen: continue
            seen.add(canon)
            if all(cdata[q]["rank"] == 9 for q in canon):
                r9_lines.append(canon)

    print(f"All-rank-9 lines: {len(r9_lines)}")

    # Test cn122 on ALL rank-9 lines
    cn122_results = []
    cn122_fail = 0
    for q1, q2, q3 in r9_lines:
        c00 = c10 = c01 = c11 = 0
        for p in cn122_support:
            e1, e2 = dot8(q1, p), dot8(q2, p)
            if e1 == 0 and e2 == 0: c00 += 1
            elif e1 == 1 and e2 == 0: c10 += 1
            elif e1 == 0 and e2 == 1: c01 += 1
            else: c11 += 1

        # cn122 has 21 core terms (not all distinct A-directions)
        # For pencil test, we use UNIQUE A-directions as the support
        # Color counts based on unique A-directions
        result = pencil_test_direct(cdata[q1]["M"], cdata[q2]["M"],
                                     c10, c01, c11, n_trials=500)
        if not result["feasible"]:
            cn122_fail += 1
            cn122_results.append({
                "line": [q1, q2, q3],
                "colors": [c00, c10, c01, c11],
                "feasible": False,
            })

    print(f"\ncn122 positive control: {cn122_fail} pencil failures out of {len(r9_lines)}")

    # If cn122 fails, that's a bug in the test
    if cn122_fail > 0:
        print("  WARNING: cn122 failures indicate a test bug!")
        for r in cn122_results:
            print(f"    line={r['line']} colors={r['colors']}")

    # ---- Verify selected near-miss infeasible cases ----
    # Pick cases with small c11 for exhaustive verification

    # Load analytical results
    anal_file = OUTDIR / "analytical_pencil_results.json"
    if anal_file.exists():
        anal = json.loads(anal_file.read_text())
        infeasible_tests = [t for t in anal.get("tests", [])
                            if not t.get("pencil_feasible", True)
                            and t.get("pencil") != "trivial_feasible"]
    else:
        infeasible_tests = []

    print(f"\nVerifying {min(20, len(infeasible_tests))} infeasible cases with intensive search:")

    verification_results = []
    for rec in infeasible_tests[:20]:
        q1, q2, q3 = rec["line"]
        c00, c10, c01, c11 = rec["colors"]

        M1 = cdata[q1]["M"]
        M2 = cdata[q2]["M"]

        if c11 <= 1:
            result = pencil_test_exhaustive_small_c11(M1, M2, c10, c01, c11)
        else:
            result = pencil_test_direct(M1, M2, c10, c01, c11, n_trials=20000)

        status = "FEASIBLE" if result.get("feasible") else "INFEASIBLE"
        print(f"  line={[q1,q2,q3]} colors=({c00},{c10},{c01},{c11}) → {status} "
              f"(checked {result.get('count', result.get('n_trials', '?'))})")

        verification_results.append({
            "line": [q1, q2, q3],
            "colors": [c00, c10, c01, c11],
            "verified_feasible": result.get("feasible"),
            "detail": result,
        })

    # ---- Also test with actual cn122 term matrices ----
    # The cn122 core decomposition provides actual B, C vectors.
    # For each rank-9 dual line, we can check that the actual term matrices
    # satisfy the pencil constraint.
    terms = read_qmm_terms(ROOT / "workspace/data/cn122_3x3_r23_repro/scheme.qmm")
    core_terms = restrict_terms_f2(terms, 1)
    cn122_A = [vec_to_mask(t["u"]) for t in core_terms]
    cn122_B = [vec_to_mask(t["v"]) for t in core_terms]
    cn122_C = [vec_to_mask(t["w"]) for t in core_terms]

    print(f"\ncn122 core: {len(core_terms)} terms")

    cn122_pencil_check = []
    for q1, q2, q3 in r9_lines[:20]:  # Check 20 lines
        M1 = cdata[q1]["M"]
        M2 = cdata[q2]["M"]

        # Compute X_{11} from actual terms
        X11 = np.zeros((9, 9), dtype=np.uint8)
        X10 = np.zeros((9, 9), dtype=np.uint8)
        X01 = np.zeros((9, 9), dtype=np.uint8)
        for s in range(len(core_terms)):
            a = cn122_A[s]
            e1 = dot8(q1, a)
            e2 = dot8(q2, a)
            b = np.array([(cn122_B[s] >> i) & 1 for i in range(9)], dtype=np.uint8).reshape(9, 1)
            c = np.array([(cn122_C[s] >> i) & 1 for i in range(9)], dtype=np.uint8).reshape(1, 9)
            bc = (b @ c) % 2
            if e1 == 1 and e2 == 1:
                X11 = (X11 + bc) % 2
            elif e1 == 1 and e2 == 0:
                X10 = (X10 + bc) % 2
            elif e1 == 0 and e2 == 1:
                X01 = (X01 + bc) % 2

        # Verify M1 = X10 + X11 and M2 = X01 + X11
        M1_check = (X10 + X11) % 2
        M2_check = (X01 + X11) % 2
        m1_ok = np.array_equal(M1_check, M1)
        m2_ok = np.array_equal(M2_check, M2)

        r_X11 = mat_rank_f2(X11)
        r_M1pX11 = mat_rank_f2((M1 + X11) % 2)
        r_M2pX11 = mat_rank_f2((M2 + X11) % 2)

        cn122_pencil_check.append({
            "line": [q1, q2, q3],
            "M1_M2_correct": m1_ok and m2_ok,
            "rank_X11": int(r_X11),
            "rank_M1pX11": int(r_M1pX11),
            "rank_M2pX11": int(r_M2pX11),
        })

    print("\ncn122 actual term-matrix pencil check (first 20 lines):")
    for r in cn122_pencil_check:
        print(f"  line={r['line']}: M_ok={r['M1_M2_correct']} "
              f"rank(X11)={r['rank_X11']} "
              f"rank(M1+X11)={r['rank_M1pX11']} "
              f"rank(M2+X11)={r['rank_M2pX11']}")

    # Save everything
    output = {
        "cn122_control": {
            "support": cn122_support,
            "n_unique_directions": len(cn122_support),
            "r9_lines_tested": len(r9_lines),
            "pencil_failures": cn122_fail,
            "actual_term_checks": cn122_pencil_check,
        },
        "near_miss_verification": verification_results,
        "elapsed_sec": time.time() - t0,
    }
    out = OUTDIR / "pencil_validation.json"
    out.write_text(json.dumps(output, indent=2, sort_keys=True, default=str) + "\n")
    print(f"\nSaved: {out}")
    print(f"Elapsed: {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
