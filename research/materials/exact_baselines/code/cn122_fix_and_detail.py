#!/usr/bin/env python3
r"""analysis: fix cn122 validation with TERM-based color counts and
build a definitive SAT-based pencil test for one near-miss infeasible case.

For cn122: each A-direction can appear multiple times (21 terms, 18 unique).
The pencil budget uses TERM counts, not unique direction counts.
X_{11} = sum of b_s c_s^T over ALL terms s in the (1,1) class.
rank(X_{11}) <= number_of_(1,1)_TERMS.

For the near-miss: 19 distinct directions, each appearing once.
Term counts = direction counts. The pencil test is correct as stated.
"""
from __future__ import annotations
import json, sys, time
from collections import Counter
from pathlib import Path
import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import (
    build_matmul_tensor_f2, contraction_matrix, mat_rank_f2,
    read_qmm_terms, restrict_terms_f2, vec_to_mask,
)
from dual_basis_instrument import gf2_mat_inv, gf2_mat_mul

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/pencil_pilot"

NEAR_MISS = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]


def build_e11_core_tensor():
    return build_matmul_tensor_f2()[1:,:,:].astype(np.uint8) % 2

def dot8(a, b):
    return bin(a & b).count('1') % 2

def main():
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    np.random.seed(456)

    T_core = build_e11_core_tensor()

    cdata = {}
    for q in range(1, 256):
        M = contraction_matrix(T_core, q)
        rk = mat_rank_f2(M)
        cdata[q] = {"rank": rk, "M": M}

    # ---- cn122 with TERM-BASED color counts ----
    terms = read_qmm_terms(ROOT / "workspace/data/cn122_3x3_r23_repro/scheme.qmm")
    core_terms = restrict_terms_f2(terms, 1)
    cn122_A = [vec_to_mask(t["u"]) for t in core_terms]
    cn122_B = [vec_to_mask(t["v"]) for t in core_terms]
    cn122_C = [vec_to_mask(t["w"]) for t in core_terms]
    n_terms = len(core_terms)

    print(f"cn122 core: {n_terms} terms, {len(set(cn122_A))} unique A-directions")

    # A-direction multiplicities
    mult = Counter(cn122_A)
    for a, c in mult.most_common():
        if c > 1:
            print(f"  direction {a}: multiplicity {c}")

    # Enumerate rank-9 lines
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

    # Validate cn122 with TERM counts
    cn122_ok = 0
    cn122_fail = 0
    cn122_fail_details = []

    for q1, q2, q3 in r9_lines:
        M1 = cdata[q1]["M"]
        M2 = cdata[q2]["M"]

        # TERM-based color counts
        c00 = c10 = c01 = c11 = 0
        X11 = np.zeros((9, 9), dtype=np.uint8)
        X10 = np.zeros((9, 9), dtype=np.uint8)
        X01 = np.zeros((9, 9), dtype=np.uint8)

        for s in range(n_terms):
            a = cn122_A[s]
            e1 = dot8(q1, a)
            e2 = dot8(q2, a)
            b = np.array([(cn122_B[s] >> i) & 1 for i in range(9)], dtype=np.uint8).reshape(9, 1)
            c = np.array([(cn122_C[s] >> i) & 1 for i in range(9)], dtype=np.uint8).reshape(1, 9)
            bc = (b @ c) % 2
            if e1 == 0 and e2 == 0:
                c00 += 1
            elif e1 == 1 and e2 == 0:
                c10 += 1
                X10 = (X10 + bc) % 2
            elif e1 == 0 and e2 == 1:
                c01 += 1
                X01 = (X01 + bc) % 2
            else:
                c11 += 1
                X11 = (X11 + bc) % 2

        # Verify tensor equations
        m1_ok = np.array_equal((X10 + X11) % 2, M1)
        m2_ok = np.array_equal((X01 + X11) % 2, M2)

        # Check pencil constraint with TERM counts
        rX11 = mat_rank_f2(X11)
        rX10 = mat_rank_f2(X10)
        rX01 = mat_rank_f2(X01)

        pencil_ok = (rX11 <= c11 and rX10 <= c10 and rX01 <= c01)

        if pencil_ok and m1_ok and m2_ok:
            cn122_ok += 1
        else:
            cn122_fail += 1
            cn122_fail_details.append({
                "line": [q1, q2, q3],
                "term_colors": [c00, c10, c01, c11],
                "ranks": [int(rX11), int(rX10), int(rX01)],
                "pencil_ok": pencil_ok,
                "tensor_ok": m1_ok and m2_ok,
            })

    print(f"\ncn122 TERM-based pencil validation on {len(r9_lines)} rank-9 lines:")
    print(f"  PASS: {cn122_ok}")
    print(f"  FAIL: {cn122_fail}")

    if cn122_fail > 0:
        for r in cn122_fail_details[:5]:
            print(f"  FAIL detail: line={r['line']} colors={r['term_colors']} "
                  f"ranks={r['ranks']} pencil={r['pencil_ok']} tensor={r['tensor_ok']}")

    # ---- Near-miss pencil: compare direction-based vs the mechanism ----
    # For the near-miss, direction counts = term counts (19 distinct, no repeats)
    # Show a few specific infeasible cases with detailed analysis

    # Pick one infeasible case: line=[42, 149, 191] colors=(3,3,6,7) per initial pilot
    test_cases = [
        ([42, 149, 191], "from initial pilot"),
        ([55, 141, 186], "from initial pilot"),
        ([78, 185, 247], "from verification"),
    ]

    print("\n---- Near-miss pencil detail for selected infeasible cases ----")
    for line, source in test_cases:
        q1, q2, q3 = line
        M1 = cdata[q1]["M"]
        M2 = cdata[q2]["M"]

        c00 = c10 = c01 = c11 = 0
        for p in NEAR_MISS:
            e1, e2 = dot8(q1, p), dot8(q2, p)
            if e1 == 0 and e2 == 0: c00 += 1
            elif e1 == 1 and e2 == 0: c10 += 1
            elif e1 == 0 and e2 == 1: c01 += 1
            else: c11 += 1

        rM1 = mat_rank_f2(M1)
        rM2 = mat_rank_f2(M2)
        M3 = contraction_matrix(T_core, q3)
        rM3 = mat_rank_f2(M3)

        # Contraction bounds
        ib1 = c10 + c11 >= rM1  # w(q1) >= r1
        ib2 = c01 + c11 >= rM2  # w(q2) >= r2
        ib3 = c10 + c01 >= rM3  # w(q3) >= r3

        # Pencil-specific: A = M1^{-1} M2
        M1_inv = gf2_mat_inv(M1)
        M2_inv = gf2_mat_inv(M2)
        A = gf2_mat_mul(M1_inv, M2) % 2
        rA_plus_I = mat_rank_f2((A + np.eye(9, dtype=np.uint8)) % 2)

        # Random search for Z with MANY trials
        best_r1 = best_r2 = 9
        found = False
        for trial in range(50000):
            while True:
                U = np.random.randint(0, 2, size=(9, c11)).astype(np.uint8)
                if mat_rank_f2(U) == c11:
                    break
            while True:
                V = np.random.randint(0, 2, size=(9, c11)).astype(np.uint8)
                if mat_rank_f2(V) == c11:
                    break
            Z = gf2_mat_mul(U, V.T) % 2
            r1 = mat_rank_f2((M1 + Z) % 2)
            r2 = mat_rank_f2((M2 + Z) % 2)
            if r1 + r2 < best_r1 + best_r2:
                best_r1, best_r2 = r1, r2
            if r1 <= c10 and r2 <= c01:
                found = True
                break

        print(f"\n  Line {line} ({source}):")
        print(f"    Colors: c00={c00}, c10={c10}, c01={c01}, c11={c11}")
        print(f"    Contraction ranks: r1={rM1}, r2={rM2}, r3={rM3}")
        print(f"    Individual bounds: ib1={ib1}, ib2={ib2}, ib3={ib3}")
        print(f"    rank(A+I) = rank(M1+M2) / M1: {rA_plus_I}")
        print(f"    Pencil target: rank(Z)≤{c11}, rank(M1+Z)≤{c10}, rank(M2+Z)≤{c01}")
        print(f"    50000 random trials: found={found}, best_ranks=({best_r1},{best_r2})")
        if not found:
            print(f"    PENCIL INFEASIBLE (empirical): "
                  f"need (≤{c10},≤{c01}) but best is ({best_r1},{best_r2})")

    # ---- Save ----
    output = {
        "cn122_term_based_validation": {
            "total_r9_lines": len(r9_lines),
            "pass": cn122_ok,
            "fail": cn122_fail,
            "fail_details": cn122_fail_details[:10],
        },
        "near_miss_detailed_tests": [
            {"line": line, "source": source}
            for line, source in test_cases
        ],
        "elapsed_sec": time.time() - t0,
    }
    out = OUTDIR / "pencil_cn122_fix_and_detail.json"
    out.write_text(json.dumps(output, indent=2, sort_keys=True, default=str) + "\n")
    print(f"\nSaved: {out}")
    print(f"Elapsed: {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
