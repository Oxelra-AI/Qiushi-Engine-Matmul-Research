#!/usr/bin/env python3
r"""
analysis: positive controls for the full spectral-resolution contraction layer.

For a contraction M(q) of rank rho and a CPD support tight at q,

    M(q) = sum_{s in I_q} b_s c_s^T,  |I_q|=rho,

any generalized inverse N with M N M = M satisfies

    c_s^T N b_t = delta_{st}.

For invertible M and |I_q|=10, Q=(c_s^T M^{-1} b_t) is a 10x10 idempotent of
rank 9, so rank(Q-I)=1 over F2 and all 2x2 minors of Q-I vanish.  This script
checks these facts on sampled verified rank-21 decompositions of the three F2
quotient cores.  It is an algebra/convention control for future graph/SAT cuts.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Optional, Sequence

import numpy as np

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/trace_saturation_gate"
for P in (ROOT / "workspace/scripts", Path("scripts")):
    if str(P) not in sys.path:
        sys.path.insert(0, str(P))

from corrected_trace_core_survey import CORES, quotient_core_from_mask, reconstruct_from_terms, term_lists  # noqa: E402
from trace_saturation_gate import contraction_matrix, contraction_ranks  # noqa: E402


def bits(mask: int, n: int = 9) -> list[int]:
    return [(int(mask) >> i) & 1 for i in range(n)]


def mat_rank_f2(M: np.ndarray) -> int:
    A = np.asarray(M, dtype=np.uint8).copy() & 1
    m, n = A.shape
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if int(A[i, c]):
                piv = i
                break
        if piv is None:
            continue
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for i in range(m):
            if i != r and int(A[i, c]):
                A[i] ^= A[r]
        r += 1
        if r == m:
            break
    return int(r)


def gf2_inv_square(M: np.ndarray) -> Optional[np.ndarray]:
    M = np.asarray(M, dtype=np.uint8) & 1
    n = M.shape[0]
    if M.shape != (n, n):
        raise ValueError("not square")
    A = np.concatenate([M.copy(), np.eye(n, dtype=np.uint8)], axis=1)
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, n):
            if int(A[i, c]):
                piv = i
                break
        if piv is None:
            return None
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for i in range(n):
            if i != r and int(A[i, c]):
                A[i] ^= A[r]
        r += 1
    return A[:, n:]


def independent_indices_columns(M: np.ndarray, r: int) -> list[int]:
    cols: list[int] = []
    cur = np.zeros((M.shape[0], 0), dtype=np.uint8)
    rk = 0
    for j in range(M.shape[1]):
        test = np.concatenate([cur, M[:, [j]]], axis=1)
        nr = mat_rank_f2(test)
        if nr > rk:
            cols.append(j)
            cur = test
            rk = nr
            if rk == r:
                break
    if len(cols) != r:
        raise RuntimeError("could not find independent columns")
    return cols


def independent_indices_rows(M: np.ndarray, r: int) -> list[int]:
    return independent_indices_columns(M.T, r)


def generalized_inverse(M: np.ndarray) -> np.ndarray:
    M = np.asarray(M, dtype=np.uint8) & 1
    r = mat_rank_f2(M)
    if r == M.shape[0] == M.shape[1]:
        inv = gf2_inv_square(M)
        assert inv is not None
        return inv
    R = independent_indices_rows(M, r)
    C = independent_indices_columns(M, r)
    S = M[np.ix_(R, C)]
    Sinv = gf2_inv_square(S)
    assert Sinv is not None
    N = np.zeros((M.shape[1], M.shape[0]), dtype=np.uint8)
    for ii, c in enumerate(C):
        for jj, row in enumerate(R):
            N[c, row] = Sinv[ii, jj]
    if not np.array_equal((M @ N @ M) & 1, M):
        raise AssertionError("constructed N is not a generalized inverse")
    return N


def bilinear(N: np.ndarray, bmask: int, cmask: int) -> int:
    b = np.array(bits(bmask, N.shape[1]), dtype=np.uint8)
    c = np.array(bits(cmask, N.shape[0]), dtype=np.uint8)
    return int((c @ N @ b) & 1)


def gamma_matrix(N: np.ndarray, B: Sequence[int], C: Sequence[int], active: Sequence[int]) -> np.ndarray:
    m = len(active)
    G = np.zeros((m, m), dtype=np.uint8)
    for i, s in enumerate(active):
        for j, t in enumerate(active):
            G[i, j] = bilinear(N, B[t], C[s])  # row s: c_s^T N b_t
    return G


def all_2x2_minors_zero(M: np.ndarray) -> bool:
    m, n = M.shape
    for i in range(m):
        for j in range(i + 1, m):
            for k in range(n):
                for l in range(k + 1, n):
                    if int((M[i, k] & M[j, l]) ^ (M[i, l] & M[j, k])):
                        return False
    return True


def analyze_scheme(T_core: np.ndarray, c_ranks: dict[int, int], row: np.ndarray, idx: int) -> dict:
    A, B, C = term_lists(row)
    verified = bool(np.array_equal(reconstruct_from_terms(row, T_core.shape), T_core))
    totals = Counter()
    failures = []
    examples = []
    for q, rho in sorted(c_ranks.items()):
        active = [s for s, a in enumerate(A) if ((int(a) & int(q)).bit_count() & 1)]
        h = len(active)
        if h < rho or rho == 0:
            continue
        M = contraction_matrix(T_core, q)
        N = generalized_inverse(M)
        totals[f"rank{rho}_hit{h}"] += 1
        if h == rho:
            G = gamma_matrix(N, B, C, active)
            ok = np.array_equal(G, np.eye(h, dtype=np.uint8))
            totals[f"rank{rho}_tight_tests"] += 1
            totals[f"rank{rho}_tight_failures"] += int(not ok)
            if (not ok) and len(failures) < 5:
                failures.append({"q": int(q), "rank": int(rho), "hit": int(h), "gamma": G.tolist(), "active": active})
            if ok and len(examples) < 6:
                examples.append({"kind": "tight", "q": int(q), "rank": int(rho), "active": active[:12]})
        if rho == 9 and h == 10:
            Minv = N
            G = gamma_matrix(Minv, B, C, active)
            Q2_ok = np.array_equal((G @ G) & 1, G)
            D = G ^ np.eye(h, dtype=np.uint8)
            dr = mat_rank_f2(D)
            minors = all_2x2_minors_zero(D)
            ok = Q2_ok and dr == 1 and minors
            totals["rank9_defect1_tests"] += 1
            totals["rank9_defect1_failures"] += int(not ok)
            if (not ok) and len(failures) < 5:
                failures.append({"q": int(q), "rank": 9, "hit": 10, "idempotent": Q2_ok, "rank_Q_plus_I": dr, "minors_zero": minors, "active": active})
            if ok and len(examples) < 6:
                examples.append({"kind": "defect1", "q": int(q), "rank": 9, "active": active[:12], "rank_Q_plus_I": dr})
    return {"scheme_index": int(idx), "verified": verified, "totals": {k: int(v) for k, v in sorted(totals.items())}, "failures_head": failures, "examples_head": examples}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pool-limit", type=int, default=12)
    ap.add_argument("--out", type=Path, default=OUTDIR / "spectral_resolution_controls.json")
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    result = {
        "schema": "spectral_resolution_controls_v1",
        "field": "F2",
        "purpose": "Validate full tight-contraction spectral equations and defect-one rank condition on known rank-21 core decompositions.",
        "pool_limit": int(args.pool_limit),
        "cores": {},
    }
    t0 = time.time()
    for name, cfg in CORES.items():
        print(f"=== {name} ===", flush=True)
        T_core, _ = quotient_core_from_mask(cfg["mask"])
        c_ranks = contraction_ranks(T_core)
        pool = np.load(cfg["pool_file"], allow_pickle=True)
        records = []
        totals = Counter()
        for idx, row in enumerate(pool[: args.pool_limit]):
            rec = analyze_scheme(T_core, c_ranks, row, idx)
            records.append(rec)
            for k, v in rec["totals"].items():
                totals[k] += int(v)
        result["cores"][name] = {
            "core_mask": int(cfg["mask"]),
            "pool_file": str(cfg["pool_file"]),
            "rank21_schemes_sampled": int(min(args.pool_limit, len(pool))),
            "aggregate_totals": {k: int(v) for k, v in sorted(totals.items())},
            "records_head": records,
        }
        print(json.dumps(result["cores"][name]["aggregate_totals"], sort_keys=True), flush=True)
    result["elapsed_sec"] = round(time.time() - t0, 3)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(args.out), "elapsed_sec": result["elapsed_sec"]}, indent=2))


if __name__ == "__main__":
    main()
