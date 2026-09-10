#!/usr/bin/env python3
r"""Independent research_record review of the E11 block-spread structure reported by research_record.

This is not a copy of the peer checker.  It rebuilds the E11 core from the tensor
convention T[3i+j,3j+k,3i+k]=1, checks the contiguous B/C block convention, and
verifies the rank-21 pool rows against the block-spread consequences:
  R1: each active slice has at least three own-block hitters;
  R2: no active slice has exactly one hitter in any off-block;
  purity/GL3 for capacity-3 slices;
  no term is active in two capacity-3 slices.
These are necessary consequences of exact E11 core decompositions, not sufficient
conditions for a rank-19 decomposition.
"""
from __future__ import annotations

import json
import sys
import time
from collections import Counter
from pathlib import Path
from typing import List, Sequence, Tuple

import numpy as np

ROOT = Path("research/research_record")
OUT = ROOT / "workspace/data/block_spread/independent_block_spread_review.json"
PEER_POOL = Path("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy")
GROUPS = [0b000000111, 0b000111000, 0b111000000]
FULL9 = (1 << 9) - 1


def gf2_rank(M: np.ndarray) -> int:
    A = np.array(M, dtype=np.uint8, copy=True) & 1
    m, n = A.shape
    r = 0
    for c in range(n):
        piv = -1
        for i in range(r, m):
            if A[i, c]:
                piv = i
                break
        if piv < 0:
            continue
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for i in range(m):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        r += 1
        if r == m:
            break
    return r


def slice_block(s: int) -> Tuple[int, int]:
    """E11 core slice s corresponds to A-index a=s+1=3*i+j and block R_j x C_i."""
    a = s + 1
    return a % 3, a // 3


def build_core() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3 * i + j, 3 * j + k, 3 * i + k] = 1
    return T[1:].copy()


def extract_group_vector(mask: int, g: int) -> np.ndarray:
    return np.array([(int(mask) >> (3 * g + k)) & 1 for k in range(3)], dtype=np.uint8)


def check_core_block_structure(Tcore: np.ndarray) -> dict:
    errors = []
    for s in range(8):
        j, i = slice_block(s)
        expected = np.zeros((9, 9), dtype=np.uint8)
        for k in range(3):
            expected[3*j+k, 3*i+k] = 1
        if not np.array_equal(Tcore[s], expected):
            errors.append(s)
    # contraction convention check: for any lambda, contracted matrix is Lambda^T tensor I3.
    contraction_mismatch = []
    A_positions = [(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
    for lam in range(1, 256):
        contracted = np.zeros((9, 9), dtype=np.uint8)
        Lambda = np.zeros((3, 3), dtype=np.uint8)
        for bit, (ii, jj) in enumerate(A_positions):
            if (lam >> bit) & 1:
                contracted ^= Tcore[bit]
                Lambda[ii, jj] = 1
        expected = np.kron(Lambda.T, np.eye(3, dtype=np.uint8)) & 1
        if not np.array_equal(contracted, expected):
            contraction_mismatch.append(lam)
            if len(contraction_mismatch) >= 5:
                break
    return {
        "nnz": int(Tcore.sum()),
        "block_structure_errors": errors,
        "contraction_mismatch_head": contraction_mismatch,
        "contraction_all_match_LambdaT_tensor_I3": not contraction_mismatch,
    }


def brent_ok(row: np.ndarray, R: int, Tcore: np.ndarray) -> bool:
    recon = np.zeros_like(Tcore)
    for t in range(R):
        u = int(row[3*t]); v = int(row[3*t+1]); w = int(row[3*t+2])
        for s in range(8):
            if (u >> s) & 1:
                bbits = [b for b in range(9) if (v >> b) & 1]
                cbits = [c for c in range(9) if (w >> c) & 1]
                for b in bbits:
                    for c in cbits:
                        recon[s, b, c] ^= 1
    return bool(np.array_equal(recon, Tcore))


def check_row(row: np.ndarray, R: int) -> dict:
    us = [int(row[3*t]) for t in range(R)]
    vs = [int(row[3*t+1]) for t in range(R)]
    ws = [int(row[3*t+2]) for t in range(R)]
    v_meets = [[bool(vs[t] & GROUPS[g]) for g in range(3)] for t in range(R)]
    w_meets = [[bool(ws[t] & GROUPS[g]) for g in range(3)] for t in range(R)]

    caps = []
    r1_bad = []
    r2_bad = []
    purity_bad = []
    gl3_bad = []
    cap3_slices = []
    own_hit_counts = []
    for s in range(8):
        j, i = slice_block(s)
        active = [t for t in range(R) if (us[t] >> s) & 1]
        caps.append(len(active))
        own_hit = [t for t in active if v_meets[t][j] and w_meets[t][i]]
        own_hit_counts.append(len(own_hit))
        if len(own_hit) < 3:
            r1_bad.append({"slice": s, "own_hit_count": len(own_hit), "capacity": len(active)})
        for jj in range(3):
            for ii in range(3):
                if jj == j and ii == i:
                    continue
                off_hit = [t for t in active if v_meets[t][jj] and w_meets[t][ii]]
                if len(off_hit) == 1:
                    r2_bad.append({"slice": s, "off_block": [jj, ii], "term": off_hit[0]})
        if len(active) == 3:
            cap3_slices.append(s)
            pure = True
            for t in active:
                if vs[t] & (FULL9 ^ GROUPS[j]) or ws[t] & (FULL9 ^ GROUPS[i]):
                    purity_bad.append({"slice": s, "term": t, "v": vs[t], "w": ws[t]})
                    pure = False
            if pure:
                V = np.vstack([extract_group_vector(vs[t], j) for t in active])
                W = np.vstack([extract_group_vector(ws[t], i) for t in active])
                if gf2_rank(V) != 3 or gf2_rank(W) != 3:
                    gl3_bad.append({"slice": s, "rankV": gf2_rank(V), "rankW": gf2_rank(W)})
    cap3_shared = []
    for t in range(R):
        hit = [s for s in cap3_slices if (us[t] >> s) & 1]
        if len(hit) >= 2:
            cap3_shared.append({"term": t, "cap3_slices": hit})
    block_spread_sizes = []
    for t in range(R):
        nr = sum(v_meets[t])
        nc = sum(w_meets[t])
        block_spread_sizes.append(nr * nc)
    return {
        "caps": caps,
        "total_A_weight": int(sum(caps)),
        "p_capacity3": len(cap3_slices),
        "cap3_slices": cap3_slices,
        "own_hit_counts": own_hit_counts,
        "r1_bad": r1_bad,
        "r2_bad": r2_bad,
        "purity_bad": purity_bad,
        "gl3_bad": gl3_bad,
        "cap3_shared": cap3_shared,
        "block_spread_sizes": block_spread_sizes,
        "all_block_spread_ok": not (r1_bad or r2_bad or purity_bad or gl3_bad or cap3_shared),
    }


def derive_rank19_corner() -> dict:
    # Deterministic consequence of purity + R1: if p cap-3 slices exist in a 19-term decomposition,
    # their 3p pure terms cannot hit any other slice's own block.  p=6 leaves one non-pure term,
    # impossible for the two remaining slices requiring at least three own-block hitters.
    cases = []
    for p in range(9):
        free_terms = 19 - 3*p
        remaining_slices = 8 - p
        weight_lb = 3*p + 4*max(remaining_slices, 0)
        r1_possible_by_free_count = (remaining_slices <= 0) or (free_terms >= 3)
        cases.append({"p": p, "free_terms_after_cap3": free_terms, "remaining_slices": remaining_slices, "weight_lower_bound_if_possible": weight_lb, "not_immediately_ruled_out_by_R1_free_count": bool(free_terms >= 0 and r1_possible_by_free_count)})
    return {"cases": cases, "conclusion_for_rank19_core": "p_capacity3 <= 5 and total_A_weight >= 32-p >= 27"}


def main() -> None:
    t0 = time.time()
    Tcore = build_core()
    core_check = check_core_block_structure(Tcore)
    pool = np.load(PEER_POOL)
    N = int(pool.shape[0]); R = int(pool.shape[1] // 3)
    spot = min(25, N)
    brent_spot_ok = sum(1 for idx in range(spot) if brent_ok(pool[idx], R, Tcore))
    failures = []
    p_hist = Counter(); weight_hist = Counter(); spread_hist = Counter(); cap_profiles = Counter()
    for idx in range(N):
        rec = check_row(pool[idx], R)
        if not rec["all_block_spread_ok"] and len(failures) < 20:
            failures.append({"row": idx, **{k: rec[k] for k in ["caps", "r1_bad", "r2_bad", "purity_bad", "gl3_bad", "cap3_shared"]}})
        p_hist[rec["p_capacity3"]] += 1
        weight_hist[rec["total_A_weight"]] += 1
        cap_profiles[str(sorted(rec["caps"]))] += 1
        spread_hist.update(rec["block_spread_sizes"])
    payload = {
        "schema": "s0908_independent_block_spread_review_v1",
        "field": "F2",
        "meaning": "Independent verification of research_record block-spread necessary conditions on the shared rank-21 E11 core pool; no rank-19 construction or lower bound follows from this check alone.",
        "tensor_convention": "T[3i+j,3j+k,3i+k]=1; E11 core removes A index 0; core slice s=a-1 maps to block R_{a mod 3} x C_{floor(a/3)}.",
        "groups": {"R_j_and_C_i_masks": GROUPS},
        "core_check": core_check,
        "pool_path": str(PEER_POOL),
        "pool_rows": N,
        "rank_terms_in_pool": R,
        "brent_spot_check": {"checked": spot, "ok": int(brent_spot_ok)},
        "all_block_spread_pass": len(failures) == 0,
        "failure_examples": failures,
        "p_capacity3_histogram": dict(sorted(p_hist.items())),
        "total_A_weight_histogram": dict(sorted(weight_hist.items())),
        "min_total_A_weight": int(min(weight_hist) if weight_hist else 0),
        "max_p_capacity3": int(max(p_hist) if p_hist else 0),
        "capacity_profiles_top15": dict(cap_profiles.most_common(15)),
        "term_block_spread_histogram": dict(sorted(spread_hist.items())),
        "rank19_consequence_review": derive_rank19_corner(),
        "elapsed_sec": round(time.time() - t0, 3),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(OUT),
        "core_check": core_check,
        "pool_rows": N,
        "rank_terms_in_pool": R,
        "brent_spot_check": payload["brent_spot_check"],
        "all_block_spread_pass": payload["all_block_spread_pass"],
        "p_hist": payload["p_capacity3_histogram"],
        "weight_min": payload["min_total_A_weight"],
        "max_p": payload["max_p_capacity3"],
        "spread_hist": payload["term_block_spread_histogram"],
        "elapsed_sec": payload["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
