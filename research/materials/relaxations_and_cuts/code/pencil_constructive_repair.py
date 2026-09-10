#!/usr/bin/env python3
r"""analysis: repair the analysis dual-line pencil inference.

analysis reported many pencil "infeasibilities" based on random search and a
one-side-tight sampler.  The review pointed out two mathematical problems:
  (i) the flagship cases were not analytically/exhaustively proved, and
  (ii) the sampler effectively searched rank(Z)=c11 factorizations, while the
       necessary pencil condition is rank(Z) <= c11.

This script reconstructs explicit witnesses for all-rank-9 E11 quotient lines
using the structure M1^{-1} M2 = H \otimes I_3 (in the current B/C ordering).
After permuting coordinates, this is three independent 3x3 blocks.  For each
block one can realize rank triples (rank(I+W), rank(H+W), rank(W)) equal to
(1,2,2), (2,1,2), or (2,2,1); direct sums give base triples
(6-a,6-b,6-c), a+b+c=3, and upward closure gives explicit feasible budgets.

The script:
  * verifies the Kronecker/block normalization for all all-rank-9 dual lines;
  * constructs direct witnesses for the flagship lines [42,149,191] and
    [55,141,186], checking the original 9x9 ranks;
  * enumerates all 3x3 block witnesses and the 3-block block-diagonal attainable
    envelope for every all-rank-9 line;
  * compares analysis stored negative classifications with this envelope;
  * writes a JSON repair record and a Markdown invalidation notice.

The output deliberately does not claim infeasibility for any line not covered by
an explicit feasible witness.  Such budgets remain unresolved by this script.
"""
from __future__ import annotations

import json
import sys
import time
from collections import Counter, defaultdict
from itertools import product
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import build_matmul_tensor_f2, contraction_matrix, mat_rank_f2
from dual_basis_instrument import gf2_mat_inv, gf2_mat_mul

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/pencil_repair"
JSON = ROOT / "workspace/data/pencil_pilot/analytical_pencil_results.json"
NOTE = ROOT / "workspace/notes/pencil_repair_and_envelope.md"

NEAR_MISS = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]
FLAGSHIP_LINES = [(42,149,191), (55,141,186)]


def dot_bits(a: int, b: int) -> int:
    return (a & b).bit_count() & 1


def build_e11_core_tensor() -> np.ndarray:
    return build_matmul_tensor_f2()[1:, :, :].astype(np.uint8) % 2


def enumerate_dual_lines(n: int = 8) -> List[Tuple[int,int,int]]:
    seen = set()
    lines: List[Tuple[int,int,int]] = []
    for q1 in range(1, 1 << n):
        for q2 in range(q1 + 1, 1 << n):
            q3 = q1 ^ q2
            if q3 == 0:
                continue
            line = tuple(sorted((q1, q2, q3)))
            if line in seen:
                continue
            seen.add(line)
            lines.append(line)
    return lines


def perm_current_to_grouped() -> np.ndarray:
    """Permutation P with y=P x, y[3*k+j] = x[3*j+k].

    Current matrix ordering is (first_index, second_index) with index 3*i+j.
    For contractions this makes Q^T \otimes I_3.  Grouping by the second index
    turns H \otimes I_3 into I_3 \otimes H, i.e. three 3x3 blocks.
    """
    P = np.zeros((9, 9), dtype=np.uint8)
    for j in range(3):
        for k in range(3):
            cur = 3 * j + k
            grp = 3 * k + j
            P[grp, cur] = 1
    return P


def gf2_add(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    return (A.astype(np.uint8) ^ B.astype(np.uint8))


def mat_to_rows(M: np.ndarray) -> List[List[int]]:
    return [[int(x) for x in row] for row in M.tolist()]


def row_masks(M: np.ndarray) -> List[int]:
    rows = []
    for i in range(M.shape[0]):
        mask = 0
        for j in range(M.shape[1]):
            if int(M[i, j]) & 1:
                mask |= 1 << j
        rows.append(mask)
    return rows


def matrix_from_int_3(v: int) -> np.ndarray:
    M = np.zeros((3, 3), dtype=np.uint8)
    for i in range(9):
        if (v >> i) & 1:
            M[i // 3, i % 3] = 1
    return M


def matrix_to_int_3(M: np.ndarray) -> int:
    v = 0
    for i in range(3):
        for j in range(3):
            if int(M[i, j]) & 1:
                v |= 1 << (3 * i + j)
    return v


def vec3_from_mask(mask: int) -> np.ndarray:
    return np.array([(mask >> i) & 1 for i in range(3)], dtype=np.uint8).reshape(3, 1)


def dot3(v: int, w: int) -> int:
    return (v & w).bit_count() & 1


def kron2(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    return np.kron(A.astype(np.uint8), B.astype(np.uint8)).astype(np.uint8) % 2


def block_diag(blocks: Sequence[np.ndarray]) -> np.ndarray:
    n = sum(b.shape[0] for b in blocks)
    M = np.zeros((n, n), dtype=np.uint8)
    off = 0
    for b in blocks:
        m = b.shape[0]
        M[off:off+m, off:off+m] = b.astype(np.uint8) % 2
        off += m
    return M


def extract_grouped_H(A_current: np.ndarray, P: np.ndarray) -> Tuple[bool, Optional[np.ndarray], Dict[str, object]]:
    """Check P A P^T = diag(H,H,H)."""
    A_g = gf2_mat_mul(gf2_mat_mul(P, A_current), P.T) % 2
    H = A_g[0:3, 0:3].copy()
    off_nonzero = 0
    diag_mismatch = 0
    for bi in range(3):
        for bj in range(3):
            block = A_g[3*bi:3*(bi+1), 3*bj:3*(bj+1)]
            if bi == bj:
                if not np.array_equal(block, H):
                    diag_mismatch += 1
            else:
                off_nonzero += int(block.sum())
    ok = off_nonzero == 0 and diag_mismatch == 0
    return ok, H if ok else None, {
        "A_grouped_row_masks": row_masks(A_g),
        "off_block_nonzero_entries": off_nonzero,
        "diag_block_mismatch_count": diag_mismatch,
        "H_rank": int(mat_rank_f2(H)) if ok else None,
        "H_plus_I_rank": int(mat_rank_f2((H + np.eye(3, dtype=np.uint8)) % 2)) if ok else None,
    }


def rank_triple_block(H: np.ndarray, W: np.ndarray) -> Tuple[int,int,int]:
    I = np.eye(3, dtype=np.uint8)
    return (
        int(mat_rank_f2((I + W) % 2)),
        int(mat_rank_f2((H + W) % 2)),
        int(mat_rank_f2(W)),
    )


def enumerate_block_witnesses(H: np.ndarray) -> Dict[Tuple[int,int,int], np.ndarray]:
    """Return one 3x3 W for each attainable block rank triple."""
    witnesses: Dict[Tuple[int,int,int], np.ndarray] = {}
    for v in range(1 << 9):
        W = matrix_from_int_3(v)
        tri = rank_triple_block(H, W)
        witnesses.setdefault(tri, W)
    return witnesses


def minimal_triples(triples: Iterable[Tuple[int,int,int]]) -> List[Tuple[int,int,int]]:
    ts = sorted(set(triples))
    mins = []
    for t in ts:
        dominated = False
        for u in ts:
            if u == t:
                continue
            if all(u[i] <= t[i] for i in range(3)) and any(u[i] < t[i] for i in range(3)):
                dominated = True
                break
        if not dominated:
            mins.append(t)
    return mins


def combine_three_block_envelope(block_wits: Dict[Tuple[int,int,int], np.ndarray]) -> Tuple[Dict[Tuple[int,int,int], List[np.ndarray]], List[Tuple[int,int,int]]]:
    """Exact block-diagonal 3-block sums, storing one W-block list per sum."""
    triples = list(block_wits.keys())
    sums: Dict[Tuple[int,int,int], List[np.ndarray]] = {}
    # Use all attainable block triples, not only the three.  This is
    # the exact boundary for block-diagonal witnesses in the normalized basis.
    for t1 in triples:
        for t2 in triples:
            for t3 in triples:
                s = (t1[0]+t2[0]+t3[0], t1[1]+t2[1]+t3[1], t1[2]+t2[2]+t3[2])
                if s not in sums:
                    sums[s] = [block_wits[t1], block_wits[t2], block_wits[t3]]
    mins = minimal_triples(sums.keys())
    return sums, mins


def find_dominated_sum(budget: Tuple[int,int,int], sums: Dict[Tuple[int,int,int], List[np.ndarray]]) -> Optional[Tuple[int,int,int]]:
    candidates = [s for s in sums if all(s[i] <= budget[i] for i in range(3))]
    if not candidates:
        return None
    # Prefer a minimal total-rank witness, then lexicographic for determinism.
    return sorted(candidates, key=lambda x: (sum(x), x))[0]


def color_counts_for_support(line: Tuple[int,int,int], support: Sequence[int]) -> Tuple[int,int,int,int]:
    q1, q2, _ = line
    c00 = c10 = c01 = c11 = 0
    for p in support:
        e1 = dot_bits(q1, p)
        e2 = dot_bits(q2, p)
        if e1 == 0 and e2 == 0:
            c00 += 1
        elif e1 == 1 and e2 == 0:
            c10 += 1
        elif e1 == 0 and e2 == 1:
            c01 += 1
        else:
            c11 += 1
    return c00, c10, c01, c11


def find_strategist_block_witness(H: np.ndarray, kind: int) -> Dict[str, object]:
    """Construct one of the three per-block triples, with formula where useful.

    kind 0 -> target (1,2,2) for (rank(I+W), rank(H+W), rank(W))
    kind 1 -> target (2,1,2)
    kind 2 -> target (2,2,1)
    """
    I = np.eye(3, dtype=np.uint8)
    H_inv = gf2_mat_inv(H)
    HpI_inv = gf2_mat_inv((H + I) % 2)
    assert H_inv is not None and HpI_inv is not None

    def outer(u_mask: int, v_mask: int) -> np.ndarray:
        u = vec3_from_mask(u_mask)
        v = vec3_from_mask(v_mask).reshape(1, 3)
        return (u @ v).astype(np.uint8) % 2

    if kind == 0:
        # W = I + u v^T, with t=(H+I)^{-1}u and v^T u = v^T t = 1.
        for u_mask in range(1, 8):
            u = vec3_from_mask(u_mask)
            t_vec = gf2_mat_mul(HpI_inv, u) % 2
            t_mask = sum(int(t_vec[i,0]) << i for i in range(3))
            for v_mask in range(1, 8):
                if dot3(v_mask, u_mask) == 1 and dot3(v_mask, t_mask) == 1:
                    W = (I + outer(u_mask, v_mask)) % 2
                    tri = rank_triple_block(H, W)
                    if tri == (1,2,2):
                        return {"W": W, "triple": tri, "u": u_mask, "t": t_mask, "v": v_mask, "method": "I_plus_uvT"}
    elif kind == 1:
        # Reduce M2+Z instead.  Construct W0 for H^{-1}, then W=H W0.
        Hinv_p_I_inv = gf2_mat_inv((H_inv + I) % 2)
        assert Hinv_p_I_inv is not None
        for u_mask in range(1, 8):
            u = vec3_from_mask(u_mask)
            t_vec = gf2_mat_mul(Hinv_p_I_inv, u) % 2
            t_mask = sum(int(t_vec[i,0]) << i for i in range(3))
            for v_mask in range(1, 8):
                if dot3(v_mask, u_mask) == 1 and dot3(v_mask, t_mask) == 1:
                    W0 = (I + outer(u_mask, v_mask)) % 2
                    W = gf2_mat_mul(H, W0) % 2
                    tri = rank_triple_block(H, W)
                    if tri == (2,1,2):
                        return {"W": W, "triple": tri, "u": u_mask, "t": t_mask, "v": v_mask, "method": "H_times_I_plus_uvT_for_Hinv"}
    else:
        # Make Z itself rank one while both I+W and H+W have rank two.
        for u_mask in range(1, 8):
            Hu_vec = gf2_mat_mul(H_inv, vec3_from_mask(u_mask)) % 2
            Hu_mask = sum(int(Hu_vec[i,0]) << i for i in range(3))
            for v_mask in range(1, 8):
                if dot3(v_mask, u_mask) == 1 and dot3(v_mask, Hu_mask) == 1:
                    W = outer(u_mask, v_mask)
                    tri = rank_triple_block(H, W)
                    if tri == (2,2,1):
                        return {"W": W, "triple": tri, "u": u_mask, "t": Hu_mask, "v": v_mask, "method": "uvT"}

    # Robust fallback: exact 512-matrix search, should not be needed.
    target = [(1,2,2), (2,1,2), (2,2,1)][kind]
    for W in enumerate_block_witnesses(H).values():
        if rank_triple_block(H, W) == target:
            return {"W": W, "triple": target, "method": "enumerated_fallback"}
    raise RuntimeError(f"No block witness for target {target}")


def constructive_special_base_witness(H: np.ndarray, base: Tuple[int,int,int]) -> Optional[List[np.ndarray]]:
    """Construct direct-sum blocks using only the three review base types."""
    # base=(6-a,6-b,6-c), a+b+c=3.  kind 0 lowers first coordinate, etc.
    deficits = [6 - base[i] for i in range(3)]
    if any(d < 0 for d in deficits) or sum(deficits) != 3:
        return None
    blocks = []
    wits = [find_strategist_block_witness(H, k)["W"] for k in range(3)]
    for kind, count in enumerate(deficits):
        for _ in range(count):
            blocks.append(wits[kind])
    if len(blocks) != 3:
        return None
    return blocks


def check_9x9_witness(M1: np.ndarray, M2: np.ndarray, W_current: np.ndarray, budget: Tuple[int,int,int]) -> Dict[str, object]:
    Z = gf2_mat_mul(M1, W_current) % 2
    rZ = int(mat_rank_f2(Z))
    r1 = int(mat_rank_f2((M1 + Z) % 2))
    r2 = int(mat_rank_f2((M2 + Z) % 2))
    return {
        "ranks_order_c10_c01_c11": [r1, r2, rZ],
        "budget_order_c10_c01_c11": list(budget),
        "passes_original_rank_inequalities": bool(r1 <= budget[0] and r2 <= budget[1] and rZ <= budget[2]),
        "Z_row_masks": row_masks(Z),
        "W_current_row_masks": row_masks(W_current),
    }


def analyze_line(line: Tuple[int,int,int], cdata: Dict[int,dict], P: np.ndarray, support: Sequence[int]) -> Dict[str, object]:
    q1, q2, q3 = line
    M1, M2, M3 = cdata[q1]["M"], cdata[q2]["M"], cdata[q3]["M"]
    ranks = (cdata[q1]["rank"], cdata[q2]["rank"], cdata[q3]["rank"])
    colors = color_counts_for_support(line, support)
    budget = (colors[1], colors[2], colors[3])
    out: Dict[str, object] = {
        "line": list(line),
        "colors_c00_c10_c01_c11": list(colors),
        "budget_c10_c01_c11": list(budget),
        "contraction_ranks": list(ranks),
        "individual_bounds_pass": bool(budget[0] + budget[2] >= ranks[0] and budget[1] + budget[2] >= ranks[1] and budget[0] + budget[1] >= ranks[2]),
    }
    if ranks != (9,9,9):
        out["all_rank9"] = False
        return out
    out["all_rank9"] = True
    M1_inv = gf2_mat_inv(M1)
    assert M1_inv is not None
    A = gf2_mat_mul(M1_inv, M2) % 2
    ok, H, norm = extract_grouped_H(A, P)
    out["normalization"] = norm
    out["normalization_ok_diag_H"] = bool(ok)
    if not ok or H is None:
        return out
    block_wits = enumerate_block_witnesses(H)
    sums, mins = combine_three_block_envelope(block_wits)
    dom = find_dominated_sum(budget, sums)
    out["block_single_minimal_triples"] = [list(t) for t in minimal_triples(block_wits.keys())]
    out["blockdiag_threeblock_minimal_triples"] = [list(t) for t in mins]
    out["blockdiag_envelope_feasible"] = dom is not None
    out["dominating_base_triple"] = list(dom) if dom is not None else None
    out["H_row_masks"] = row_masks(H)

    # Verify three fundamental block witnesses.
    special = []
    for kind in range(3):
        rec = find_strategist_block_witness(H, kind)
        special.append({
            "kind": kind,
            "method": rec["method"],
            "triple": list(rec["triple"]),
            "W_row_masks": row_masks(rec["W"]),
            "u": rec.get("u"),
            "t": rec.get("t"),
            "v": rec.get("v"),
        })
    out["strategist_block_witnesses"] = special

    if dom is not None:
        blocks = sums[dom]
        W_grouped = block_diag(blocks)
        W_current = gf2_mat_mul(gf2_mat_mul(P.T, W_grouped), P) % 2
        wit_check = check_9x9_witness(M1, M2, W_current, budget)
        wit_check["W_grouped_row_masks"] = row_masks(W_grouped)
        out["explicit_9x9_witness_check"] = wit_check

        # If the budget dominates one of the simple (6-a,6-b,6-c) triples,
        # also store a witness built only from the three closed-form block types.
        simple_bases = []
        for a in range(4):
            for b in range(4-a):
                c = 3 - a - b
                base = (6-a, 6-b, 6-c)
                if all(base[i] <= budget[i] for i in range(3)):
                    simple_bases.append(base)
        out["simple_strategist_bases_dominated"] = [list(x) for x in simple_bases]
        if simple_bases:
            base = sorted(simple_bases, key=lambda x: (sum(x), x))[0]
            sblocks = constructive_special_base_witness(H, base)
            if sblocks is not None:
                Wg2 = block_diag(sblocks)
                Wc2 = gf2_mat_mul(gf2_mat_mul(P.T, Wg2), P) % 2
                out["simple_strategist_9x9_witness_check"] = {
                    "base": list(base),
                    **check_9x9_witness(M1, M2, Wc2, budget),
                    "W_grouped_row_masks": row_masks(Wg2),
                }
    return out


def main() -> None:
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    T_core = build_e11_core_tensor()
    cdata: Dict[int, dict] = {}
    for q in range(1, 256):
        M = contraction_matrix(T_core, q)
        cdata[q] = {"rank": int(mat_rank_f2(M)), "M": M}
    rank_hist = Counter(rec["rank"] for rec in cdata.values())
    lines = enumerate_dual_lines(8)
    r9_lines = [ln for ln in lines if all(cdata[q]["rank"] == 9 for q in ln)]
    P = perm_current_to_grouped()

    # Verify every all-rank-9 line has the expected block normalization.
    norm_failures = []
    H_hist = Counter()
    H_minimal_envelopes = {}
    all_r9_envelope_records = []
    for line in r9_lines:
        q1, q2, _ = line
        M1_inv = gf2_mat_inv(cdata[q1]["M"])
        assert M1_inv is not None
        A = gf2_mat_mul(M1_inv, cdata[q2]["M"]) % 2
        ok, H, norm = extract_grouped_H(A, P)
        if not ok or H is None:
            norm_failures.append({"line": list(line), "normalization": norm})
            continue
        H_key = tuple(row_masks(H))
        H_hist[H_key] += 1
        if H_key not in H_minimal_envelopes:
            bw = enumerate_block_witnesses(H)
            sums, mins = combine_three_block_envelope(bw)
            H_minimal_envelopes[str(H_key)] = {
                "H_row_masks": list(H_key),
                "H_rank": int(mat_rank_f2(H)),
                "H_plus_I_rank": int(mat_rank_f2((H + np.eye(3, dtype=np.uint8)) % 2)),
                "block_minimal_triples": [list(t) for t in minimal_triples(bw.keys())],
                "threeblock_minimal_triples": [list(t) for t in mins],
                "threeblock_sum_count": len(sums),
            }
        colors = color_counts_for_support(line, NEAR_MISS)
        budget = (colors[1], colors[2], colors[3])
        bw = enumerate_block_witnesses(H)
        sums, _ = combine_three_block_envelope(bw)
        dom = find_dominated_sum(budget, sums)
        all_r9_envelope_records.append({
            "line": list(line),
            "colors_c00_c10_c01_c11": list(colors),
            "budget_c10_c01_c11": list(budget),
            "blockdiag_envelope_feasible": dom is not None,
            "dominating_base_triple": list(dom) if dom else None,
        })

    # Analyze flagship lines and a few stored cases in detail.
    detailed_lines = {}
    requested_lines = list(FLAGSHIP_LINES) + [(78,185,247)]
    for line in requested_lines:
        detailed_lines[str(line)] = analyze_line(line, cdata, P, NEAR_MISS)

    # Compare analysis stored tests, especially negative random_2000 entries.
    analysis = json.loads(JSON.read_text()) if JSON.exists() else {}
    corrected_tests = []
    correction_counts = Counter()
    for rec in analysis.get("tests", []):
        line = tuple(rec["line"])
        colors = tuple(rec["colors"])
        # analysis colors order is c00,c10,c01,c11.
        budget = (colors[1], colors[2], colors[3])
        a = analyze_line(line, cdata, P, NEAR_MISS)
        feasible = bool(a.get("blockdiag_envelope_feasible", False))
        old_method = rec.get("pencil_detail", {}).get("method")
        old_feasible = bool(rec.get("pencil_feasible"))
        if old_feasible:
            status = "old_feasible_kept"
        elif feasible:
            status = "old_negative_corrected_to_constructively_feasible"
        elif old_method and old_method.startswith("random"):
            status = "old_random_negative_reclassified_unresolved"
        else:
            status = "old_negative_reclassified_unresolved"
        correction_counts[status] += 1
        corrected_tests.append({
            "line": list(line),
            "old_pencil_feasible": old_feasible,
            "old_method": old_method,
            "old_colors_c00_c10_c01_c11": list(colors),
            "budget_c10_c01_c11": list(budget),
            "new_status": status,
            "blockdiag_envelope_feasible": feasible,
            "dominating_base_triple": a.get("dominating_base_triple"),
            "original_rank_check_passes": a.get("explicit_9x9_witness_check", {}).get("passes_original_rank_inequalities"),
        })

    r9_feasible_count = sum(1 for r in all_r9_envelope_records if r["blockdiag_envelope_feasible"])
    r9_budget_profile = Counter(tuple(r["budget_c10_c01_c11"]) for r in all_r9_envelope_records)
    r9_budget_feasible_profile = Counter(tuple(r["budget_c10_c01_c11"]) for r in all_r9_envelope_records if r["blockdiag_envelope_feasible"])

    output = {
        "schema": "pencil_constructive_repair_v1",
        "elapsed_sec": time.time() - t0,
        "near_miss_support": NEAR_MISS,
        "contraction_rank_histogram": dict(sorted(rank_hist.items())),
        "dual_line_count": len(lines),
        "all_rank9_line_count": len(r9_lines),
        "normalization_failures": norm_failures,
        "unique_H_count_for_all_rank9_lines": len(H_hist),
        "H_histogram": {str(k): v for k, v in H_hist.items()},
        "H_minimal_envelopes": H_minimal_envelopes,
        "all_rank9_near_miss_blockdiag_envelope": {
            "feasible_count": r9_feasible_count,
            "unresolved_count": len(all_r9_envelope_records) - r9_feasible_count,
            "records_head": all_r9_envelope_records[:25],
            "records_tail": all_r9_envelope_records[-25:],
            "budget_profile": {str(k): v for k, v in sorted(r9_budget_profile.items())},
            "budget_profile_constructively_feasible": {str(k): v for k, v in sorted(r9_budget_feasible_profile.items())},
        },
        "detailed_line_analyses": detailed_lines,
        "stored_test_reclassification": {
            "counts": dict(correction_counts),
            "records": corrected_tests,
        },
        "scientific_status": {
            "negative_classifications_valid_as_exclusions": False,
            "reason": "Most analysis negatives were random/sample failures for rank(Z)=c11-style factorizations, whereas the pencil condition allows rank(Z)<=c11; explicit lower-rank Z witnesses exist for flagship lines and many stored negative records.",
            "safe_use": "Only explicit feasible witnesses are established here. Budgets outside the block-diagonal constructive envelope remain unresolved, not infeasible.",
        },
    }
    out_json = OUTDIR / "pencil_constructive_repair.json"
    out_json.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")

    # Markdown research note / invalidation notice.
    flagship_summaries = []
    for line in FLAGSHIP_LINES:
        rec = detailed_lines[str(line)]
        chk = rec.get("simple_strategist_9x9_witness_check") or rec.get("explicit_9x9_witness_check")
        flagship_summaries.append(
            f"- line {list(line)} colors {rec['colors_c00_c10_c01_c11']} budget {rec['budget_c10_c01_c11']}: "
            f"witness ranks {chk['ranks_order_c10_c01_c11']} <= {chk['budget_order_c10_c01_c11']}, "
            f"pass={chk['passes_original_rank_inequalities']}."
        )
    note = f"""# analysis: repair of the dual-line pencil inference

## Correction

The analysis negative pencil classifications are not valid exclusions.  The stored
`analytical_pencil_results.json` marks many cases, including `[42,149,191]` and
`[55,141,186]`, by `random_2000`, not by an exhaustive algebraic test.  More
importantly, that search effectively looked for witnesses through rank-`c11`
factorizations, while the pencil condition is

```text
rank(Z) <= c11,  rank(M1+Z) <= c10,  rank(M2+Z) <= c01.
```

A lower-rank `Z` is allowed and can realize the flagship budgets.

## Explicit flagship witnesses checked in the original 9x9 inequalities

{chr(10).join(flagship_summaries)}

The witnesses are stored as row masks for `W` and `Z` in
`workspace/data/pencil_repair/pencil_constructive_repair.json` under
`detailed_line_analyses`.

## Structural envelope

For every all-rank-9 E11 dual line checked here, the normalized pencil satisfies
`M1^-1 M2 = H ⊗ I3` in the current ordering, or `diag(H,H,H)` after regrouping
coordinates.  The script verified {len(r9_lines)} all-rank-9 lines and found
{len(norm_failures)} normalization failures.  For each 3x3 block, exact
enumeration of all 512 matrices gives the block-rank triples; in particular the
three constructive triples `(1,2,2)`, `(2,1,2)`, and `(2,2,1)` are realized by
rank-one update formulas.  Combining three blocks gives a block-diagonal
constructive feasible envelope.  On the analysis near-miss, this envelope
constructively realizes {r9_feasible_count}/{len(r9_lines)} all-rank-9 line
budgets.  The remaining budgets are not excluded by this calculation; they are
only outside this explicit block-diagonal envelope.

## Reclassification of analysis stored tests

Counts: `{dict(correction_counts)}`.

No support-search cut should be generated from the 106 analysis reported
"infeasible" patterns.  Only future exclusions based on an exact full pencil
analysis or replayable proof may be used as necessary support consequences.

## Consequence for the main E11 distinct branch

The pencil formulation remains a useful local B/C compatibility question, but
analysis did not establish a new separating obstruction.  The central search must
continue using complete Wang rows, transported radius-three overlap cuts, and
validated compatibility tests, with pencil information admitted only when it is
constructive or rigorously proved.
"""
    NOTE.write_text(note)

    print(json.dumps({
        "out_json": str(out_json),
        "note": str(NOTE),
        "all_rank9_lines": len(r9_lines),
        "normalization_failures": len(norm_failures),
        "near_miss_blockdiag_feasible": r9_feasible_count,
        "near_miss_blockdiag_unresolved": len(r9_lines)-r9_feasible_count,
        "reclassification_counts": dict(correction_counts),
        "flagship_passes": {
            str(line): (detailed_lines[str(line)].get("simple_strategist_9x9_witness_check") or detailed_lines[str(line)].get("explicit_9x9_witness_check", {})).get("passes_original_rank_inequalities")
            for line in FLAGSHIP_LINES
        }
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
