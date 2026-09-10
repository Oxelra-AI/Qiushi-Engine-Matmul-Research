#!/usr/bin/env python3
r"""analysis: exact block-diagonal budget boundary for all E11 dual-line pencils.

The E11 core contractions have the form Q^T \otimes I_3.  After grouping the
coordinates by the second matrix index, every contraction becomes three identical
3x3 blocks.  Therefore for any dual line <q1,q2>, the pencil budget condition
admits a structured witness if the budget (c10,c01,c11) dominates a three-block
sum of exact single-block triples

  (rank(Q1+Z_b), rank(Q2+Z_b), rank(Z_b)),  Z_b in Mat_3(F2).

This script compares that explicit block-diagonal feasible envelope with the
three individual contraction rank inequalities for every one of the 10,795 dual
lines and all budgets relevant to a length-19 support.
"""
from __future__ import annotations

import json
import sys
import time
from collections import Counter, defaultdict
from itertools import product
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import build_matmul_tensor_f2, contraction_matrix, mat_rank_f2

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/pencil_repair"


def enumerate_dual_lines(n: int = 8) -> List[Tuple[int,int,int]]:
    seen = set()
    lines = []
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


def gf2_mat_mul(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    return ((A.astype(np.uint8) @ B.astype(np.uint8)) % 2).astype(np.uint8)


def row_masks(M: np.ndarray) -> List[int]:
    out = []
    for i in range(M.shape[0]):
        m = 0
        for j in range(M.shape[1]):
            if int(M[i, j]) & 1:
                m |= 1 << j
        out.append(m)
    return out


def perm_current_to_grouped() -> np.ndarray:
    P = np.zeros((9, 9), dtype=np.uint8)
    for j in range(3):
        for k in range(3):
            cur = 3 * j + k
            grp = 3 * k + j
            P[grp, cur] = 1
    return P


def matrix_from_int_3(v: int) -> np.ndarray:
    M = np.zeros((3, 3), dtype=np.uint8)
    for i in range(9):
        if (v >> i) & 1:
            M[i // 3, i % 3] = 1
    return M


def grouped_block(M: np.ndarray, P: np.ndarray) -> Tuple[bool, np.ndarray, Dict[str, object]]:
    Mg = gf2_mat_mul(gf2_mat_mul(P, M), P.T)
    H = Mg[0:3, 0:3].copy()
    off = 0
    mismatch = 0
    for bi in range(3):
        for bj in range(3):
            block = Mg[3*bi:3*(bi+1), 3*bj:3*(bj+1)]
            if bi == bj:
                if not np.array_equal(block, H):
                    mismatch += 1
            else:
                off += int(block.sum())
    return off == 0 and mismatch == 0, H, {"off_nonzero": off, "diag_mismatch": mismatch, "grouped_rows": row_masks(Mg)}


def minimal_triples(triples: Iterable[Tuple[int,int,int]]) -> List[Tuple[int,int,int]]:
    ts = sorted(set(triples))
    mins = []
    for t in ts:
        if not any(all(u[i] <= t[i] for i in range(3)) and any(u[i] < t[i] for i in range(3)) for u in ts if u != t):
            mins.append(t)
    return mins


def block_envelope(A: np.ndarray, B: np.ndarray) -> Tuple[set[Tuple[int,int,int]], List[Tuple[int,int,int]]]:
    single = []
    for z in range(1 << 9):
        Z = matrix_from_int_3(z)
        single.append((
            int(mat_rank_f2((A + Z) % 2)),
            int(mat_rank_f2((B + Z) % 2)),
            int(mat_rank_f2(Z)),
        ))
    single = sorted(set(single))
    sums = set()
    for t1 in single:
        for t2 in single:
            for t3 in single:
                sums.add((t1[0]+t2[0]+t3[0], t1[1]+t2[1]+t3[1], t1[2]+t2[2]+t3[2]))
    return sums, minimal_triples(sums)


def dominates_some(budget: Tuple[int,int,int], triples: Iterable[Tuple[int,int,int]]) -> bool:
    return any(all(t[i] <= budget[i] for i in range(3)) for t in triples)


def budget_passes_individual(b: Tuple[int,int,int], ranks: Tuple[int,int,int]) -> bool:
    c10, c01, c11 = b
    r1, r2, r3 = ranks
    return c10 + c11 >= r1 and c01 + c11 >= r2 and c10 + c01 >= r3


def individual_minimal(ranks: Tuple[int,int,int], total_len: int = 19) -> List[Tuple[int,int,int]]:
    passing = []
    for c10 in range(total_len + 1):
        for c01 in range(total_len + 1 - c10):
            for c11 in range(total_len + 1 - c10 - c01):
                b = (c10, c01, c11)
                if budget_passes_individual(b, ranks):
                    passing.append(b)
    return minimal_triples(passing)


def main() -> None:
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    T = build_matmul_tensor_f2()[1:, :, :].astype(np.uint8) % 2
    P = perm_current_to_grouped()
    cdata = {}
    block_data = {}
    contraction_group_failures = []
    for q in range(1, 256):
        M = contraction_matrix(T, q)
        ok, H, info = grouped_block(M, P)
        if not ok:
            contraction_group_failures.append({"q": q, "info": info})
        cdata[q] = {"M": M, "rank": int(mat_rank_f2(M))}
        block_data[q] = {"H": H, "H_rank": int(mat_rank_f2(H)), "H_rows": row_masks(H)}

    lines = enumerate_dual_lines(8)
    env_cache: Dict[Tuple[Tuple[int,...], Tuple[int,...]], Tuple[set, List[Tuple[int,int,int]]]] = {}
    line_failures = []
    by_rank_type = defaultdict(lambda: {
        "line_count": 0,
        "same_minimal_count": 0,
        "env_minimal_types": Counter(),
        "individual_minimal": None,
        "first_examples": [],
    })
    full_equiv_count = 0
    checked_budget_count = 0

    for line in lines:
        q1, q2, q3 = line
        A = block_data[q1]["H"]
        B = block_data[q2]["H"]
        key = (tuple(block_data[q1]["H_rows"]), tuple(block_data[q2]["H_rows"]))
        if key not in env_cache:
            env_cache[key] = block_envelope(A, B)
        sums, env_mins = env_cache[key]
        ranks = (cdata[q1]["rank"], cdata[q2]["rank"], cdata[q3]["rank"])
        indiv_mins = individual_minimal(ranks, 19)
        rt = ranks
        by_rank_type[rt]["line_count"] += 1
        by_rank_type[rt]["env_minimal_types"][tuple(env_mins)] += 1
        by_rank_type[rt]["individual_minimal"] = [list(x) for x in indiv_mins]
        if len(by_rank_type[rt]["first_examples"]) < 3:
            by_rank_type[rt]["first_examples"].append({
                "line": list(line),
                "H1_rows": block_data[q1]["H_rows"],
                "H2_rows": block_data[q2]["H_rows"],
                "env_minimal": [list(x) for x in env_mins],
            })

        same = set(env_mins) == set(indiv_mins)
        if same:
            by_rank_type[rt]["same_minimal_count"] += 1

        # Directly compare every support-relevant budget, not only minimal sets.
        missing = []
        extra = []
        for c10 in range(20):
            for c01 in range(20 - c10):
                for c11 in range(20 - c10 - c01):
                    b = (c10, c01, c11)
                    ib = budget_passes_individual(b, ranks)
                    fea = dominates_some(b, sums)
                    checked_budget_count += 1
                    if ib and not fea:
                        missing.append(b)
                    if fea and not ib:
                        extra.append(b)
        if not missing and not extra:
            full_equiv_count += 1
        else:
            line_failures.append({
                "line": list(line),
                "ranks": list(ranks),
                "env_minimal": [list(x) for x in env_mins],
                "individual_minimal": [list(x) for x in indiv_mins],
                "missing_ib_budgets_head": [list(x) for x in missing[:20]],
                "extra_non_ib_budgets_head": [list(x) for x in extra[:20]],
                "missing_count": len(missing),
                "extra_count": len(extra),
            })

    rank_summary = {}
    for rt, rec in sorted(by_rank_type.items()):
        env_types = []
        for mins_tuple, cnt in rec["env_minimal_types"].most_common():
            env_types.append({"count": cnt, "minimal": [list(x) for x in mins_tuple]})
        rank_summary[str(rt)] = {
            "line_count": rec["line_count"],
            "same_minimal_count": rec["same_minimal_count"],
            "individual_minimal": rec["individual_minimal"],
            "env_minimal_type_count": len(env_types),
            "env_minimal_types_head": env_types[:5],
            "first_examples": rec["first_examples"],
        }

    out = {
        "schema": "pencil_boundary_all_lines_v1",
        "elapsed_sec": time.time() - t0,
        "contraction_group_failures": contraction_group_failures,
        "dual_line_count": len(lines),
        "unique_ordered_block_pair_count": len(env_cache),
        "full_budget_equivalence_line_count": full_equiv_count,
        "line_failure_count": len(line_failures),
        "line_failures_head": line_failures[:20],
        "checked_budget_assignments_with_sum_le_19": checked_budget_count,
        "rank_type_summary": rank_summary,
        "conclusion": {
            "support_level_dual_line_pencil_adds_over_individual_rank_bounds_for_length19": bool(len(line_failures) > 0),
            "statement": "For every checked E11 dual line and every color budget c10+c01+c11<=19, the explicit 3-block pencil envelope is equivalent to the three individual contraction rank inequalities." if not line_failures else "Some lines/budgets are not covered by the explicit block envelope; inspect line_failures_head.",
        },
    }
    out_path = OUTDIR / "pencil_boundary_all_lines.json"
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out_path),
        "dual_lines": len(lines),
        "contraction_group_failures": len(contraction_group_failures),
        "unique_ordered_block_pair_count": len(env_cache),
        "full_budget_equivalence_line_count": full_equiv_count,
        "line_failure_count": len(line_failures),
        "elapsed_sec": time.time() - t0,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
