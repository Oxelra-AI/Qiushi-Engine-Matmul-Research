#!/usr/bin/env python3
r"""analysis: fast exact block-envelope comparison for E11 dual-line pencils.

For each E11 dual line <q1,q2>, group the 9x9 contractions into three 3x3
blocks.  A block-diagonal witness Z is obtained from three independent 3x3
matrices Z_b.  This gives an explicit feasible envelope for the pencil budgets
(c10,c01,c11).  Since the true pencil allows arbitrary 9x9 Z, this envelope is
a certified feasible subset; if it already covers every budget satisfying the
individual contraction rank inequalities, then the dual-line pencil supplies no
support-level budget cut beyond those inequalities.

This optimized script avoids the slow analysis all-lines script by using a 3x3
rank table and dynamic programming on the small set of single-block rank triples.
"""
from __future__ import annotations

import json
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from fixed_A_saturation import build_matmul_tensor_f2, contraction_matrix, mat_rank_f2

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/pencil_repair"


def enumerate_dual_lines(n: int = 8) -> List[Tuple[int,int,int]]:
    seen = set(); out = []
    for q1 in range(1, 1 << n):
        for q2 in range(q1 + 1, 1 << n):
            q3 = q1 ^ q2
            line = tuple(sorted((q1, q2, q3)))
            if line not in seen:
                seen.add(line); out.append(line)
    return out


def mat3_from_int(x: int) -> np.ndarray:
    M = np.zeros((3,3), dtype=np.uint8)
    for i in range(9):
        if (x >> i) & 1:
            M[i//3, i%3] = 1
    return M


def int_from_mat3(M: np.ndarray) -> int:
    x = 0
    for i in range(3):
        for j in range(3):
            if int(M[i,j]) & 1:
                x |= 1 << (3*i+j)
    return x


def row_masks(M: np.ndarray) -> List[int]:
    rows = []
    for i in range(M.shape[0]):
        x = 0
        for j in range(M.shape[1]):
            if int(M[i,j]) & 1:
                x |= 1 << j
        rows.append(x)
    return rows


def gf2_mat_mul(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    return ((A.astype(np.uint8) @ B.astype(np.uint8)) & 1).astype(np.uint8)


def perm_current_to_grouped() -> np.ndarray:
    P = np.zeros((9, 9), dtype=np.uint8)
    for j in range(3):
        for k in range(3):
            P[3*k+j, 3*j+k] = 1
    return P


def grouped_H_from_contraction(M: np.ndarray, P: np.ndarray) -> Tuple[bool,int,dict]:
    Mg = gf2_mat_mul(gf2_mat_mul(P, M), P.T)
    H = Mg[:3,:3].copy()
    off = 0; mismatch = 0
    for bi in range(3):
        for bj in range(3):
            block = Mg[3*bi:3*bi+3, 3*bj:3*bj+3]
            if bi == bj:
                if not np.array_equal(block, H): mismatch += 1
            else:
                off += int(block.sum())
    return off == 0 and mismatch == 0, int_from_mat3(H), {"off_nonzero": off, "diag_mismatch": mismatch, "grouped_rows": row_masks(Mg), "H_rows": row_masks(H)}


def minimal_triples(triples: Iterable[Tuple[int,int,int]]) -> List[Tuple[int,int,int]]:
    ts = sorted(set(triples))
    ans = []
    for t in ts:
        dominated = False
        for u in ts:
            if u == t: continue
            if u[0] <= t[0] and u[1] <= t[1] and u[2] <= t[2] and (u[0] < t[0] or u[1] < t[1] or u[2] < t[2]):
                dominated = True; break
        if not dominated:
            ans.append(t)
    return ans


def upward_covers(budget: Tuple[int,int,int], mins: Sequence[Tuple[int,int,int]]) -> bool:
    return any(t[0] <= budget[0] and t[1] <= budget[1] and t[2] <= budget[2] for t in mins)


def individual_budgets_minimal(ranks: Tuple[int,int,int], total: int = 19) -> List[Tuple[int,int,int]]:
    r1,r2,r3 = ranks
    passers = []
    for c10 in range(total+1):
        for c01 in range(total+1-c10):
            for c11 in range(total+1-c10-c01):
                if c10+c11 >= r1 and c01+c11 >= r2 and c10+c01 >= r3:
                    passers.append((c10,c01,c11))
    return minimal_triples(passers)


def all_budgets(total: int = 19) -> Iterable[Tuple[int,int,int]]:
    for c10 in range(total+1):
        for c01 in range(total+1-c10):
            for c11 in range(total+1-c10-c01):
                yield (c10,c01,c11)


def main() -> None:
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)

    # 3x3 rank table and addition table.
    rank3 = [0]*512
    for x in range(512):
        rank3[x] = int(mat_rank_f2(mat3_from_int(x)))

    # Build q -> 3x3 block H for every E11-core contraction.
    T = build_matmul_tensor_f2()[1:,:,:].astype(np.uint8) % 2
    P = perm_current_to_grouped()
    qH = {}
    qrank = {}
    group_failures = []
    for q in range(1,256):
        M = contraction_matrix(T, q)
        ok, h, info = grouped_H_from_contraction(M, P)
        if not ok:
            group_failures.append({"q": q, "info": info})
        qH[q] = h
        qrank[q] = 3 * rank3[h]
        actual = int(mat_rank_f2(M))
        if qrank[q] != actual:
            group_failures.append({"q": q, "expected_rank_from_H": qrank[q], "actual_rank": actual})

    # Cache exact block-diagonal three-block minimal rank triples for ordered (H1,H2).
    env_cache = {}
    def env_minima(h1: int, h2: int) -> List[Tuple[int,int,int]]:
        key = (h1,h2)
        if key in env_cache:
            return env_cache[key]
        single = set()
        for z in range(512):
            single.add((rank3[h1 ^ z], rank3[h2 ^ z], rank3[z]))
        sums = {(0,0,0)}
        for _ in range(3):
            ns = set()
            for a in sums:
                for b in single:
                    s = (a[0]+b[0], a[1]+b[1], a[2]+b[2])
                    # No length-19 budget can dominate a coordinate >19, but ranks <=9 anyway.
                    ns.add(s)
            sums = ns
        mins = minimal_triples(sums)
        env_cache[key] = mins
        return mins

    lines = enumerate_dual_lines(8)
    rank_type_summary = defaultdict(lambda: {"line_count":0, "env_equals_individual_count":0, "env_type_counts":Counter(), "examples":[]})
    failures = []
    for line in lines:
        q1,q2,q3 = line
        ranks = (qrank[q1], qrank[q2], qrank[q3])
        env = env_minima(qH[q1], qH[q2])
        indiv = individual_budgets_minimal(ranks, 19)
        missing = []
        # For true comparison, scan all length-relevant budgets.
        for b in all_budgets(19):
            ib = (b[0]+b[2] >= ranks[0] and b[1]+b[2] >= ranks[1] and b[0]+b[1] >= ranks[2])
            fea = upward_covers(b, env)
            if ib and not fea:
                missing.append(b)
        rec = rank_type_summary[ranks]
        rec["line_count"] += 1
        if not missing:
            rec["env_equals_individual_count"] += 1
        rec["env_type_counts"][tuple(env)] += 1
        if len(rec["examples"]) < 3:
            rec["examples"].append({"line": list(line), "H1": qH[q1], "H2": qH[q2], "env_minimal": [list(x) for x in env], "individual_minimal": [list(x) for x in indiv], "missing_count": len(missing)})
        if missing:
            failures.append({"line": list(line), "ranks": list(ranks), "H1": qH[q1], "H2": qH[q2], "env_minimal": [list(x) for x in env], "individual_minimal": [list(x) for x in indiv], "missing_count": len(missing), "missing_head": [list(x) for x in missing[:20]]})

    rts = {}
    for ranks, rec in sorted(rank_type_summary.items()):
        env_types = []
        for env_tuple, cnt in rec["env_type_counts"].most_common():
            env_types.append({"count": cnt, "minimal": [list(x) for x in env_tuple]})
        rts[str(ranks)] = {
            "line_count": rec["line_count"],
            "env_covers_all_individual_budget_count": rec["env_equals_individual_count"],
            "env_minimal_type_count": len(env_types),
            "env_minimal_types_head": env_types[:10],
            "examples": rec["examples"],
        }

    out = {
        "schema": "pencil_boundary_fast_v1",
        "elapsed_sec": time.time()-t0,
        "dual_line_count": len(lines),
        "grouping_failures": group_failures,
        "unique_ordered_H_pair_count": len(env_cache),
        "line_count_where_blockdiag_envelope_covers_every_individual_budget": len(lines) - len(failures),
        "line_failure_count": len(failures),
        "failure_head": failures[:30],
        "rank_type_summary": rts,
        "conclusion": {
            "for_length19_support_budgets": "explicit block-diagonal pencil envelope covers all budgets allowed by individual contraction rank bounds" if not failures else "some budgets allowed by individual bounds are not covered by the explicit block-diagonal envelope",
            "interpretation": "Where coverage holds, dual-line pencil realizability gives no support-level color-count cut beyond individual contraction bounds, because an explicit structured Z exists. This is not a full decomposition witness for the original tensor support."
        }
    }
    path = OUTDIR / "pencil_boundary_fast.json"
    path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(path),
        "dual_lines": len(lines),
        "grouping_failures": len(group_failures),
        "unique_ordered_H_pair_count": len(env_cache),
        "covered_lines": len(lines) - len(failures),
        "failure_lines": len(failures),
        "elapsed_sec": time.time()-t0,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
