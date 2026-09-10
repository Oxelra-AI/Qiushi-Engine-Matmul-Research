#!/usr/bin/env python3
"""Tight rank-weight geometry pilot for the E11 core over F2.

This script does not try to settle rank 19.  It tests the mathematical leverage
suggested by the corrected bridge: for a fixed 19-column A support of the E11
core, each contraction q gives

    sum_{t: <q,a_t>=1} b_t c_t^T = T_core(q)

and therefore |I_q| >= rank(T_core(q)).  When equality holds, all participating
B factors must lie in col(T_core(q)) and all C factors in row(T_core(q)).
Intersecting such domains across tight contractions gives a fixed-A domain
filter; a valid rank-one completion must survive zero-domain, linear membership,
and independent-transversal tests.

Outputs are research evidence about whether this tight geometry adds leverage
beyond support counts.  They are not proof certificates for a global theorem.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import random
import sys
import time
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

# ---------------- F2 utilities ----------------

def poppar(x: int) -> int:
    return x.bit_count() & 1


def gf2_rank_rows(rows: Iterable[int], nbits: int) -> int:
    basis = [0] * nbits
    r = 0
    for x in rows:
        v = int(x)
        while v:
            p = v.bit_length() - 1
            if basis[p]:
                v ^= basis[p]
            else:
                basis[p] = v
                r += 1
                break
    return r


def gf2_basis_rows(rows: Iterable[int], nbits: int) -> List[int]:
    basis = [0] * nbits
    for x in rows:
        v = int(x)
        while v:
            p = v.bit_length() - 1
            if basis[p]:
                v ^= basis[p]
            else:
                basis[p] = v
                break
    return [b for b in basis if b]


def span_set(basis: Sequence[int]) -> set[int]:
    vals = {0}
    for b in basis:
        vals |= {v ^ int(b) for v in list(vals)}
    return vals


def full_basis(n: int) -> List[int]:
    return [1 << i for i in range(n)]


def intersection_basis(spaces: Sequence[Sequence[int]], n: int) -> List[int]:
    if not spaces:
        return full_basis(n)
    cur = span_set(spaces[0])
    for B in spaces[1:]:
        cur &= span_set(B)
        if cur == {0}:
            return []
    return gf2_basis_rows(cur, n)


def in_span(v: int, basis: Sequence[int], n: int) -> bool:
    return gf2_rank_rows(list(basis) + [int(v)], n) == gf2_rank_rows(basis, n)


def mat_rank_from_rows(rows: Sequence[int], ncols: int) -> int:
    return gf2_rank_rows(rows, ncols)


def matmul_rank3_from_mask(mask8: int) -> int:
    """Rank of the 3x3 Lambda with Lambda_00=0 and remaining entries from mask8."""
    rows = [0, 0, 0]
    for orig in range(1, 9):
        if (mask8 >> (orig - 1)) & 1:
            i, k = divmod(orig, 3)
            rows[i] |= 1 << k
    return gf2_rank_rows(rows, 3)


def lambda_rows(mask8: int) -> List[int]:
    rows = [0, 0, 0]
    for orig in range(1, 9):
        if (mask8 >> (orig - 1)) & 1:
            i, k = divmod(orig, 3)
            rows[i] |= 1 << k
    return rows


def build_core_tensor() -> List[List[int]]:
    """Return core slices as lists of 9 row masks (9 bits each)."""
    slices: List[List[int]] = []
    for orig in range(1, 9):
        i, k = divmod(orig, 3)  # A = e_{i,k}; block rows B-block k, cols C-block i
        rows = [0] * 9
        for j in range(3):
            b = 3 * k + j
            c = 3 * i + j
            rows[b] |= 1 << c
        slices.append(rows)
    return slices


def contraction_rows(core_slices: Sequence[Sequence[int]], q: int) -> List[int]:
    rows = [0] * 9
    for s in range(8):
        if (q >> s) & 1:
            for r in range(9):
                rows[r] ^= int(core_slices[s][r])
    return rows


def col_space_basis_from_rows(rows: Sequence[int]) -> List[int]:
    cols = []
    for c in range(9):
        v = 0
        for r in range(9):
            if (int(rows[r]) >> c) & 1:
                v |= 1 << r
        if v:
            cols.append(v)
    return gf2_basis_rows(cols, 9)


def row_space_basis_from_rows(rows: Sequence[int]) -> List[int]:
    return gf2_basis_rows([int(r) for r in rows if int(r)], 9)


def mask_to_bits(mask: int, n: int) -> List[int]:
    return [(int(mask) >> i) & 1 for i in range(n)]


def mask_to_hex_list(xs: Sequence[int]) -> List[str]:
    return [hex(int(x)) for x in xs]

# ---------------- QMM parsing / positive control ----------------

def parse_qmm(path: Path) -> List[dict]:
    terms: List[dict] = []
    cur: Dict[str, object] = {}
    with path.open() as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if line.startswith("term"):
                if cur:
                    terms.append(cur)
                cur = {"index": int(line.split()[1])}
            elif line.startswith("u "):
                cur["u"] = [abs(int(x)) & 1 for x in line.split()[1:]]
            elif line.startswith("v "):
                cur["v"] = [abs(int(x)) & 1 for x in line.split()[1:]]
            elif line.startswith("w "):
                cur["w"] = [abs(int(x)) & 1 for x in line.split()[1:]]
    if cur:
        terms.append(cur)
    return terms


def vec_to_mask(v: Sequence[int]) -> int:
    m = 0
    for i, bit in enumerate(v):
        if int(bit) & 1:
            m |= 1 << i
    return m


def cn122_core_terms(qmm: Path) -> Tuple[List[int], List[dict]]:
    outA: List[int] = []
    out_terms: List[dict] = []
    for t in parse_qmm(qmm):
        u = t["u"]
        assert isinstance(u, list)
        proj = vec_to_mask(u[1:])
        if proj:
            outA.append(proj)
            out_terms.append(t)
    return outA, out_terms

# ---------------- fixed-A tight domain analysis ----------------

def target_bitset(core_slices: Sequence[Sequence[int]]) -> int:
    bits = 0
    idx = 0
    for a in range(8):
        for r in range(9):
            row = int(core_slices[a][r])
            for c in range(9):
                if (row >> c) & 1:
                    bits |= 1 << idx
                idx += 1
    return bits


def contribution_bitset(a_mask: int, b_mask: int, c_mask: int) -> int:
    bits = 0
    for alpha in range(8):
        if (int(a_mask) >> alpha) & 1:
            for r in range(9):
                if (int(b_mask) >> r) & 1:
                    base = (alpha * 9 + r) * 9
                    cm = int(c_mask)
                    while cm:
                        lsb = cm & -cm
                        c = lsb.bit_length() - 1
                        bits |= 1 << (base + c)
                        cm ^= lsb
    return bits


def linear_membership(core_slices: Sequence[Sequence[int]], A_cols: Sequence[int],
                      B_domains: Sequence[Sequence[int]], C_domains: Sequence[Sequence[int]]) -> dict:
    cols: List[int] = []
    nvars_by_term = []
    for a, Bb, Cb in zip(A_cols, B_domains, C_domains):
        cnt = 0
        for b in Bb:
            for c in Cb:
                cols.append(contribution_bitset(int(a), int(b), int(c)))
                cnt += 1
        nvars_by_term.append(cnt)
    tgt = target_bitset(core_slices)
    r0 = gf2_rank_rows(cols, 648)
    r1 = gf2_rank_rows(cols + [tgt], 648)
    return {
        "necessary_linear_test_passed": r0 == r1,
        "coefficient_rank": r0,
        "rank_with_rhs": r1,
        "variables": len(cols),
        "equations": 648,
        "affine_solution_dimension_if_consistent": (len(cols) - r0) if r0 == r1 else None,
        "rhs_weight": tgt.bit_count(),
        "variables_by_term_hist": dict(sorted(Counter(nvars_by_term).items())),
    }


def sum_space_dim(domain_list: Sequence[Sequence[int]], n: int) -> int:
    rows: List[int] = []
    for B in domain_list:
        rows.extend(int(x) for x in B)
    return gf2_rank_rows(rows, n)


def transversal_failures(tight_records: Sequence[dict], B_domains: Sequence[Sequence[int]],
                         C_domains: Sequence[Sequence[int]], max_report: int = 30) -> dict:
    failures: List[dict] = []
    per_q_first: List[dict] = []
    for rec in tight_records:
        I = [int(x) for x in rec["terms"]]
        m = len(I)
        if m <= 1:
            continue
        for side, domains in (("B", B_domains), ("C", C_domains)):
            first = None
            # r can be 3, 6, 9; exhaustive subsets are cheap.
            for size in range(1, m + 1):
                for J_tuple in combinations(I, size):
                    dim = sum_space_dim([domains[j] for j in J_tuple], 9)
                    if dim < size:
                        first = {
                            "q": int(rec["q"]),
                            "q_hex": hex(int(rec["q"])),
                            "rank": int(rec["rank"]),
                            "active_count": int(rec["active_count"]),
                            "side": side,
                            "subset_terms": list(J_tuple),
                            "subset_size": size,
                            "sum_domain_dim": dim,
                            "term_domain_dims": [len(domains[j]) for j in J_tuple],
                            "participating_terms": I,
                        }
                        break
                if first is not None:
                    break
            if first is not None:
                if len(failures) < max_report:
                    failures.append(first)
                per_q_first.append(first)
    return {
        "failure_count_reported": len(failures),
        "saturated_contractions_with_failure_reported": len({f["q"] for f in failures}),
        "failures_head": failures,
        "per_q_first_head": per_q_first[:max_report],
    }


def analyze_A_support(label: str, A_cols: Sequence[int], core_slices: Sequence[Sequence[int]],
                      actual_terms: Optional[Sequence[dict]] = None, max_tight_records: int = 20) -> dict:
    t0 = time.time()
    A_cols = [int(a) for a in A_cols]
    sat_B: List[List[List[int]]] = [[] for _ in A_cols]
    sat_C: List[List[List[int]]] = [[] for _ in A_cols]
    undersat: List[dict] = []
    tight_records: List[dict] = []
    hist_rank = Counter()
    hist_count_minus_rank = Counter()
    hist_count_by_rank = Counter()
    domain_source_count_by_term = [0] * len(A_cols)

    for q in range(1, 256):
        rows = contraction_rows(core_slices, q)
        rk = mat_rank_from_rows(rows, 9)
        I = [i for i, a in enumerate(A_cols) if poppar(q & a)]
        cnt = len(I)
        hist_rank[rk] += 1
        hist_count_minus_rank[cnt - rk] += 1
        hist_count_by_rank[(rk, cnt)] += 1
        if cnt < rk:
            undersat.append({"q": q, "q_hex": hex(q), "rank": rk, "active_count": cnt, "defect": rk - cnt, "terms": I})
        elif cnt == rk and cnt > 0:
            Bb = col_space_basis_from_rows(rows)
            Cb = row_space_basis_from_rows(rows)
            rec = {
                "q": q,
                "q_hex": hex(q),
                "lambda_rows": lambda_rows(q),
                "rank": rk,
                "lambda_rank": rk // 3,
                "active_count": cnt,
                "terms": I,
                "B_space_dim": len(Bb),
                "C_space_dim": len(Cb),
                "B_space_basis": Bb,
                "C_space_basis": Cb,
            }
            tight_records.append(rec)
            for i in I:
                sat_B[i].append(Bb)
                sat_C[i].append(Cb)
                domain_source_count_by_term[i] += 1

    B_domains = [intersection_basis(spaces, 9) for spaces in sat_B]
    C_domains = [intersection_basis(spaces, 9) for spaces in sat_C]
    zero_terms = [i for i, (Bb, Cb) in enumerate(zip(B_domains, C_domains)) if len(Bb) == 0 or len(Cb) == 0]
    lin = linear_membership(core_slices, A_cols, B_domains, C_domains)
    trans = transversal_failures(tight_records, B_domains, C_domains)

    actual_membership = None
    if actual_terms is not None:
        bad = []
        for i, t in enumerate(actual_terms):
            b = vec_to_mask(t["v"])
            c = vec_to_mask(t["w"])
            b_ok = in_span(b, B_domains[i], 9)
            c_ok = in_span(c, C_domains[i], 9)
            if not (b_ok and c_ok):
                bad.append({"term": i, "original_index": int(t.get("index", i)), "a": A_cols[i],
                            "b": b, "c": c, "B_dim": len(B_domains[i]), "C_dim": len(C_domains[i]),
                            "b_ok": b_ok, "c_ok": c_ok})
        actual_membership = {"checked_terms": len(actual_terms), "all_b_c_in_domains": not bad, "bad_terms": bad[:20]}

    term_summaries = []
    for i, a in enumerate(A_cols):
        term_summaries.append({
            "term": i,
            "a": a,
            "a_hex": hex(a),
            "a_weight": int(a).bit_count(),
            "tight_contractions_containing_term": domain_source_count_by_term[i],
            "B_dim": len(B_domains[i]),
            "C_dim": len(C_domains[i]),
            "linear_X_dim": len(B_domains[i]) * len(C_domains[i]),
            "B_basis": B_domains[i],
            "C_basis": C_domains[i],
        })

    return {
        "label": label,
        "term_count": len(A_cols),
        "distinct_A_points": len(set(A_cols)),
        "A_cols": A_cols,
        "A_multiplicity_hist": dict(sorted(Counter(Counter(A_cols).values()).items())),
        "A_weight_hist": dict(sorted(Counter(a.bit_count() for a in A_cols).items())),
        "rank_weight": {
            "undersaturated_count": len(undersat),
            "undersaturated_head": undersat[:max_tight_records],
            "tight_count": len(tight_records),
            "tight_by_matrix_rank": dict(sorted(Counter(r["lambda_rank"] for r in tight_records).items())),
            "q_rank_hist": dict(sorted(hist_rank.items())),
            "active_count_minus_rank_hist": {str(k): v for k, v in sorted(hist_count_minus_rank.items())},
            "active_count_by_rank_head": {str(k): v for k, v in sorted(hist_count_by_rank.items())[:40]},
            "tight_records_head": tight_records[:max_tight_records],
        },
        "domain_summary": {
            "term_domain_dims_hist": {f"B{k[0]}_C{k[1]}": v for k, v in sorted(Counter((len(B_domains[i]), len(C_domains[i])) for i in range(len(A_cols))).items())},
            "zero_domain_terms": [term_summaries[i] for i in zero_terms],
            "tight_sources_by_term_hist": dict(sorted(Counter(domain_source_count_by_term).items())),
            "term_summaries": term_summaries,
        },
        "linear_membership": lin,
        "transversal_test": trans,
        "actual_membership": actual_membership,
        "elapsed_sec": round(time.time() - t0, 4),
    }

# ---------------- rank-weight support sampler ----------------

def rank_by_q() -> Dict[int, int]:
    return {q: 3 * matmul_rank3_from_mask(q) for q in range(1, 256)}


def solve_rankweight_supports(num: int, time_limit: float, seed: int, require_distinct: bool = True) -> List[List[int]]:
    try:
        from ortools.sat.python import cp_model
    except Exception as e:  # pragma: no cover
        print(f"OR-Tools unavailable: {e}", file=sys.stderr)
        return []

    ranks = rank_by_q()
    rng = random.Random(seed)
    supports: List[List[int]] = []
    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in range(1, 256)}
    model.Add(sum(x.values()) == 19)
    for q, rk in ranks.items():
        model.Add(sum(x[p] for p in range(1, 256) if poppar(p & q)) >= rk)

    # Mild normalization to avoid supports completely wandering under permutation: include one small point.
    # This is not a mathematical assumption for the output; it only makes the pilot reproducible.
    # We do not force a particular point by default because construction search should remain broad.

    for k in range(num):
        # Re-solve after excluding earlier supports.  Different random seeds alter
        # CP-SAT search order; the pilot needs variety, not an exhaustive sample.
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = max(0.1, time_limit / max(1, num))
        solver.parameters.num_search_workers = 8
        solver.parameters.random_seed = seed + 7919 * k
        status = solver.Solve(model)
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            break
        sol = [p for p in range(1, 256) if solver.Value(x[p])]
        supports.append(sol)
        # Exclude this exact support.
        model.Add(sum(x[p] for p in sol) <= 18)
    return supports

# ---------------- main ----------------

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--outdir", type=Path, default=Path("data/tight_rank_geometry"))
    ap.add_argument("--qmm", type=Path, default=Path("data/cn122_3x3_r23_repro/scheme.qmm"))
    ap.add_argument("--samples", type=int, default=20)
    ap.add_argument("--sample-time", type=float, default=30.0)
    ap.add_argument("--seed", type=int, default=90801)
    args = ap.parse_args()

    args.outdir.mkdir(parents=True, exist_ok=True)
    core_slices = build_core_tensor()

    q_rank_hist = Counter(matmul_rank3_from_mask(q) for q in range(1, 256))
    print("Lambda rank distribution in L={lambda_00=0}:", dict(sorted(q_rank_hist.items())))

    records: List[dict] = []

    if args.qmm.exists():
        A, terms = cn122_core_terms(args.qmm)
        rec = analyze_A_support("cn122_rank23_restricted_core_21term_positive_control", A, core_slices, terms)
        records.append(rec)
        print("positive_control", json.dumps({
            "terms": rec["term_count"],
            "distinct": rec["distinct_A_points"],
            "undersat": rec["rank_weight"]["undersaturated_count"],
            "tight": rec["rank_weight"]["tight_count"],
            "domain_hist": rec["domain_summary"]["term_domain_dims_hist"],
            "linear": rec["linear_membership"]["necessary_linear_test_passed"],
            "actual_domains": None if rec["actual_membership"] is None else rec["actual_membership"]["all_b_c_in_domains"],
            "trans_fail": rec["transversal_test"]["failure_count_reported"],
        }, sort_keys=True))

    # Old near-miss support from earlier research analysis; useful because it nearly satisfies complete Wang rows.
    near = [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219]
    rec = analyze_A_support("S0904_L15_near_complete_Wang_support", near, core_slices, None)
    records.append(rec)
    print("near_L15", json.dumps({
        "undersat": rec["rank_weight"]["undersaturated_count"],
        "tight": rec["rank_weight"]["tight_count"],
        "tight_by_rank": rec["rank_weight"]["tight_by_matrix_rank"],
        "domain_hist": rec["domain_summary"]["term_domain_dims_hist"],
        "zero_terms": len(rec["domain_summary"]["zero_domain_terms"]),
        "linear": rec["linear_membership"]["necessary_linear_test_passed"],
        "affine_dim": rec["linear_membership"]["affine_solution_dimension_if_consistent"],
        "trans_fail": rec["transversal_test"]["failure_count_reported"],
    }, sort_keys=True))

    sample_supports = solve_rankweight_supports(args.samples, args.sample_time, args.seed)
    sample_summaries = []
    for i, sup in enumerate(sample_supports):
        rec = analyze_A_support(f"rank_weight_only_sample_{i}", sup, core_slices, None, max_tight_records=8)
        records.append(rec)
        sample_summaries.append({
            "i": i,
            "support": sup,
            "A_weight_hist": rec["A_weight_hist"],
            "tight": rec["rank_weight"]["tight_count"],
            "tight_by_rank": rec["rank_weight"]["tight_by_matrix_rank"],
            "zero_terms": len(rec["domain_summary"]["zero_domain_terms"]),
            "domain_hist": rec["domain_summary"]["term_domain_dims_hist"],
            "linear": rec["linear_membership"]["necessary_linear_test_passed"],
            "affine_dim": rec["linear_membership"]["affine_solution_dimension_if_consistent"],
            "trans_fail": rec["transversal_test"]["failure_count_reported"],
        })
        print("sample", i, json.dumps(sample_summaries[-1], sort_keys=True)[:1000])

    aggregate = {
        "sample_count": len(sample_summaries),
        "rank_weight_only_pass_linear_count": sum(1 for s in sample_summaries if s["linear"]),
        "rank_weight_only_zero_domain_count": sum(1 for s in sample_summaries if s["zero_terms"] > 0),
        "rank_weight_only_transversal_reported_count": sum(1 for s in sample_summaries if s["trans_fail"] > 0),
        "sample_tight_hist": dict(sorted(Counter(s["tight"] for s in sample_summaries).items())),
        "sample_domain_hist_hist": dict(sorted(Counter(str(s["domain_hist"]) for s in sample_summaries).items())),
    }

    payload = {
        "schema": "tight_rank_geometry_pilot_v1",
        "field": "F2",
        "core": "E11 quotient core T[1:,:,:]",
        "purpose": "Compare rank-weight support counts with factor-geometry constraints from tight contractions for rank-19 E11-core search.",
        "lambda_rank_distribution_in_L": {str(k): int(v) for k, v in sorted(q_rank_hist.items())},
        "records": records,
        "sample_summaries": sample_summaries,
        "aggregate": aggregate,
        "interpretation_limits": [
            "Rank-weight supports and fixed-A domain passes are necessary conditions only, not decompositions.",
            "The L15 near-complete support still violates complete Wang rows in the old record and cannot be treated as an admissible core support.",
            "The positive control is a 21-term core induced by the verified rank-23 scheme, not a rank-19 construction.",
        ],
    }
    out = args.outdir / "tight_rank_geometry_pilot.json"
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    brief = {
        "out": str(out),
        "lambda_rank_distribution_in_L": payload["lambda_rank_distribution_in_L"],
        "aggregate": aggregate,
    }
    print(json.dumps(brief, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
