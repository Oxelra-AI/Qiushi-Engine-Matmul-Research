#!/usr/bin/env python3
r"""analysis: generalized low-excess contraction filter for E11-core A-lists.

This script turns the analysis slice excess theorem into a coordinate-free
support-level test over all rank-one and rank-two A-dual contractions lambda,
not only the eight coordinate slices.

For a contraction lambda with rank d = rank(Lambda), the E11 core contraction is
    M_lambda = Lambda^T \otimes I_3,
so rank(M_lambda)=r=3d.  If m selected terms are active under lambda, exact
factorization B_I C_I^T = M_lambda gives Sylvester's inequality
    e_B(lambda) + e_C(lambda) <= m-r,
where e_B and e_C are excess dimensions above the prescribed column and row
spaces U_lambda=col(M_lambda), V_lambda=row(M_lambda).

Consequences used here:
  * m < r rejects the A-list (ordinary contraction rank lower bound).
  * m = r forces both B- and C-purity relative to U_lambda,V_lambda.
  * m = r+1 forces one-sided purity.
  * if a tight contraction lambda shares h terms with another contraction mu,
    then those h B-vectors (and C-vectors) are independent inside U_lambda
    (resp. V_lambda).  Therefore their projections modulo U_mu (resp. V_mu)
    have dimension at least max(0, h - dim(U_lambda cap U_mu)).  These lower
    bounds can exceed mu's excess budget or force one side of mu to be pure.
  * two pure contractions that share any nonzero term on a side whose prescribed
    spaces intersect trivially are incompatible.

The result is still only a necessary condition for B/C completion.  Passing it
never implies existence of a rank-19 core.  Rejection is theorem-grade for the
fixed A-list under the nonzero rank-one term semantics, because it is derived
from exact contraction identities.
"""
from __future__ import annotations

import argparse
import collections
import json
import sys
import time
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np

ROOT = Path("research/research_record")
POOL_PATH = Path("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy")
OUT = ROOT / "workspace/data/general_low_excess/general_low_excess_filter.json"

# Optional peer/local helpers for calibration comparisons only.
PEER_SCRIPTS = Path("scripts")
if str(PEER_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(PEER_SCRIPTS))
try:
    import e11_shadow_filter as peer_shadow  # type: ignore
    import e11_purity_2sat_filter as peer_purity  # type: ignore
except Exception:  # pragma: no cover - comparison helpers absent
    peer_shadow = None
    peer_purity = None

NS = 8
N9 = 9
FULL9 = (1 << 9) - 1


def poppar(x: int) -> int:
    return int(x).bit_count() & 1


def full_mask_from_quotient(q: int) -> int:
    """Insert the missing E11/full-bit 0 into an 8-bit quotient mask."""
    q = int(q)
    full = 0
    k = 0
    for bit in range(9):
        if bit == 0:
            continue
        if (q >> k) & 1:
            full |= 1 << bit
        k += 1
    return full


def mat3_from_full_mask(mask: int) -> np.ndarray:
    return np.array([[(int(mask) >> (3 * i + j)) & 1 for j in range(3)] for i in range(3)], dtype=np.uint8)


def lambda_matrix(lam8: int) -> np.ndarray:
    return mat3_from_full_mask(full_mask_from_quotient(lam8))


def gf2_rank_matrix(M: np.ndarray) -> int:
    A = np.array(M, dtype=np.uint8, copy=True) & 1
    if A.ndim == 1:
        return int(A.any())
    m, n = A.shape
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i, c]:
                piv = i
                break
        if piv is None:
            continue
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        for i in range(m):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        r += 1
        if r == m:
            break
    return int(r)


def row_mask(row: Sequence[int]) -> int:
    x = 0
    for i, b in enumerate(row):
        if int(b) & 1:
            x |= 1 << i
    return x


def rref_basis_int(rows: Iterable[int], n: int = N9) -> Tuple[int, ...]:
    basis = [0] * n
    for row0 in rows:
        v = int(row0) & ((1 << n) - 1)
        while v:
            p = v.bit_length() - 1
            if basis[p]:
                v ^= basis[p]
            else:
                basis[p] = v
                break
    # Make reduced basis.
    for p in range(n):
        if basis[p]:
            for q in range(n):
                if q != p and basis[q] and ((basis[q] >> p) & 1):
                    basis[q] ^= basis[p]
    return tuple(basis[p] for p in range(n - 1, -1, -1) if basis[p])


def rank_basis(rows: Iterable[int], n: int = N9) -> int:
    return len(rref_basis_int(rows, n=n))


def sum_dim(a: Sequence[int], b: Sequence[int], n: int = N9) -> int:
    return rank_basis(list(a) + list(b), n=n)


def intersection_dim(a: Sequence[int], b: Sequence[int], n: int = N9) -> int:
    return len(a) + len(b) - sum_dim(a, b, n=n)


def contraction_matrix(lam8: int) -> np.ndarray:
    L = lambda_matrix(lam8)
    return np.kron(L.T.astype(np.uint8), np.eye(3, dtype=np.uint8)) & 1


def row_space_basis(M: np.ndarray) -> Tuple[int, ...]:
    return rref_basis_int([row_mask(row) for row in M], n=M.shape[1])


def col_space_basis(M: np.ndarray) -> Tuple[int, ...]:
    # Column vectors of M become row masks of M.T.
    return rref_basis_int([row_mask(row) for row in M.T], n=M.shape[0])


@dataclass(frozen=True)
class LambdaSpace:
    lam: int
    rank_lambda: int
    rank_contraction: int
    U: Tuple[int, ...]  # column/B space basis as 9-bit masks
    V: Tuple[int, ...]  # row/C space basis as 9-bit masks


@dataclass
class ContractionRecord:
    lam: int
    rank_lambda: int
    r: int
    active: Tuple[int, ...]
    m: int
    budget: int
    U: Tuple[int, ...]
    V: Tuple[int, ...]
    eB_lb: int = 0
    eC_lb: int = 0
    lb_sources_B: List[dict] = None  # type: ignore
    lb_sources_C: List[dict] = None  # type: ignore
    B_impossible: bool = False
    C_impossible: bool = False
    B_forced: bool = False
    C_forced: bool = False

    def __post_init__(self):
        if self.lb_sources_B is None:
            self.lb_sources_B = []
        if self.lb_sources_C is None:
            self.lb_sources_C = []


LAMBDA_SPACES: Dict[int, LambdaSpace] = {}
for lam in range(1, 256):
    L = lambda_matrix(lam)
    d = gf2_rank_matrix(L)
    M = contraction_matrix(lam)
    rc = gf2_rank_matrix(M)
    assert rc == 3 * d
    LAMBDA_SPACES[lam] = LambdaSpace(
        lam=lam,
        rank_lambda=d,
        rank_contraction=rc,
        U=col_space_basis(M),
        V=row_space_basis(M),
    )

RANK12_LAMBDAS = [lam for lam, sp in LAMBDA_SPACES.items() if sp.rank_lambda in (1, 2)]


def dot8(lam: int, u: int) -> int:
    return poppar(int(lam) & int(u))


def solve_2sat(clauses: List[List[int]], nvars: int) -> Tuple[bool, Optional[List[bool]], dict]:
    """Implication-graph 2-SAT.  Literals are +/- (var_index+1)."""
    adj = [[] for _ in range(2 * nvars)]
    radj = [[] for _ in range(2 * nvars)]

    def idx(lit: int) -> int:
        v = abs(lit) - 1
        return 2 * v + (1 if lit > 0 else 0)

    def neg(i: int) -> int:
        return i ^ 1

    for cl in clauses:
        if len(cl) == 0:
            return False, None, {"empty_clause": True}
        if len(cl) == 1:
            a = b = int(cl[0])
        elif len(cl) == 2:
            a, b = int(cl[0]), int(cl[1])
        else:
            raise ValueError(f"non-2SAT clause {cl}")
        ia, ib = idx(a), idx(b)
        na, nb = neg(ia), neg(ib)
        adj[na].append(ib); radj[ib].append(na)
        adj[nb].append(ia); radj[ia].append(nb)

    sys.setrecursionlimit(max(10000, 4 * nvars + 10))
    seen = [False] * (2 * nvars)
    order: List[int] = []

    def dfs(v: int):
        seen[v] = True
        for w in adj[v]:
            if not seen[w]:
                dfs(w)
        order.append(v)

    for v in range(2 * nvars):
        if not seen[v]:
            dfs(v)

    comp = [-1] * (2 * nvars)

    def rdfs(v: int, c: int):
        comp[v] = c
        for w in radj[v]:
            if comp[w] < 0:
                rdfs(w, c)

    c = 0
    for v in reversed(order):
        if comp[v] < 0:
            rdfs(v, c); c += 1

    for v in range(nvars):
        if comp[2 * v] == comp[2 * v + 1]:
            return False, None, {"conflict_var": v, "components": c}
    assignment = [comp[2 * v] < comp[2 * v + 1] for v in range(nvars)]
    return True, assignment, {"components": c}


def analyze_a_list(us: Sequence[int], name: str = "support", include_pair_conflicts: bool = True) -> dict:
    """Run generalized low-excess necessary tests on a labelled A-list.

    `us` is a term list, not necessarily a set; repeated projected A-directions
    are counted with multiplicity.  This is important for fixed-A completion
    probes, although the rank-20 lower-bound bridge later focuses on the
    distinct projected-direction branch.
    """
    us = [int(u) for u in us]
    records: Dict[int, ContractionRecord] = {}
    scalar_violations = []
    rank_count_hist = collections.Counter()

    for lam in RANK12_LAMBDAS:
        sp = LAMBDA_SPACES[lam]
        active = tuple(i for i, u in enumerate(us) if dot8(lam, u))
        m = len(active)
        r = sp.rank_contraction
        rec = ContractionRecord(lam=lam, rank_lambda=sp.rank_lambda, r=r,
                                active=active, m=m, budget=m - r, U=sp.U, V=sp.V)
        records[lam] = rec
        rank_count_hist[(sp.rank_lambda, m)] += 1
        if m < r:
            scalar_violations.append({"lambda": lam, "rank_lambda": sp.rank_lambda, "active_count": m, "rank_contraction": r, "deficit": r - m})

    tight_lams = [lam for lam, rec in records.items() if rec.m == rec.r]

    # Tight-contraction leakage lower bounds into every other rank-1/2 contraction.
    leakage_budget_violations = []
    for mu, rec_mu in records.items():
        if rec_mu.m < rec_mu.r:
            continue
        for lam in tight_lams:
            if lam == mu:
                continue
            rec_lam = records[lam]
            shared = sorted(set(rec_lam.active).intersection(rec_mu.active))
            h = len(shared)
            if h == 0:
                continue
            dU = intersection_dim(rec_lam.U, rec_mu.U)
            dV = intersection_dim(rec_lam.V, rec_mu.V)
            lbB = max(0, h - dU)
            lbC = max(0, h - dV)
            if lbB > rec_mu.eB_lb:
                rec_mu.eB_lb = lbB
                rec_mu.lb_sources_B = [{"tight_lambda": lam, "shared_terms": shared, "h": h, "intersection_dim": dU, "lb": lbB}]
            elif lbB and lbB == rec_mu.eB_lb:
                rec_mu.lb_sources_B.append({"tight_lambda": lam, "shared_terms": shared, "h": h, "intersection_dim": dU, "lb": lbB})
            if lbC > rec_mu.eC_lb:
                rec_mu.eC_lb = lbC
                rec_mu.lb_sources_C = [{"tight_lambda": lam, "shared_terms": shared, "h": h, "intersection_dim": dV, "lb": lbC}]
            elif lbC and lbC == rec_mu.eC_lb:
                rec_mu.lb_sources_C.append({"tight_lambda": lam, "shared_terms": shared, "h": h, "intersection_dim": dV, "lb": lbC})

        if rec_mu.eB_lb + rec_mu.eC_lb > rec_mu.budget:
            leakage_budget_violations.append({
                "lambda": mu,
                "rank_lambda": rec_mu.rank_lambda,
                "active_count": rec_mu.m,
                "rank_contraction": rec_mu.r,
                "budget": rec_mu.budget,
                "eB_lb": rec_mu.eB_lb,
                "eC_lb": rec_mu.eC_lb,
                "B_sources_head": rec_mu.lb_sources_B[:4],
                "C_sources_head": rec_mu.lb_sources_C[:4],
            })
        if rec_mu.eB_lb > 0:
            rec_mu.B_impossible = True
        if rec_mu.eC_lb > 0:
            rec_mu.C_impossible = True
        if rec_mu.budget >= 0 and rec_mu.eB_lb == rec_mu.budget and rec_mu.budget > 0:
            rec_mu.C_forced = True
        if rec_mu.budget >= 0 and rec_mu.eC_lb == rec_mu.budget and rec_mu.budget > 0:
            rec_mu.B_forced = True

    # Variables for side-purity decisions on contractions where purity is forced,
    # required, or can be used in conflicts.  Rank-3 contractions have full 9D
    # spaces and are omitted because their side-purity is vacuous.
    var_index: Dict[Tuple[int, str], int] = {}

    def var(lam: int, side: str) -> int:
        key = (lam, side)
        if key not in var_index:
            var_index[key] = len(var_index)
        return var_index[key]

    clauses: List[List[int]] = []
    reasons: List[dict] = []
    pure_relevant = []
    for lam, rec in records.items():
        if rec.m < rec.r:
            continue
        relevant = False
        if rec.m == rec.r:
            # Tight: both sides pure.
            b = var(lam, "B"); c = var(lam, "C")
            clauses.append([b + 1]); reasons.append({"type": "tight_forces_B", "lambda": lam, "lit": b + 1})
            clauses.append([c + 1]); reasons.append({"type": "tight_forces_C", "lambda": lam, "lit": c + 1})
            relevant = True
        elif rec.m == rec.r + 1:
            b = var(lam, "B"); c = var(lam, "C")
            clauses.append([b + 1, c + 1]); reasons.append({"type": "one_excess_needs_one_side_pure", "lambda": lam, "clause": [b + 1, c + 1]})
            relevant = True
        if rec.B_impossible or rec.B_forced:
            b = var(lam, "B"); relevant = True
            if rec.B_impossible:
                clauses.append([-(b + 1)]); reasons.append({"type": "B_pure_impossible_from_tight_leakage", "lambda": lam, "lit": -(b + 1), "eB_lb": rec.eB_lb})
            if rec.B_forced:
                clauses.append([b + 1]); reasons.append({"type": "B_pure_forced_by_C_budget_saturation", "lambda": lam, "lit": b + 1, "eC_lb": rec.eC_lb, "budget": rec.budget})
        if rec.C_impossible or rec.C_forced:
            c = var(lam, "C"); relevant = True
            if rec.C_impossible:
                clauses.append([-(c + 1)]); reasons.append({"type": "C_pure_impossible_from_tight_leakage", "lambda": lam, "lit": -(c + 1), "eC_lb": rec.eC_lb})
            if rec.C_forced:
                clauses.append([c + 1]); reasons.append({"type": "C_pure_forced_by_B_budget_saturation", "lambda": lam, "lit": c + 1, "eB_lb": rec.eB_lb, "budget": rec.budget})
        if relevant:
            pure_relevant.append(lam)

    pair_conflict_count = 0
    if include_pair_conflicts:
        for a_i, b_i in combinations(sorted(set(lam for lam, _side in var_index)), 2):
            rec_a, rec_b = records[a_i], records[b_i]
            if not set(rec_a.active).intersection(rec_b.active):
                continue
            if (a_i, "B") in var_index and (b_i, "B") in var_index and intersection_dim(rec_a.U, rec_b.U) == 0:
                va = var_index[(a_i, "B")]; vb = var_index[(b_i, "B")]
                clauses.append([-(va + 1), -(vb + 1)])
                pair_conflict_count += 1
                if len(reasons) < 200:
                    reasons.append({"type": "shared_term_zero_B_intersection", "lambdas": [a_i, b_i], "clause": [-(va + 1), -(vb + 1)]})
            if (a_i, "C") in var_index and (b_i, "C") in var_index and intersection_dim(rec_a.V, rec_b.V) == 0:
                va = var_index[(a_i, "C")]; vb = var_index[(b_i, "C")]
                clauses.append([-(va + 1), -(vb + 1)])
                pair_conflict_count += 1
                if len(reasons) < 200:
                    reasons.append({"type": "shared_term_zero_C_intersection", "lambdas": [a_i, b_i], "clause": [-(va + 1), -(vb + 1)]})

    sat = True
    assignment = None
    solver_info = {}
    if scalar_violations or leakage_budget_violations:
        sat = False
        solver_info = {"hard_reject_before_2sat": True}
    else:
        sat, assignment, solver_info = solve_2sat(clauses, len(var_index)) if var_index else (True, [], {"components": 0})

    inv_var = {v: k for k, v in var_index.items()}
    assignment_named = None
    if assignment is not None:
        assignment_named = {f"{side}_{lam}": bool(assignment[v]) for v, (lam, side) in inv_var.items()}

    low_hist = collections.Counter()
    for rec in records.values():
        if rec.m >= rec.r and rec.m <= rec.r + 2:
            low_hist[(rec.rank_lambda, rec.m - rec.r)] += 1

    # Compact witness records for interpreting what the filter actually used.
    forced_or_blocked_head = []
    for lam, rec in sorted(records.items()):
        if rec.m >= rec.r and (rec.m <= rec.r + 1 or rec.eB_lb or rec.eC_lb or rec.B_forced or rec.C_forced):
            forced_or_blocked_head.append({
                "lambda": lam,
                "rank_lambda": rec.rank_lambda,
                "active_count": rec.m,
                "rank_contraction": rec.r,
                "budget": rec.budget,
                "eB_lb": rec.eB_lb,
                "eC_lb": rec.eC_lb,
                "B_impossible": rec.B_impossible,
                "C_impossible": rec.C_impossible,
                "B_forced": rec.B_forced,
                "C_forced": rec.C_forced,
                "B_sources_head": rec.lb_sources_B[:2],
                "C_sources_head": rec.lb_sources_C[:2],
            })
        if len(forced_or_blocked_head) >= 40:
            break

    return {
        "name": name,
        "term_count": len(us),
        "distinct_A_count": len(set(us)),
        "multiplicity_hist": {str(k): int(v) for k, v in sorted(collections.Counter(collections.Counter(us).values()).items())},
        "total_A_weight": int(sum(int(u).bit_count() for u in us)),
        "rank_count_hist": {f"rank{d}_m{m}": int(v) for (d, m), v in sorted(rank_count_hist.items())},
        "low_excess_hist": {f"rank{d}_budget{k}": int(v) for (d, k), v in sorted(low_hist.items())},
        "tight_count": len(tight_lams),
        "tight_by_rank": {str(k): int(v) for k, v in sorted(collections.Counter(records[lam].rank_lambda for lam in tight_lams).items())},
        "half_pure_count": sum(1 for rec in records.values() if rec.m == rec.r + 1),
        "scalar_violation_count": len(scalar_violations),
        "scalar_violations_head": scalar_violations[:20],
        "leakage_budget_violation_count": len(leakage_budget_violations),
        "leakage_budget_violations_head": leakage_budget_violations[:20],
        "n_purity_variables": len(var_index),
        "n_2sat_clauses": len(clauses),
        "pair_zero_intersection_conflict_clauses": pair_conflict_count,
        "2sat_sat": bool(sat),
        "rejects_support": bool((not sat) or scalar_violations or leakage_budget_violations),
        "solver_info": solver_info,
        "assignment_head": None if assignment_named is None else dict(list(sorted(assignment_named.items()))[:40]),
        "reasons_head": reasons[:80],
        "forced_or_blocked_head": forced_or_blocked_head,
        "interpretation": "Necessary A-list rejection derived from contraction rank/Sylvester excess and exact prescribed B/C spaces. Passing does not imply B/C completion.",
    }


def row_to_terms(row: Sequence[int]) -> List[Tuple[int, int, int]]:
    r = len(row) // 3
    return [(int(row[3 * t]), int(row[3 * t + 1]), int(row[3 * t + 2])) for t in range(r)]


def peer_shadow_summary(us: List[int]) -> Optional[dict]:
    if peer_shadow is None:
        return None
    inv_lams = peer_shadow.invertible_lambda_masks()
    return peer_shadow.analyze_support(us, subset=None, min_subset=False)


def analyze_rank21_pool(max_head: int = 12) -> dict:
    pool = np.load(POOL_PATH)
    hist = collections.Counter()
    reject_head = []
    tight_hist = collections.Counter()
    for idx, row in enumerate(pool):
        us = [u for u, _v, _w in row_to_terms(row)]
        res = analyze_a_list(us, name=f"rank21_pool_{idx}")
        hist[(res["rejects_support"], res["scalar_violation_count"], res["leakage_budget_violation_count"], res["2sat_sat"], res["tight_count"], res["half_pure_count"])] += 1
        tight_hist[(res["tight_count"], res["half_pure_count"])] += 1
        if res["rejects_support"] and len(reject_head) < max_head:
            reject_head.append({"row": idx, "result": res})
    return {
        "pool_path": str(POOL_PATH),
        "rows": int(pool.shape[0]),
        "terms_per_row": int(pool.shape[1] // 3),
        "all_pass": len(reject_head) == 0,
        "hist": {str(k): int(v) for k, v in sorted(hist.items(), key=lambda kv: str(kv[0]))},
        "tight_half_hist_head": {str(k): int(v) for k, v in sorted(tight_hist.items(), key=lambda kv: (-kv[1], kv[0]))[:40]},
        "reject_head": reject_head,
    }


def same_w_deletion_lists() -> List[dict]:
    pool = np.load(POOL_PATH)
    out = []
    seen = set()
    for idx, row in enumerate(pool):
        terms = row_to_terms(row)
        groups: Dict[int, List[int]] = collections.defaultdict(list)
        for t, (_u, _v, w) in enumerate(terms):
            groups[int(w)].append(t)
        for w, inds in groups.items():
            for a, b in combinations(inds, 2):
                rem = [terms[t] for t in range(len(terms)) if t not in (a, b)]
                us = [u for u, _v, _w in rem]
                # Keep multiplicity/order for fixed-A completion, but report unique multiset count too.
                key = tuple(sorted(us))
                if key in seen:
                    continue
                seen.add(key)
                out.append({"pool_row": idx, "deleted_terms": [a, b], "deleted_w": int(w), "u_masks": us})
    return out


def shadow_consistent_quick(us: List[int]) -> Optional[bool]:
    if peer_shadow is None:
        return None
    try:
        return bool(peer_shadow.analyze_support(us)["full_shadow_consistent"])
    except Exception:
        return None


def coordinate_purity_pass(us: List[int]) -> Optional[bool]:
    if peer_purity is None:
        return None
    try:
        return not bool(peer_purity.build_purity_clauses(us, extended=True)["rejects_support"])
    except Exception:
        return None


def analyze_same_w_deletions(max_records: Optional[int] = None) -> dict:
    records = same_w_deletion_lists()
    if max_records is not None:
        records = records[:max_records]
    hist = collections.Counter()
    head = []
    general_reject_after_shadow_coord_pass = 0
    shadow_coord_pass_total = 0
    first_general_rejects = []
    for idx, rec in enumerate(records):
        us = rec["u_masks"]
        sh_ok = shadow_consistent_quick(us)
        coord_pass = coordinate_purity_pass(us)
        gen = analyze_a_list(us, name=f"same_w_{idx}")
        key = (sh_ok, coord_pass, gen["rejects_support"], gen["scalar_violation_count"], gen["leakage_budget_violation_count"], gen["2sat_sat"])
        hist[key] += 1
        if sh_ok is True and coord_pass is True:
            shadow_coord_pass_total += 1
            if gen["rejects_support"]:
                general_reject_after_shadow_coord_pass += 1
                if len(first_general_rejects) < 10:
                    first_general_rejects.append({"source": rec, "general": gen})
        if len(head) < 20:
            head.append({"source": rec, "shadow_ok": sh_ok, "coordinate_purity_pass": coord_pass, "general_reject": gen["rejects_support"], "general_summary": {k: gen[k] for k in ["term_count", "distinct_A_count", "total_A_weight", "tight_count", "half_pure_count", "scalar_violation_count", "leakage_budget_violation_count", "2sat_sat", "n_purity_variables", "n_2sat_clauses"]}})
    return {
        "records_scanned": len(records),
        "hist": {str(k): int(v) for k, v in sorted(hist.items(), key=lambda kv: str(kv[0]))},
        "shadow_and_coordinate_pass_total": shadow_coord_pass_total,
        "general_reject_after_shadow_and_coordinate_pass": general_reject_after_shadow_coord_pass,
        "first_general_rejects_after_shadow_coordinate_head": first_general_rejects,
        "records_head": head,
        "meaning": "Same-W deletions are a local near-miss family from rank-21 cores, not a cover of rank-19 E11 supports. General low-excess rejection is a fixed-A-list obstruction only.",
    }


def parse_support_arg(s: str) -> List[int]:
    if not s:
        return []
    p = Path(s)
    if p.exists():
        data = json.loads(p.read_text())
        if isinstance(data, list):
            return [int(x) for x in data]
        for key in ["u_masks", "support", "A_cols", "A_support"]:
            if key in data:
                return [int(x) for x in data[key]]
        raise ValueError(f"No support key in {s}")
    return [int(x) for x in s.replace(";", ",").replace(" ", ",").split(",") if x.strip()]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--support", default="", help="optional comma-separated A-list or JSON file")
    ap.add_argument("--name", default="manual_support")
    ap.add_argument("--skip-pool", action="store_true")
    ap.add_argument("--skip-same-w", action="store_true")
    ap.add_argument("--same-w-max", type=int, default=None)
    ap.add_argument("--out", type=Path, default=OUT)
    args = ap.parse_args()

    t0 = time.time()
    manual = None
    if args.support:
        us = parse_support_arg(args.support)
        manual = analyze_a_list(us, name=args.name)

    known = {
        "L15_near_support": analyze_a_list([1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219], "L15_near_support"),
        "near_support": analyze_a_list([1,2,3,4,8,20,24,31,32,36,64,73,127,128,141,160,182,192,219], "near_support"),
    }

    pool = None if args.skip_pool else analyze_rank21_pool()
    samew = None if args.skip_same_w else analyze_same_w_deletions(args.same_w_max)

    result = {
        "schema": "s0908_general_low_excess_filter_v1",
        "field": "F2",
        "purpose": "Generalize low-excess support geometry from coordinate slices to all rank-one/rank-two E11 contractions using actual prescribed B/C subspace intersections.",
        "mathematical_basis": {
            "contraction": "M_lambda = Lambda^T tensor I3 for quotient lambda with Lambda_00=0",
            "rank": "rank(M_lambda)=3*rank(Lambda)",
            "excess_bound": "For m active terms and r=rank(M_lambda), e_B+e_C <= m-r relative to col(M_lambda), row(M_lambda).",
            "tight_leakage": "If lambda is tight and shares h terms with mu, then e_B(mu)>=max(0,h-dim(U_lambda cap U_mu)) and similarly for C; this uses independence of the tight active B/C bases.",
            "scope": "Necessary condition for a fixed A-list; it does not prove existence and it is not a complete rank lower bound unless embedded in a complete proof-producing cover.",
        },
        "lambda_rank_distribution": {str(k): int(v) for k, v in sorted(collections.Counter(sp.rank_lambda for sp in LAMBDA_SPACES.values()).items())},
        "manual": manual,
        "known_near_supports": known,
        "rank21_pool": pool,
        "same_w_deletions": samew,
        "elapsed_sec": round(time.time() - t0, 3),
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    brief = {
        "out": str(args.out),
        "manual_reject": None if manual is None else manual["rejects_support"],
        "known_rejects": {k: v["rejects_support"] for k, v in known.items()},
        "rank21_pool_all_pass": None if pool is None else pool["all_pass"],
        "same_w_scanned": None if samew is None else samew["records_scanned"],
        "same_w_shadow_coord_pass_total": None if samew is None else samew["shadow_and_coordinate_pass_total"],
        "same_w_general_reject_after_shadow_coord": None if samew is None else samew["general_reject_after_shadow_and_coordinate_pass"],
        "elapsed_sec": result["elapsed_sec"],
    }
    print(json.dumps(brief, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
