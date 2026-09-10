#!/usr/bin/env python3
r"""analysis: contraction-weight excess formulation for E11 rank-19 support search.

This script implements the exact F2 simplification suggested after analysis.
For a labelled A-list or for distinct support variables x_p, define contraction
weights
    m_lam = #{t : <lam,u_t>=1}.
Then for two contractions lambda, mu over F2,
    h_{lambda,mu} = (m_lambda + m_mu - m_{lambda+mu})/2
is their shared active-term count.  If lambda is tight, m_lambda=r_lambda,
where r_lambda = rank(Lambda^T \otimes I_3), the low-excess leakage bounds for
a rank-one/rank-two target mu can be written using only the m-variables:
    2 e_B(mu) >= r_lambda + m_mu - m_{lambda+mu}
                   - 2 dim(U_lambda cap U_mu),
and analogously for C.  Here U,V are the prescribed column/row spaces of
M_lam=Lambda^T tensor I3.  We also impose
    e_B(mu)+e_C(mu) <= m_mu-r_mu,
with e_B,e_C nonnegative integer excess variables.

The formulation is a coverage-preserving necessary condition at the A-support
level.  A feasible support/excess assignment is not a B/C completion.  UNSAT from
a non-proof-producing solver is experimental evidence, not a theorem certificate.
"""
from __future__ import annotations

import argparse
import collections
import json
import math
import pickle
import sys
import time
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/contraction_weight_excess"
POOL_PATH = Path("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy")
LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
REDUCED_PATH = Path("data/reduced_wang/primitive_reduced_rows.pkl")
CACHE_PATH = OUTDIR / "e11_complete_wang_records.pkl"

S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from core_capacity_from_wang_lut import CoreQuotient, load_lut  # type: ignore  # noqa:E402
from complete_core_and_transversal import build_core_constraints, complete_core_wang_scan  # type: ignore  # noqa:E402

# Optional peer helpers for calibration only.  The core formulation here does not
# depend on them.
PEER = Path("scripts")
if str(PEER) not in sys.path:
    sys.path.insert(0, str(PEER))
try:  # pragma: no cover - optional in some reproductions
    import e11_shadow_filter as peer_shadow  # type: ignore
    import e11_purity_2sat_filter as peer_purity  # type: ignore
except Exception:  # pragma: no cover
    peer_shadow = None
    peer_purity = None

NS = 8
N9 = 9
FULL9 = (1 << 9) - 1
POINTS = list(range(1, 256))


def poppar(x: int) -> int:
    return int(x).bit_count() & 1


def dot8(a: int, b: int) -> int:
    return poppar(int(a) & int(b))


def full_mask_from_quotient(q: int) -> int:
    """Insert the deleted E11/full-coordinate bit 0 into an 8-bit quotient mask."""
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
    # Full bit convention: bit 3*i+j is A_{ij}.
    return np.array([[(int(mask) >> (3 * i + j)) & 1 for j in range(3)] for i in range(3)], dtype=np.uint8)


def lambda_mat(lam8: int) -> np.ndarray:
    return mat3_from_full_mask(full_mask_from_quotient(lam8))


def contraction_mat(lam8: int) -> np.ndarray:
    L = lambda_mat(lam8)
    return np.kron(L.T.astype(np.uint8), np.eye(3, dtype=np.uint8)) & 1


def row_mask(row: Sequence[int]) -> int:
    x = 0
    for i, b in enumerate(row):
        if int(b) & 1:
            x |= 1 << i
    return x


def gf2_rref(rows: Iterable[int], n: int = N9) -> Tuple[int, ...]:
    basis = [0] * n
    for row in rows:
        v = int(row) & ((1 << n) - 1)
        while v:
            p = v.bit_length() - 1
            if basis[p]:
                v ^= basis[p]
            else:
                basis[p] = v
                break
    # Reduced form so equality of subspaces is canonical enough for diagnostics.
    for p in range(n):
        if basis[p]:
            for q in range(n):
                if q != p and basis[q] and ((basis[q] >> p) & 1):
                    basis[q] ^= basis[p]
    return tuple(basis[p] for p in range(n - 1, -1, -1) if basis[p])


def gf2_rank(rows: Iterable[int], n: int = N9) -> int:
    return len(gf2_rref(rows, n=n))


def rank_mat(M: np.ndarray) -> int:
    return gf2_rank([row_mask(row) for row in M], n=M.shape[1])


def row_space(M: np.ndarray) -> Tuple[int, ...]:
    return gf2_rref([row_mask(row) for row in M], n=M.shape[1])


def col_space(M: np.ndarray) -> Tuple[int, ...]:
    return gf2_rref([row_mask(row) for row in M.T], n=M.shape[0])


def sum_dim(A: Sequence[int], B: Sequence[int], n: int = N9) -> int:
    return gf2_rank(list(A) + list(B), n=n)


def intersection_dim(A: Sequence[int], B: Sequence[int], n: int = N9) -> int:
    return len(A) + len(B) - sum_dim(A, B, n=n)


@dataclass(frozen=True)
class Space:
    lam: int
    rank_lam: int
    r: int
    U: Tuple[int, ...]
    V: Tuple[int, ...]


def build_spaces() -> Dict[int, Space]:
    spaces: Dict[int, Space] = {}
    for lam in range(1, 256):
        L = lambda_mat(lam)
        d = rank_mat(L)
        M = contraction_mat(lam)
        r = rank_mat(M)
        if r != 3 * d:
            raise AssertionError((lam, d, r))
        spaces[lam] = Space(lam=lam, rank_lam=d, r=r, U=col_space(M), V=row_space(M))
    return spaces


SPACES = build_spaces()
RANK_DIST = collections.Counter(sp.rank_lam for sp in SPACES.values())


def parse_rank_set(spec: str) -> Tuple[int, ...]:
    s = spec.strip().lower()
    if s in {"all", "123", "1,2,3"}:
        return (1, 2, 3)
    if s in {"12", "1,2"}:
        return (1, 2)
    if s in {"3"}:
        return (3,)
    vals = tuple(sorted({int(x) for x in s.replace("+", ",").split(",") if x}))
    if not vals or any(v not in (1, 2, 3) for v in vals):
        raise ValueError(f"bad rank set: {spec}")
    return vals


def ceil_half_nonneg(v: int) -> int:
    if v <= 0:
        return 0
    return (int(v) + 1) // 2


def row_to_terms(row: Sequence[int]) -> List[Tuple[int, int, int]]:
    r = len(row) // 3
    return [(int(row[3 * t]), int(row[3 * t + 1]), int(row[3 * t + 2])) for t in range(r)]


def support_weights(us: Sequence[int]) -> Dict[int, int]:
    weights: Dict[int, int] = {}
    for lam in range(1, 256):
        weights[lam] = sum(1 for u in us if dot8(lam, int(u)))
    return weights


def m_from_weights(weights: Dict[int, int], nu: int, total_terms: int) -> int:
    return int(total_terms) if int(nu) == 0 else int(weights[int(nu)])


def check_excess_from_weights(
    weights: Dict[int, int],
    total_terms: int,
    source_ranks: Tuple[int, ...] = (1, 2, 3),
    target_ranks: Tuple[int, ...] = (1, 2),
    scalar_ranks: Tuple[int, ...] = (1, 2, 3),
    head_limit: int = 20,
) -> dict:
    """Evaluate the contraction-weight excess necessary condition on fixed weights."""
    scalar_violations = []
    scalar_by_rank = collections.Counter()
    for lam, sp in SPACES.items():
        if sp.rank_lam in scalar_ranks and weights[lam] < sp.r:
            item = {"lambda": lam, "rank_lambda": sp.rank_lam, "m": int(weights[lam]), "r": sp.r}
            scalar_violations.append(item)
            scalar_by_rank[sp.rank_lam] += 1

    tight_sources = [lam for lam, sp in SPACES.items() if sp.rank_lam in source_ranks and weights[lam] == sp.r]
    tight_rank_hist = collections.Counter(SPACES[lam].rank_lam for lam in tight_sources)

    target_records = {}
    leakage_violations = []
    side_bound_violations = []
    for mu, sp_mu in SPACES.items():
        if sp_mu.rank_lam not in target_ranks:
            continue
        m_mu = int(weights[mu])
        r_mu = sp_mu.r
        if m_mu < r_mu:
            # Already counted as scalar; no meaningful excess variables for this target.
            continue
        budget = m_mu - r_mu
        max_side = N9 - r_mu
        eB_lb = 0
        eC_lb = 0
        srcB = None
        srcC = None
        for lam in tight_sources:
            if lam == mu:
                continue
            sp_lam = SPACES[lam]
            nu = lam ^ mu
            m_nu = m_from_weights(weights, nu, total_terms)
            rhsB = sp_lam.r + m_mu - m_nu - 2 * intersection_dim(sp_lam.U, sp_mu.U)
            rhsC = sp_lam.r + m_mu - m_nu - 2 * intersection_dim(sp_lam.V, sp_mu.V)
            lbB = ceil_half_nonneg(rhsB)
            lbC = ceil_half_nonneg(rhsC)
            if lbB > eB_lb:
                h2 = int(weights[lam]) + m_mu - m_nu
                srcB = {"tight_lambda": lam, "rank_lambda": sp_lam.rank_lam, "h_twice": h2,
                        "h": h2 // 2 if h2 % 2 == 0 else None,
                        "m_lambda_plus_mu": m_nu,
                        "intersection_dim": intersection_dim(sp_lam.U, sp_mu.U), "rhs_twice": rhsB}
                eB_lb = lbB
            if lbC > eC_lb:
                h2 = int(weights[lam]) + m_mu - m_nu
                srcC = {"tight_lambda": lam, "rank_lambda": sp_lam.rank_lam, "h_twice": h2,
                        "h": h2 // 2 if h2 % 2 == 0 else None,
                        "m_lambda_plus_mu": m_nu,
                        "intersection_dim": intersection_dim(sp_lam.V, sp_mu.V), "rhs_twice": rhsC}
                eC_lb = lbC
        rec = {"lambda": mu, "rank_lambda": sp_mu.rank_lam, "m": m_mu, "r": r_mu,
               "budget": budget, "max_side_excess": max_side, "eB_lb": eB_lb,
               "eC_lb": eC_lb, "srcB": srcB, "srcC": srcC}
        target_records[mu] = rec
        if eB_lb > max_side or eC_lb > max_side:
            side_bound_violations.append(rec)
        if eB_lb + eC_lb > budget:
            leakage_violations.append(rec)

    leakage_by_source_pair = collections.Counter()
    for rec in leakage_violations:
        rb = None if rec["srcB"] is None else rec["srcB"]["rank_lambda"]
        rc = None if rec["srcC"] is None else rec["srcC"]["rank_lambda"]
        leakage_by_source_pair[(rb, rc)] += 1

    feasible = not scalar_violations and not side_bound_violations and not leakage_violations
    return {
        "total_terms": int(total_terms),
        "source_ranks": list(source_ranks),
        "target_ranks": list(target_ranks),
        "scalar_ranks": list(scalar_ranks),
        "scalar_violation_count": len(scalar_violations),
        "scalar_by_rank": {str(k): int(v) for k, v in sorted(scalar_by_rank.items())},
        "scalar_violations_head": scalar_violations[:head_limit],
        "tight_source_count": len(tight_sources),
        "tight_source_rank_hist": {str(k): int(v) for k, v in sorted(tight_rank_hist.items())},
        "leakage_violation_count": len(leakage_violations),
        "leakage_by_source_rank_pair": {str(k): int(v) for k, v in sorted(leakage_by_source_pair.items(), key=lambda kv: str(kv[0]))},
        "leakage_violations_head": leakage_violations[:head_limit],
        "side_bound_violation_count": len(side_bound_violations),
        "side_bound_violations_head": side_bound_violations[:head_limit],
        "target_count": len(target_records),
        "feasible_excess_assignment": bool(feasible),
    }


def check_a_list(us: Sequence[int], **kwargs) -> dict:
    weights = support_weights(us)
    out = check_excess_from_weights(weights, total_terms=len(us), **kwargs)
    out.update({
        "term_count": len(us),
        "distinct_A_count": len(set(int(u) for u in us)),
        "multiplicity_hist": {str(k): int(v) for k, v in sorted(collections.Counter(collections.Counter(int(u) for u in us).values()).items())},
        "total_A_weight": int(sum(int(u).bit_count() for u in us)),
    })
    return out


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
                key = tuple(sorted(us))
                if key in seen:
                    continue
                seen.add(key)
                out.append({"pool_row": idx, "deleted_terms": [a, b], "deleted_w": int(w), "u_masks": us})
    return out


def shadow_consistent(us: List[int]) -> Optional[bool]:
    if peer_shadow is None:
        return None
    try:
        return bool(peer_shadow.analyze_support(us)["full_shadow_consistent"])
    except Exception:
        return None


def coord_purity_pass(us: List[int]) -> Optional[bool]:
    if peer_purity is None:
        return None
    try:
        return not bool(peer_purity.build_purity_clauses(us, extended=True)["rejects_support"])
    except Exception:
        return None


def evaluate_calibration(max_samew: Optional[int] = None, head_limit: int = 20) -> dict:
    t0 = time.time()
    pool = np.load(POOL_PATH)
    pool_hist = collections.Counter()
    pool_reject_head = []
    for idx, row in enumerate(pool):
        us = [u for u, _v, _w in row_to_terms(row)]
        res = check_a_list(us, source_ranks=(1, 2, 3), target_ranks=(1, 2), scalar_ranks=(1, 2, 3), head_limit=5)
        key = (res["feasible_excess_assignment"], res["scalar_violation_count"], res["leakage_violation_count"])
        pool_hist[key] += 1
        if not res["feasible_excess_assignment"] and len(pool_reject_head) < head_limit:
            pool_reject_head.append({"row": idx, "result": res})

    known = {
        "L15_near_support": [1, 2, 3, 4, 8, 20, 24, 31, 32, 64, 73, 109, 127, 128, 141, 160, 182, 192, 219],
        "near_support": [1, 2, 3, 4, 8, 20, 24, 31, 32, 36, 64, 73, 127, 128, 141, 160, 182, 192, 219],
    }
    known_eval = {name: check_a_list(us, source_ranks=(1, 2, 3), target_ranks=(1, 2), scalar_ranks=(1, 2, 3), head_limit=head_limit) for name, us in known.items()}

    samew = same_w_deletion_lists()
    if max_samew is not None:
        samew = samew[:max_samew]
    sw_hist = collections.Counter()
    shadow_coord_survivors = 0
    rank12_scalar_clean = 0
    full_scalar_clean = 0
    excess_feasible_full = 0
    excess_reject_no_full_scalar = 0
    rank3_source_changes = 0
    survivor_head = []
    leak_only_head = []
    for i, rec in enumerate(samew):
        us = [int(u) for u in rec["u_masks"]]
        sh = shadow_consistent(us)
        cp = coord_purity_pass(us)
        if not (sh is True and cp is True):
            sw_hist[(sh, cp, "not_shadow_coord")] += 1
            continue
        shadow_coord_survivors += 1
        r12 = check_a_list(us, source_ranks=(1, 2), target_ranks=(1, 2), scalar_ranks=(1, 2), head_limit=3)
        allsrc = check_a_list(us, source_ranks=(1, 2, 3), target_ranks=(1, 2), scalar_ranks=(1, 2, 3), head_limit=5)
        if r12["scalar_violation_count"] == 0:
            rank12_scalar_clean += 1
        if allsrc["scalar_violation_count"] == 0:
            full_scalar_clean += 1
        if allsrc["feasible_excess_assignment"]:
            excess_feasible_full += 1
        if allsrc["scalar_violation_count"] == 0 and allsrc["leakage_violation_count"] > 0:
            excess_reject_no_full_scalar += 1
            if len(leak_only_head) < head_limit:
                leak_only_head.append({"index": i, "source": rec, "rank12": r12, "allsource_fullscalar": allsrc})
        if (r12["leakage_violation_count"], r12["feasible_excess_assignment"]) != (allsrc["leakage_violation_count"], allsrc["feasible_excess_assignment"]):
            rank3_source_changes += 1
        sw_hist[("survivor", allsrc["feasible_excess_assignment"], allsrc["scalar_violation_count"] > 0, allsrc["leakage_violation_count"] > 0)] += 1
        if len(survivor_head) < head_limit:
            survivor_head.append({"index": i, "source": rec, "shadow_ok": sh, "coord_purity_pass": cp, "rank12": r12, "allsource_fullscalar": allsrc})

    return {
        "schema": "s0908_contraction_weight_excess_eval_v1",
        "purpose": "Validate contraction-weight excess formulation and resolve same-W scalar cleanliness using all rank-1/2/3 contraction rank tests.",
        "spaces": {
            "convention": "M_lambda = Lambda^T tensor I3 with quotient bit 0 deleted; rank(M_lambda)=3 rank(Lambda).",
            "lambda_rank_distribution": {str(k): int(v) for k, v in sorted(RANK_DIST.items())},
        },
        "rank21_pool_excess_validation": {
            "pool_path": str(POOL_PATH),
            "rows": int(pool.shape[0]),
            "hist_feasible_scalar_leak": {str(k): int(v) for k, v in sorted(pool_hist.items(), key=lambda kv: str(kv[0]))},
            "all_pass": all(k[0] for k in pool_hist),
            "reject_head": pool_reject_head,
            "meaning": "A-only necessary conditions must not reject verified 21-term E11 core decompositions; this tests the formulation but not sufficiency.",
        },
        "known_near_supports": known_eval,
        "same_w_shadow_coordinate_survivor_reclassification": {
            "records_scanned": len(samew),
            "shadow_coord_survivors": shadow_coord_survivors,
            "rank12_scalar_clean_survivors": rank12_scalar_clean,
            "full_rank123_scalar_clean_survivors": full_scalar_clean,
            "full_excess_feasible_survivors": excess_feasible_full,
            "full_excess_reject_no_full_scalar_survivors": excess_reject_no_full_scalar,
            "rank3_source_changed_rank12_result_count": rank3_source_changes,
            "hist": {str(k): int(v) for k, v in sorted(sw_hist.items(), key=lambda kv: str(kv[0]))},
            "survivor_head": survivor_head,
            "leak_only_full_scalar_clean_head": leak_only_head,
            "meaning": "Same-W deletion lists remain local repeated-A near-misses; this table only resolves what their rejections are relative to the full scalar baseline and the all-source excess inequalities.",
        },
        "elapsed_sec": round(time.time() - t0, 3),
    }


def load_complete_records(cache: Path = CACHE_PATH):
    if cache.exists() and cache.stat().st_size > 0:
        try:
            with cache.open("rb") as f:
                payload = pickle.load(f)
            return payload["records"], payload.get("meta", {}) | {"cache_used": True, "cache_path": str(cache)}
        except Exception:
            pass
    t0 = time.time()
    lut, lut_meta = load_lut(LUT_PATH)
    records, meta = build_core_constraints(CoreQuotient(1), lut)
    meta = dict(meta)
    meta["lut_coverage_ok"] = lut_meta.get("coverage_ok")
    meta["cache_used"] = False
    meta["cache_path"] = str(cache)
    meta["build_sec"] = round(time.time() - t0, 3)
    cache.parent.mkdir(parents=True, exist_ok=True)
    with cache.open("wb") as f:
        pickle.dump({"records": records, "meta": meta}, f)
    return records, meta


def load_reduced_kept() -> set[int]:
    with REDUCED_PATH.open("rb") as f:
        red = pickle.load(f)
    return set(int(k) for k in red["kept_key8"])


def points_from_bitset(bs: int) -> List[int]:
    pts = []
    bs = int(bs)
    while bs:
        bit = bs & -bs
        pts.append(bit.bit_length())  # point p is stored at bit p-1
        bs ^= bit
    return pts


def add_wang_constraints(model, x: Dict[int, object], records: Sequence[dict], mode: str, s_rank: int, already_extra: Optional[set[int]] = None) -> dict:
    if mode == "none":
        return {"mode": mode, "added": 0, "skipped_not_kept": 0, "by_L": {}, "by_dim8": {}}
    kept = None
    if mode == "reduced":
        kept = load_reduced_kept()
    elif mode == "complete":
        kept = None
    else:
        raise ValueError(mode)
    by_L = collections.Counter()
    by_dim = collections.Counter()
    added = 0
    skipped = 0
    already_extra = already_extra or set()
    for rec in records:
        key = int(rec["key8"])
        if kept is not None and key not in kept and key not in already_extra:
            skipped += 1
            continue
        L = int(rec["L"])
        cap = int(s_rank) - L
        if cap >= s_rank:
            continue
        pts = points_from_bitset(int(rec["point_bitset"]))
        if pts:
            model.Add(sum(x[p] for p in pts) <= cap)
            added += 1
            by_L[L] += 1
            by_dim[int(rec["dim8"])] += 1
    return {"mode": mode, "added": added, "skipped_not_kept": skipped, "by_L": {str(k): int(v) for k, v in sorted(by_L.items())}, "by_dim8": {str(k): int(v) for k, v in sorted(by_dim.items())}}


def model_solve(args) -> dict:
    from ortools.sat.python import cp_model

    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    records, rec_meta = load_complete_records()
    source_ranks = parse_rank_set(args.source_ranks)
    target_ranks = parse_rank_set(args.target_ranks)
    scalar_ranks = parse_rank_set(args.scalar_ranks)
    s_rank = int(args.rank)

    model = cp_model.CpModel()
    x = {p: model.NewBoolVar(f"x_{p}") for p in POINTS}
    model.Add(sum(x.values()) == s_rank)
    if args.force_point:
        for p in args.force_point:
            model.Add(x[int(p)] == 1)
    if args.forbid_point:
        for p in args.forbid_point:
            model.Add(x[int(p)] == 0)

    m = {}
    for lam in range(1, 256):
        var = model.NewIntVar(0, s_rank, f"m_{lam}")
        model.Add(var == sum(x[p] for p in POINTS if dot8(lam, p)))
        m[lam] = var
    def m_expr(nu: int):
        return s_rank if int(nu) == 0 else m[int(nu)]

    scalar_count = 0
    scalar_by_rank = collections.Counter()
    for lam, sp in SPACES.items():
        if sp.rank_lam in scalar_ranks:
            model.Add(m[lam] >= sp.r)
            scalar_count += 1
            scalar_by_rank[sp.rank_lam] += 1

    already_extra: set[int] = set()
    wang_summary = add_wang_constraints(model, x, records, args.wang, s_rank, already_extra=already_extra)

    excess_summary = {"enabled": bool(args.use_excess)}
    if args.use_excess:
        eB = {}
        eC = {}
        target_lams = [lam for lam, sp in SPACES.items() if sp.rank_lam in target_ranks]
        for mu in target_lams:
            sp = SPACES[mu]
            max_side = N9 - sp.r
            eB[mu] = model.NewIntVar(0, max_side, f"eB_{mu}")
            eC[mu] = model.NewIntVar(0, max_side, f"eC_{mu}")
            model.Add(eB[mu] + eC[mu] <= m[mu] - sp.r)

        tight = {}
        source_lams = [lam for lam, sp in SPACES.items() if sp.rank_lam in source_ranks]
        for lam in source_lams:
            sp = SPACES[lam]
            b = model.NewBoolVar(f"tight_{lam}")
            tight[lam] = b
            model.Add(m[lam] == sp.r).OnlyEnforceIf(b)
            model.Add(m[lam] >= sp.r + 1).OnlyEnforceIf(b.Not())

        ineq_added_B = 0
        ineq_added_C = 0
        skipped_trivial_B = 0
        skipped_trivial_C = 0
        ineq_by_source_rank = collections.Counter()
        ineq_by_pair_rank = collections.Counter()
        for lam in source_lams:
            sp_lam = SPACES[lam]
            for mu in target_lams:
                if lam == mu:
                    continue
                sp_mu = SPACES[mu]
                nu = lam ^ mu
                # Maximum RHS using m_mu<=s_rank and scalar lower bound on m_nu when nu != 0.
                mnu_lb = 0 if nu == 0 else (SPACES[nu].r if SPACES[nu].rank_lam in scalar_ranks else 0)
                dU = intersection_dim(sp_lam.U, sp_mu.U)
                dV = intersection_dim(sp_lam.V, sp_mu.V)
                rhsmaxB = sp_lam.r + s_rank - mnu_lb - 2 * dU
                rhsmaxC = sp_lam.r + s_rank - mnu_lb - 2 * dV
                if rhsmaxB > 0:
                    model.Add(2 * eB[mu] >= sp_lam.r + m[mu] - m_expr(nu) - 2 * dU).OnlyEnforceIf(tight[lam])
                    ineq_added_B += 1
                else:
                    skipped_trivial_B += 1
                if rhsmaxC > 0:
                    model.Add(2 * eC[mu] >= sp_lam.r + m[mu] - m_expr(nu) - 2 * dV).OnlyEnforceIf(tight[lam])
                    ineq_added_C += 1
                else:
                    skipped_trivial_C += 1
                if rhsmaxB > 0 or rhsmaxC > 0:
                    ineq_by_source_rank[sp_lam.rank_lam] += int(rhsmaxB > 0) + int(rhsmaxC > 0)
                    ineq_by_pair_rank[(sp_lam.rank_lam, sp_mu.rank_lam)] += int(rhsmaxB > 0) + int(rhsmaxC > 0)
        excess_summary = {
            "enabled": True,
            "source_ranks": list(source_ranks),
            "target_ranks": list(target_ranks),
            "target_count": len(target_lams),
            "source_count": len(source_lams),
            "excess_variables": 2 * len(target_lams),
            "tight_booleans": len(source_lams),
            "leakage_inequalities_B": ineq_added_B,
            "leakage_inequalities_C": ineq_added_C,
            "skipped_trivial_B": skipped_trivial_B,
            "skipped_trivial_C": skipped_trivial_C,
            "ineq_by_source_rank": {str(k): int(v) for k, v in sorted(ineq_by_source_rank.items())},
            "ineq_by_source_target_rank": {str(k): int(v) for k, v in sorted(ineq_by_pair_rank.items(), key=lambda kv: str(kv[0]))},
        }

    total_weight = model.NewIntVar(0, NS * s_rank, "total_A_weight")
    model.Add(total_weight == sum(int(p).bit_count() * x[p] for p in POINTS))
    if args.target_weight is not None:
        model.Add(total_weight == int(args.target_weight))
    if args.min_weight is not None:
        model.Add(total_weight >= int(args.min_weight))
    if args.max_weight is not None:
        model.Add(total_weight <= int(args.max_weight))
    if args.minimize_weight:
        model.Minimize(total_weight)
    if args.maximize_weight:
        model.Maximize(total_weight)

    build_sec = time.time() - t0
    rounds = []
    candidate_found = None
    # Keep adding complete rows only in reduced mode when a returned support violates them.
    for rnd in range(int(args.max_rounds)):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = float(args.solver_time)
        solver.parameters.num_search_workers = int(args.workers)
        solver.parameters.random_seed = int(args.seed + rnd)
        if args.log_search:
            solver.parameters.log_search_progress = True
        ts = time.time()
        status = solver.Solve(model)
        solve_sec = time.time() - ts
        status_name = solver.StatusName(status)
        rec = {"round": rnd, "status": status_name, "solve_sec": round(solve_sec, 3), "response_stats": solver.ResponseStats()}
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            rounds.append(rec)
            break
        A = [p for p in POINTS if solver.Value(x[p])]
        tw = int(solver.Value(total_weight))
        weights = {lam: int(solver.Value(m[lam])) for lam in range(1, 256)}
        ex_eval = check_excess_from_weights(weights, total_terms=s_rank, source_ranks=source_ranks,
                                            target_ranks=target_ranks, scalar_ranks=scalar_ranks, head_limit=10)
        scan = complete_core_wang_scan(f"round_{rnd}", A, s_rank, records, max_head=12)
        new_rows = []
        if args.wang == "reduced" and scan["complete_violation_count"]:
            selected = set(A)
            kept = load_reduced_kept()
            for rec0 in records:
                key = int(rec0["key8"])
                if key in kept or key in already_extra:
                    continue
                cap = s_rank - int(rec0["L"])
                if cap >= s_rank:
                    continue
                pts = points_from_bitset(int(rec0["point_bitset"]))
                occ = sum(1 for p in pts if p in selected)
                if occ > cap:
                    model.Add(sum(x[p] for p in pts) <= cap)
                    already_extra.add(key)
                    if len(new_rows) < 20:
                        new_rows.append({"key8": key, "L": int(rec0["L"]), "cap": cap,
                                         "dim8": int(rec0["dim8"]), "occ": occ, "excess": occ - cap})
        rec.update({
            "A_support": A,
            "total_A_weight": tw,
            "weight_rank_hist": {str(k): int(v) for k, v in sorted(collections.Counter(weights.values()).items())},
            "excess_eval": ex_eval,
            "complete_wang_scan": {k: scan[k] for k in ["complete_violation_count", "max_excess", "violations_by_dim8", "violations_by_full_lut_L", "violations_by_excess", "violations_head"]},
            "new_complete_rows_added": len(new_rows),
            "new_rows_head": new_rows,
        })
        rounds.append(rec)
        if scan["complete_violation_count"] == 0 and ex_eval["feasible_excess_assignment"]:
            candidate_found = {"round": rnd, "A_support": A, "total_A_weight": tw, "meaning": "A distinct 19-point support satisfying complete Wang and contraction-weight excess necessary conditions; still requires shadow and exact B/C completion."}
            break
        # Avoid returning the same failed support.
        model.Add(sum(x[p] for p in A) <= s_rank - 1)

    result = {
        "schema": "s0908_contraction_weight_excess_solve_v1",
        "purpose": "Coverage-preserving CP-SAT support experiment using contraction weights and guarded integer excess variables.",
        "parameters": vars(args) | {"out": str(args.out)},
        "spaces": {
            "convention": "M_lambda = Lambda^T tensor I3; quotient directions are 8-bit masks bits 0..7.",
            "lambda_rank_distribution": {str(k): int(v) for k, v in sorted(RANK_DIST.items())},
        },
        "complete_records_meta": rec_meta,
        "constraint_summary": {
            "rank": s_rank,
            "distinct_points": 255,
            "scalar_bounds": {"count": scalar_count, "by_rank": {str(k): int(v) for k, v in sorted(scalar_by_rank.items())}},
            "wang": wang_summary,
            "excess": excess_summary,
            "weight_bounds": {"target": args.target_weight, "min": args.min_weight, "max": args.max_weight, "minimize": args.minimize_weight, "maximize": args.maximize_weight},
            "extra_complete_rows_added_total": len(already_extra),
        },
        "model_stats": model.ModelStats(),
        "build_sec": round(build_sec, 3),
        "rounds": rounds,
        "candidate_found": candidate_found,
        "elapsed_sec": round(time.time() - t0, 3),
        "interpretation": "Feasible supports pass only necessary A-level conditions. UNKNOWN or non-proof UNSAT is not a rank lower-bound proof.",
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--action", choices=["eval", "solve"], required=True)
    ap.add_argument("--out", type=Path, default=OUTDIR / "result.json")
    # Evaluation options
    ap.add_argument("--max-samew", type=int, default=None)
    # Solve options
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--wang", choices=["none", "reduced", "complete"], default="reduced")
    ap.add_argument("--use-excess", action="store_true")
    ap.add_argument("--source-ranks", default="123")
    ap.add_argument("--target-ranks", default="12")
    ap.add_argument("--scalar-ranks", default="123")
    ap.add_argument("--solver-time", type=float, default=60.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=1001)
    ap.add_argument("--max-rounds", type=int, default=1)
    ap.add_argument("--target-weight", type=int, default=None)
    ap.add_argument("--min-weight", type=int, default=None)
    ap.add_argument("--max-weight", type=int, default=None)
    ap.add_argument("--minimize-weight", action="store_true")
    ap.add_argument("--maximize-weight", action="store_true")
    ap.add_argument("--force-point", type=int, nargs="*", default=[])
    ap.add_argument("--forbid-point", type=int, nargs="*", default=[])
    ap.add_argument("--log-search", action="store_true")
    args = ap.parse_args()

    if args.action == "eval":
        result = evaluate_calibration(max_samew=args.max_samew)
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
        print(json.dumps({
            "out": str(args.out),
            "pool_all_pass": result["rank21_pool_excess_validation"]["all_pass"],
            "known_feasible": {k: v["feasible_excess_assignment"] for k, v in result["known_near_supports"].items()},
            "samew": {k: result["same_w_shadow_coordinate_survivor_reclassification"][k] for k in ["records_scanned", "shadow_coord_survivors", "rank12_scalar_clean_survivors", "full_rank123_scalar_clean_survivors", "full_excess_feasible_survivors", "full_excess_reject_no_full_scalar_survivors", "rank3_source_changed_rank12_result_count"]},
            "elapsed_sec": result["elapsed_sec"],
        }, indent=2, sort_keys=True))
    else:
        result = model_solve(args)
        last = result["rounds"][-1] if result["rounds"] else None
        brief_last = None
        if last is not None:
            brief_last = {k: last.get(k) for k in ["round", "status", "solve_sec", "total_A_weight", "new_complete_rows_added"]}
            if "complete_wang_scan" in last:
                brief_last["complete_wang_viol"] = last["complete_wang_scan"]["complete_violation_count"]
            if "excess_eval" in last:
                brief_last["excess_feasible"] = last["excess_eval"]["feasible_excess_assignment"]
                brief_last["scalar_viol"] = last["excess_eval"]["scalar_violation_count"]
                brief_last["leak_viol"] = last["excess_eval"]["leakage_violation_count"]
        print(json.dumps({
            "out": str(args.out),
            "build_sec": result["build_sec"],
            "constraint_summary": result["constraint_summary"],
            "last": brief_last,
            "candidate_found": result["candidate_found"],
            "elapsed_sec": result["elapsed_sec"],
        }, indent=2, sort_keys=True)[:12000])


if __name__ == "__main__":
    main()
