#!/usr/bin/env python3
r"""analysis: mixed-source support cuts from unconditional leakage.

For target mu, B-source lam, C-source nu, the unconditional leakage
bounds plus the Sylvester budget imply the support-only inequality

    m_lam + m_{lam+mu} + m_nu + m_{nu+mu} >= 2K,
    K = r_mu + r_lam + r_nu - d_B(lam,mu) - d_C(nu,mu).

Equivalently, for distinct support variables x_p,

    sum_p c_p x_p >= K,

where c_p = 1 if mu(p)=1, and c_p=lambda(p)+nu(p) (ordinary integer
sum 0,1,2) if mu(p)=0.  The zero contraction has m_0=0, not the number
of terms; this matters when a source equals the target.

This script compares these inequalities with canonical Wang occupation
rows.  If D=span{lam,mu,nu} in the dual quotient space, then the cut's
left-hand side is at least the number of selected points active on D,
which is bounded below by the Wang row for D^perp.  Thus a cut is
single-row Wang dominated whenever L(D) >= K.

The computations here are support-level necessary-condition experiments,
not tensor rank proofs.
"""
from __future__ import annotations

import argparse
import collections
import json
import sys
import time
from functools import lru_cache
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

SCRIPTS = Path("scripts")
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import contraction_weight_excess_search as base  # noqa:E402
from unconditional_leakage import get_intersection_dims  # noqa:E402

OUTDIR = Path("data/mixed_source_cuts")
POINTS = base.POINTS
TARGETS_12 = [mu for mu, sp in base.SPACES.items() if sp.rank_lam <= 2]
SOURCES_ALL = list(base.SPACES.keys())


def weights_for_support(us: Sequence[int]) -> Dict[int, int]:
    return base.support_weights(us)


def m_from_weights_zero(weights: Dict[int, int], alpha: int) -> int:
    """Contraction active count with m_0=0."""
    return 0 if int(alpha) == 0 else int(weights[int(alpha)])


@lru_cache(maxsize=None)
def dual_basis_key(rows_tuple: Tuple[int, ...]) -> Tuple[int, ...]:
    rows = [int(r) for r in rows_tuple if int(r) != 0]
    return tuple(base.gf2_rref(rows, n=8))


@lru_cache(maxsize=None)
def annihilator_bitset_for_basis(basis: Tuple[int, ...]) -> int:
    """Bitset of nonzero primal points p annihilated by every dual basis row."""
    bs = 0
    for p in POINTS:
        ok = True
        for a in basis:
            if base.dot8(a, p):
                ok = False
                break
        if ok:
            bs |= 1 << (p - 1)
    return bs


def build_wang_by_annihilator() -> Tuple[Dict[int, dict], dict]:
    records, meta = base.load_complete_records()
    by_bs = {int(rec["point_bitset"]): rec for rec in records}
    return by_bs, meta


_WANG_BY_BS = None
_WANG_META = None


def wang_by_bs():
    global _WANG_BY_BS, _WANG_META
    if _WANG_BY_BS is None:
        _WANG_BY_BS, _WANG_META = build_wang_by_annihilator()
    return _WANG_BY_BS, _WANG_META


@lru_cache(maxsize=None)
def wang_L_for_dual_span_sorted(sorted_rows: Tuple[int, ...]) -> dict:
    basis = dual_basis_key(tuple(sorted_rows))
    ann_bs = annihilator_bitset_for_basis(basis)
    by_bs, _meta = wang_by_bs()
    rec = by_bs.get(ann_bs)
    if rec is None:
        raise KeyError(f"annihilator bitset not found for dual basis {basis}")
    return {
        "dual_basis": list(basis),
        "dual_dim": len(basis),
        "annihilator_point_bitset": int(ann_bs),
        "annihilator_dim8": int(rec["dim8"]),
        "annihilator_key8": int(rec["key8"]),
        "annihilator_key9": int(rec["key9"]),
        "L_D": int(rec["L"]),
        "cap_for_s19": 19 - int(rec["L"]),
        "annihilator_point_count": int(rec["point_count"]),
    }


def wang_L_for_dual_span(rows: Iterable[int]) -> dict:
    basis = tuple(base.gf2_rref([int(r) for r in rows if int(r) != 0], n=8))
    return wang_L_for_dual_span_sorted(tuple(sorted(basis)))


@lru_cache(maxsize=None)
def coeff_bitsets(mu: int, lam: int, nu: int) -> Tuple[int, int, int, Tuple[int, int, int]]:
    """Return (coeff1_bitset, coeff2_bitset, positive_bitset, counts[0..2])."""
    bs1 = 0
    bs2 = 0
    counts = [0, 0, 0]
    for p in POINTS:
        if base.dot8(mu, p):
            c = 1
        else:
            c = base.dot8(lam, p) + base.dot8(nu, p)
        counts[c] += 1
        if c == 1:
            bs1 |= 1 << (p - 1)
        elif c == 2:
            bs2 |= 1 << (p - 1)
    return bs1, bs2, bs1 | bs2, (counts[0], counts[1], counts[2])


def cut_params(mu: int, lam: int, nu: int, dB_tbl=None, dC_tbl=None) -> dict:
    if dB_tbl is None or dC_tbl is None:
        dB_tbl, dC_tbl = get_intersection_dims()
    sp_mu = base.SPACES[int(mu)]
    sp_lam = base.SPACES[int(lam)]
    sp_nu = base.SPACES[int(nu)]
    dB = int(dB_tbl[(int(lam), int(mu))])
    dC = int(dC_tbl[(int(nu), int(mu))])
    K = int(sp_mu.r + sp_lam.r + sp_nu.r - dB - dC)
    wrec = wang_L_for_dual_span([lam, mu, nu])
    bs1, bs2, pos, counts = coeff_bitsets(int(mu), int(lam), int(nu))
    return {
        "mu": int(mu),
        "lam_B": int(lam),
        "nu_C": int(nu),
        "rank_mu": int(sp_mu.rank_lam),
        "rank_lam_B": int(sp_lam.rank_lam),
        "rank_nu_C": int(sp_nu.rank_lam),
        "r_mu": int(sp_mu.r),
        "r_lam_B": int(sp_lam.r),
        "r_nu_C": int(sp_nu.r),
        "dB_lam_mu": dB,
        "dC_nu_mu": dC,
        "K": K,
        "coeff_counts_0_1_2": list(counts),
        "coeff1_bitset": int(bs1),
        "coeff2_bitset": int(bs2),
        "positive_bitset": int(pos),
        "single_wang": wrec,
        "single_wang_dominated": bool(wrec["L_D"] >= K),
        "single_wang_gap_K_minus_L": int(K - wrec["L_D"]),
    }


def cut_lhs_for_support(mu: int, lam: int, nu: int, us: Sequence[int]) -> dict:
    w = weights_for_support(us)
    lhs2 = (m_from_weights_zero(w, lam) + m_from_weights_zero(w, lam ^ mu) +
            m_from_weights_zero(w, nu) + m_from_weights_zero(w, nu ^ mu))
    if lhs2 % 2:
        raise AssertionError((mu, lam, nu, lhs2))
    lhs = lhs2 // 2
    bs1, bs2, pos, _counts = coeff_bitsets(mu, lam, nu)
    support_bs = 0
    coeff_sum = 0
    active = 0
    coeff2 = 0
    for p in us:
        p = int(p)
        support_bs |= 1 << (p - 1)
        if (bs2 >> (p - 1)) & 1:
            coeff_sum += 2
            active += 1
            coeff2 += 1
        elif (bs1 >> (p - 1)) & 1:
            coeff_sum += 1
            active += 1
    if coeff_sum != lhs:
        raise AssertionError((mu, lam, nu, lhs, coeff_sum))
    return {"lhs": int(lhs), "lhs_twice": int(lhs2), "active_on_D": int(active), "coeff2_selected": int(coeff2)}


def diagnose_known() -> dict:
    t0 = time.time()
    dB_tbl, dC_tbl = get_intersection_dims()
    known_file = OUTDIR.parent / "unconditional_leakage/l15_violation_details.json"
    with known_file.open() as f:
        known_diag = json.load(f)
    result = {
        "schema": "s0908_mixed_source_cut_diagnose_v1",
        "purpose": "Convert analysis best B/C leakage pairs for L15 and analysis into direct support cuts and compare with the single Wang row for D=span(lambda,mu,nu).",
        "source_file": str(known_file),
        "items": {},
    }
    for name, block in known_diag.items():
        us = [int(x) for x in block["support"]]
        items = []
        for v in block["violations"]:
            mu = int(v["target_mu"])
            lam = int(v["best_src_B"]["lam"])
            nu = int(v["best_src_C"]["lam"])
            cp = cut_params(mu, lam, nu, dB_tbl, dC_tbl)
            lhs = cut_lhs_for_support(mu, lam, nu, us)
            ann_bs = int(cp["single_wang"]["annihilator_point_bitset"])
            support_bs = 0
            for p in us:
                support_bs |= 1 << (int(p) - 1)
            occ_ann = (support_bs & ann_bs).bit_count()
            outside = len(us) - occ_ann
            cp_small = {k: v for k, v in cp.items() if k not in ("coeff1_bitset", "coeff2_bitset", "positive_bitset")}
            item = {
                **cp_small,
                "support_lhs": lhs["lhs"],
                "support_active_on_D": outside,
                "support_coeff2_selected": lhs["coeff2_selected"],
                "violates_mixed_cut": bool(lhs["lhs"] < cp["K"]),
                "violates_single_wang_D_row": bool(outside < cp["single_wang"]["L_D"]),
                "annihilator_occupancy": int(occ_ann),
                "annihilator_capacity_s19": int(cp["single_wang"]["cap_for_s19"]),
                "support_wang_excess_for_D": int(max(0, occ_ann - cp["single_wang"]["cap_for_s19"])),
                "interpretation": "single Wang dominated" if cp["single_wang_dominated"] else "not dominated by the D^perp Wang row",
            }
            items.append(item)
        result["items"][name] = {
            "support_size": len(us),
            "violation_count": int(block["violation_count"]),
            "best_pair_cuts": items,
            "all_best_pair_cuts_single_wang_dominated": all(it["single_wang_dominated"] for it in items),
        }
    result["elapsed_sec"] = round(time.time() - t0, 3)
    return result


def support_cut_violation_scan(name: str, us: Sequence[int], max_records: int = 30) -> dict:
    """Scan all mixed-source cuts for a fixed support and classify violated cuts."""
    t0 = time.time()
    dB_tbl, dC_tbl = get_intersection_dims()
    w = weights_for_support(us)
    stats = collections.Counter()
    by_target = collections.Counter()
    by_gap = collections.Counter()
    records = []
    non_dominated_records = []
    for mu in TARGETS_12:
        sp_mu = base.SPACES[mu]
        for lam in SOURCES_ALL:
            sp_lam = base.SPACES[lam]
            lhs_a = m_from_weights_zero(w, lam) + m_from_weights_zero(w, lam ^ mu)
            dB = int(dB_tbl[(lam, mu)])
            for nu in SOURCES_ALL:
                sp_nu = base.SPACES[nu]
                lhs2 = lhs_a + m_from_weights_zero(w, nu) + m_from_weights_zero(w, nu ^ mu)
                K = int(sp_mu.r + sp_lam.r + sp_nu.r - dB - int(dC_tbl[(nu, mu)]))
                if lhs2 >= 2 * K:
                    continue
                wrec = wang_L_for_dual_span([lam, mu, nu])
                dominated = wrec["L_D"] >= K
                gap = K - wrec["L_D"]
                stats[("violated", "dominated" if dominated else "not_single_dominated")] += 1
                stats[("violated_dimD", wrec["dual_dim"])] += 1
                by_target[mu] += 1
                by_gap[gap] += 1
                rec = {
                    "mu": int(mu), "lam_B": int(lam), "nu_C": int(nu),
                    "K": int(K), "lhs": int(lhs2 // 2), "lhs_twice": int(lhs2),
                    "gap_K_minus_LD": int(gap), "L_D": int(wrec["L_D"]),
                    "dual_dim": int(wrec["dual_dim"]),
                    "single_wang_dominated": bool(dominated),
                    "rank_tuple": [int(sp_mu.rank_lam), int(sp_lam.rank_lam), int(sp_nu.rank_lam)],
                    "r_tuple": [int(sp_mu.r), int(sp_lam.r), int(sp_nu.r)],
                    "dB": dB, "dC": int(dC_tbl[(nu, mu)]),
                }
                if len(records) < max_records:
                    records.append(rec)
                if not dominated and len(non_dominated_records) < max_records:
                    non_dominated_records.append(rec)
    return {
        "name": name,
        "support_size": len(us),
        "elapsed_sec": round(time.time() - t0, 3),
        "stats": {str(k): int(v) for k, v in sorted(stats.items(), key=lambda kv: str(kv[0]))},
        "violated_by_target_head": {str(k): int(v) for k, v in by_target.most_common(20)},
        "gap_hist": {str(k): int(v) for k, v in sorted(by_gap.items())},
        "records_head": records,
        "non_single_dominated_head": non_dominated_records,
    }


def scan_known_all(max_records: int = 30) -> dict:
    known = {
        "L15": [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219],
        "analysis": [1,2,3,4,8,20,24,31,32,36,64,73,127,128,141,160,182,192,219],
    }
    return {
        "schema": "s0908_all_mixed_cut_violations_known_v1",
        "purpose": "Scan all target/source/source mixed cuts violated by L15 and analysis and determine whether any such violation is not dominated by the D^perp Wang row.",
        "known": {name: support_cut_violation_scan(name, us, max_records=max_records) for name, us in known.items()},
    }


def enumerate_cut_dominance(sample_limit: int = 0, max_gap_records: int = 50) -> dict:
    """Enumerate all target/source/source triples and count single-Wang dominance.

    This does not materialize CP-SAT constraints.  It records whether the direct
    mixed-source inequality can be stronger than the single Wang lower bound for
    the same dual span.
    """
    t0 = time.time()
    dB_tbl, dC_tbl = get_intersection_dims()
    stats = collections.Counter()
    by_dim_gap = collections.Counter()
    by_rank_tuple_gap = collections.Counter()
    gap_hist = collections.Counter()
    positive_gap_records = []
    processed = 0
    for mu in TARGETS_12:
        sp_mu = base.SPACES[mu]
        for lam in SOURCES_ALL:
            sp_lam = base.SPACES[lam]
            dB = int(dB_tbl[(lam, mu)])
            for nu in SOURCES_ALL:
                sp_nu = base.SPACES[nu]
                K = int(sp_mu.r + sp_lam.r + sp_nu.r - dB - int(dC_tbl[(nu, mu)]))
                wrec = wang_L_for_dual_span([lam, mu, nu])
                gap = K - int(wrec["L_D"])
                dimD = int(wrec["dual_dim"])
                stats["triples_total"] += 1
                stats[f"target_rank_{sp_mu.rank_lam}"] += 1
                if gap <= 0:
                    stats["single_wang_dominated"] += 1
                else:
                    stats["not_single_wang_dominated"] += 1
                    if len(positive_gap_records) < max_gap_records:
                        positive_gap_records.append({
                            "mu": int(mu), "lam_B": int(lam), "nu_C": int(nu),
                            "K": int(K), "L_D": int(wrec["L_D"]), "gap": int(gap),
                            "dual_dim": dimD,
                            "rank_tuple": [int(sp_mu.rank_lam), int(sp_lam.rank_lam), int(sp_nu.rank_lam)],
                            "r_tuple": [int(sp_mu.r), int(sp_lam.r), int(sp_nu.r)],
                            "dB": dB, "dC": int(dC_tbl[(nu, mu)]),
                        })
                gap_hist[gap] += 1
                by_dim_gap[(dimD, gap)] += 1
                by_rank_tuple_gap[(sp_mu.rank_lam, sp_lam.rank_lam, sp_nu.rank_lam, gap)] += 1
                processed += 1
                if sample_limit and processed >= sample_limit:
                    break
            if sample_limit and processed >= sample_limit:
                break
        if sample_limit and processed >= sample_limit:
            break
    return {
        "schema": "s0908_mixed_cut_global_dominance_v1",
        "purpose": "Count whether mixed-source support cuts are dominated by the single Wang row for D=span(lambda,mu,nu).",
        "sample_limit": int(sample_limit),
        "elapsed_sec": round(time.time() - t0, 3),
        "stats": {str(k): int(v) for k, v in sorted(stats.items(), key=lambda kv: str(kv[0]))},
        "gap_hist": {str(k): int(v) for k, v in sorted(gap_hist.items())},
        "by_dim_gap_head": {str(k): int(v) for k, v in sorted(by_dim_gap.items(), key=lambda kv: (kv[0][0], kv[0][1]))[:100]},
        "by_rank_tuple_gap_head": {str(k): int(v) for k, v in sorted(by_rank_tuple_gap.items(), key=lambda kv: str(kv[0]))[:120]},
        "positive_gap_records_head": positive_gap_records,
    }


def build_unique_nondominated_cuts(min_gap: int = 1, max_cuts: int = 200000, sort_by: str = "gapK") -> dict:
    """Build unique non-single-Wang-dominated cut patterns with strongest K.

    Pattern is represented by (coeff1_bitset, coeff2_bitset).  For each pattern
    retain the maximum K and one realizing triple.  This is intended for later
    DFS/PB experiments; it avoids storing all source-pair derivations.
    """
    t0 = time.time()
    dB_tbl, dC_tbl = get_intersection_dims()
    best: Dict[Tuple[int, int], dict] = {}
    raw_nondom = 0
    for mu in TARGETS_12:
        sp_mu = base.SPACES[mu]
        for lam in SOURCES_ALL:
            sp_lam = base.SPACES[lam]
            dB = int(dB_tbl[(lam, mu)])
            for nu in SOURCES_ALL:
                sp_nu = base.SPACES[nu]
                K = int(sp_mu.r + sp_lam.r + sp_nu.r - dB - int(dC_tbl[(nu, mu)]))
                wrec = wang_L_for_dual_span([lam, mu, nu])
                gap = K - int(wrec["L_D"])
                if gap < min_gap:
                    continue
                raw_nondom += 1
                bs1, bs2, _pos, counts = coeff_bitsets(mu, lam, nu)
                key = (int(bs1), int(bs2))
                old = best.get(key)
                if old is None or K > old["K"] or (K == old["K"] and gap > old["gap_K_minus_LD"]):
                    best[key] = {
                        "mu": int(mu), "lam_B": int(lam), "nu_C": int(nu),
                        "K": int(K), "L_D": int(wrec["L_D"]), "gap_K_minus_LD": int(gap),
                        "dual_dim": int(wrec["dual_dim"]),
                        "rank_tuple": [int(sp_mu.rank_lam), int(sp_lam.rank_lam), int(sp_nu.rank_lam)],
                        "r_tuple": [int(sp_mu.r), int(sp_lam.r), int(sp_nu.r)],
                        "dB": dB, "dC": int(dC_tbl[(nu, mu)]),
                        "coeff_counts_0_1_2": list(counts),
                        "coeff1_bitset": int(bs1), "coeff2_bitset": int(bs2),
                    }
    cuts = list(best.values())
    if sort_by == "gapK":
        cuts.sort(key=lambda c: (c["gap_K_minus_LD"], c["K"], c["dual_dim"]), reverse=True)
    elif sort_by == "K":
        cuts.sort(key=lambda c: (c["K"], c["gap_K_minus_LD"], c["dual_dim"]), reverse=True)
    else:
        cuts.sort(key=lambda c: (c["dual_dim"], c["gap_K_minus_LD"], c["K"]), reverse=True)
    if max_cuts and len(cuts) > max_cuts:
        cuts_out = cuts[:max_cuts]
        truncated = True
    else:
        cuts_out = cuts
        truncated = False
    return {
        "schema": "s0908_unique_nondominated_mixed_cuts_v1",
        "purpose": "Unique coefficient-pattern mixed cuts not dominated by the single Wang row; stored for partial-support pruning experiments.",
        "min_gap": int(min_gap),
        "raw_nondominated_triples": int(raw_nondom),
        "unique_patterns": int(len(cuts)),
        "returned_cuts": int(len(cuts_out)),
        "truncated": bool(truncated),
        "sort_by": sort_by,
        "gap_hist_unique": {str(k): int(v) for k, v in sorted(collections.Counter(c["gap_K_minus_LD"] for c in cuts).items())},
        "K_hist_unique": {str(k): int(v) for k, v in sorted(collections.Counter(c["K"] for c in cuts).items())},
        "dual_dim_hist_unique": {str(k): int(v) for k, v in sorted(collections.Counter(c["dual_dim"] for c in cuts).items())},
        "cuts": cuts_out,
        "elapsed_sec": round(time.time() - t0, 3),
    }


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("diagnose-known")
    p.add_argument("--out", default=str(OUTDIR / "known_best_pair_dominance.json"))
    p = sub.add_parser("scan-known-all")
    p.add_argument("--max-records", type=int, default=30)
    p.add_argument("--out", default=str(OUTDIR / "known_all_mixed_cut_violations.json"))
    p = sub.add_parser("enumerate-dominance")
    p.add_argument("--sample-limit", type=int, default=0)
    p.add_argument("--max-gap-records", type=int, default=50)
    p.add_argument("--out", default=str(OUTDIR / "global_mixed_cut_dominance.json"))
    p = sub.add_parser("build-cuts")
    p.add_argument("--min-gap", type=int, default=1)
    p.add_argument("--max-cuts", type=int, default=200000)
    p.add_argument("--sort-by", choices=["gapK", "K", "dim"], default="gapK")
    p.add_argument("--out", default=str(OUTDIR / "unique_nondominated_cuts.json"))
    args = ap.parse_args()

    OUTDIR.mkdir(parents=True, exist_ok=True)
    if args.cmd == "diagnose-known":
        result = diagnose_known()
    elif args.cmd == "scan-known-all":
        result = scan_known_all(max_records=args.max_records)
    elif args.cmd == "enumerate-dominance":
        result = enumerate_cut_dominance(sample_limit=args.sample_limit, max_gap_records=args.max_gap_records)
    elif args.cmd == "build-cuts":
        result = build_unique_nondominated_cuts(min_gap=args.min_gap, max_cuts=args.max_cuts, sort_by=args.sort_by)
    else:
        raise ValueError(args.cmd)

    outpath = Path(args.out)
    outpath.parent.mkdir(parents=True, exist_ok=True)
    with outpath.open("w") as f:
        json.dump(result, f, indent=2, sort_keys=True)
    # Print compact summary without huge cuts.
    compact = dict(result)
    if "cuts" in compact:
        compact["cuts_head"] = compact["cuts"][:5]
        compact.pop("cuts", None)
    print(json.dumps(compact, indent=2, sort_keys=True)[:12000])


if __name__ == "__main__":
    main()
