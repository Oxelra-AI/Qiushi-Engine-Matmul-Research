#!/usr/bin/env python3
r"""analysisb: test whether mixed-source cuts follow from Wang rows inside D.

For a mixed cut derived from (mu, lambda_B, nu_C), its coefficients depend only on
D=span(mu,lambda,nu).  The review noted single-row domination by the Wang row
for D^perp when L(D)>=K.  This script goes one ARTIFACT further: within the quotient
by D^perp, impose ALL Wang lower bounds L(E) for nonzero subspaces E<=D and solve
the tiny integer problem over the 2^dim(D) pattern counts.  If the resulting
minimum of the mixed left side is >=K, the cut is implied by the local family of
Wang rows living inside D.  If not, it is not explained by those D-local rows,
though it might still be implied by Wang rows involving directions outside D.
"""
from __future__ import annotations

import argparse
import collections
import json
import sys
import time
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

SCRIPTS = Path("scripts")
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import contraction_weight_excess_search as base  # noqa:E402
import mixed_source_cuts as cuts  # noqa:E402
from unconditional_leakage import get_intersection_dims  # noqa:E402

OUTDIR = Path("data/mixed_source_cuts")


def xor_combo(basis: Sequence[int], alpha: int) -> int:
    v = 0
    for i, b in enumerate(basis):
        if (alpha >> i) & 1:
            v ^= int(b)
    return v


@lru_cache(maxsize=None)
def subspace_bases_coord(d: int) -> Tuple[Tuple[int, ...], ...]:
    vecs = list(range(1, 1 << d))
    out = {tuple()}  # include zero for completeness
    for r in range(1, d + 1):
        for comb in combinations(vecs, r):
            rb = tuple(base.gf2_rref(comb, n=d))
            if len(rb) == r:
                out.add(rb)
    return tuple(sorted(out, key=lambda b: (len(b), b)))


@lru_cache(maxsize=None)
def point_pattern_counts(D_basis: Tuple[int, ...]) -> Tuple[int, ...]:
    d = len(D_basis)
    counts = [0] * (1 << d)
    for p in base.POINTS:
        pat = 0
        for i, row in enumerate(D_basis):
            if base.dot8(row, p):
                pat |= 1 << i
        counts[pat] += 1
    return tuple(counts)


def coords_of_in_D(D_basis: Tuple[int, ...], v: int) -> int:
    for alpha in range(1 << len(D_basis)):
        if xor_combo(D_basis, alpha) == int(v):
            return alpha
    raise ValueError(f"vector {v} not in D basis {D_basis}")


def dlocal_constraints(D_basis: Tuple[int, ...]) -> List[dict]:
    d = len(D_basis)
    cons = []
    for E_basis_coord in subspace_bases_coord(d):
        if not E_basis_coord:
            continue
        E_rows = [xor_combo(D_basis, a) for a in E_basis_coord]
        w = cuts.wang_L_for_dual_span(E_rows)
        active_pats = []
        for pat in range(1 << d):
            active = any(base.dot8(e, pat) for e in E_basis_coord)
            if active:
                active_pats.append(pat)
        cons.append({
            "E_basis_coord": list(E_basis_coord),
            "E_rows": E_rows,
            "dimE": len(E_basis_coord),
            "L": int(w["L_D"]),
            "active_patterns": active_pats,
        })
    return cons


def coeffs_on_patterns(D_basis: Tuple[int, ...], mu: int, lam: int, nu: int) -> List[int]:
    d = len(D_basis)
    mu_c = coords_of_in_D(D_basis, mu)
    lam_c = coords_of_in_D(D_basis, lam)
    nu_c = coords_of_in_D(D_basis, nu)
    coeff = []
    for pat in range(1 << d):
        q = base.dot8(mu_c, pat)
        if q:
            c = 1
        else:
            c = base.dot8(lam_c, pat) + base.dot8(nu_c, pat)
        coeff.append(int(c))
    return coeff


def support_pattern_counts(D_basis: Tuple[int, ...], us: Sequence[int]) -> List[int]:
    d = len(D_basis)
    counts = [0] * (1 << d)
    for p in us:
        pat = 0
        for i, row in enumerate(D_basis):
            if base.dot8(row, int(p)):
                pat |= 1 << i
        counts[pat] += 1
    return counts


def minimize_over_dlocal_counts(D_basis: Tuple[int, ...], coeff: Sequence[int], total: int = 19) -> dict:
    caps = point_pattern_counts(D_basis)
    cons = dlocal_constraints(D_basis)
    d = len(D_basis)
    n_pat = 1 << d
    best_val = None
    best_y = None
    feasible_count = 0

    # Recursive enumeration of pattern count vectors. d<=3 in this application.
    y = [0] * n_pat
    suffix_caps = [0] * (n_pat + 1)
    for i in range(n_pat - 1, -1, -1):
        suffix_caps[i] = suffix_caps[i + 1] + caps[i]

    # Light pruning: for partial y, constraints with all active patterns assigned can be checked.
    active_sets = [set(c["active_patterns"]) for c in cons]

    def rec(i: int, remaining: int):
        nonlocal best_val, best_y, feasible_count
        if remaining < 0 or remaining > suffix_caps[i]:
            return
        if i == n_pat:
            if remaining != 0:
                return
            for con in cons:
                if sum(y[j] for j in con["active_patterns"]) < con["L"]:
                    return
            feasible_count += 1
            val = sum(int(coeff[j]) * y[j] for j in range(n_pat))
            if best_val is None or val < best_val:
                best_val = val
                best_y = list(y)
            return
        max_here = min(caps[i], remaining)
        for v in range(max_here + 1):
            y[i] = v
            # Prune constraints whose future maximum cannot reach L.
            ok = True
            for con, aset in zip(cons, active_sets):
                current = sum(y[j] for j in aset if j <= i)
                future_max = sum(caps[j] for j in aset if j > i)
                if current + min(future_max, remaining - v) < con["L"]:
                    ok = False
                    break
            if ok:
                rec(i + 1, remaining - v)
        y[i] = 0

    rec(0, total)
    return {
        "feasible_count_vectors": int(feasible_count),
        "min_lhs_dlocal_wang": None if best_val is None else int(best_val),
        "minimizer_pattern_counts": best_y,
        "pattern_capacities": list(caps),
        "constraints": cons,
    }


def analyze_cut(mu: int, lam: int, nu: int, support: Sequence[int] | None = None) -> dict:
    dB_tbl, dC_tbl = get_intersection_dims()
    cp = cuts.cut_params(mu, lam, nu, dB_tbl, dC_tbl)
    D_basis = tuple(base.gf2_rref([mu, lam, nu], n=8))
    coeff = coeffs_on_patterns(D_basis, mu, lam, nu)
    local = minimize_over_dlocal_counts(D_basis, coeff, total=19)
    support_info = None
    if support is not None:
        yc = support_pattern_counts(D_basis, support)
        support_info = {
            "pattern_counts": yc,
            "lhs": int(sum(coeff[i] * yc[i] for i in range(len(yc)))),
            "satisfies_dlocal_wang": all(sum(yc[j] for j in con["active_patterns"]) >= con["L"] for con in local["constraints"]),
        }
    return {
        "mu": int(mu), "lam_B": int(lam), "nu_C": int(nu),
        "D_basis": list(D_basis), "dimD": len(D_basis),
        "K": int(cp["K"]), "L_D": int(cp["single_wang"]["L_D"]),
        "single_wang_dominated": bool(cp["single_wang_dominated"]),
        "gap_K_minus_LD": int(cp["single_wang_gap_K_minus_L"]),
        "rank_tuple": [cp["rank_mu"], cp["rank_lam_B"], cp["rank_nu_C"]],
        "r_tuple": [cp["r_mu"], cp["r_lam_B"], cp["r_nu_C"]],
        "dB": cp["dB_lam_mu"], "dC": cp["dC_nu_mu"],
        "coeff_by_pattern": coeff,
        "dlocal": {
            "min_lhs": local["min_lhs_dlocal_wang"],
            "implied_by_D_local_Wang": (local["min_lhs_dlocal_wang"] is not None and local["min_lhs_dlocal_wang"] >= cp["K"]),
            "feasible_count_vectors": local["feasible_count_vectors"],
            "minimizer_pattern_counts": local["minimizer_pattern_counts"],
            "pattern_capacities": local["pattern_capacities"],
            "constraints_summary": [{"dimE": c["dimE"], "L": c["L"], "active_patterns": c["active_patterns"]} for c in local["constraints"]],
        },
        "support_info": support_info,
    }


def analyze_best() -> dict:
    known_file = OUTDIR / "known_best_pair_dominance.json"
    if not known_file.exists():
        # Build it if caller did not run the other script.
        result = cuts.diagnose_known()
        with known_file.open("w") as f:
            json.dump(result, f, indent=2, sort_keys=True)
    with known_file.open() as f:
        data = json.load(f)
    supports = {
        "L15": [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219],
        "analysis": [1,2,3,4,8,20,24,31,32,36,64,73,127,128,141,160,182,192,219],
    }
    out = {"schema": "s0908_Dlocal_implication_for_best_v1", "items": {}}
    for name, block in data["items"].items():
        arr = []
        for rec in block["best_pair_cuts"]:
            arr.append(analyze_cut(rec["mu"], rec["lam_B"], rec["nu_C"], supports[name]))
        out["items"][name] = arr
    return out


def analyze_known_violations(max_each: int = 0) -> dict:
    # Recompute all violated cuts for L15/analysis, deduplicate triples, and run D-local tests.
    known = {
        "L15": [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219],
        "analysis": [1,2,3,4,8,20,24,31,32,36,64,73,127,128,141,160,182,192,219],
    }
    dB_tbl, dC_tbl = get_intersection_dims()
    result = {"schema": "s0908_Dlocal_implication_for_all_known_violations_v1", "items": {}}
    for name, us in known.items():
        weights = base.support_weights(us)
        recs = []
        counts = collections.Counter()
        seen = set()
        for mu in cuts.TARGETS_12:
            sp_mu = base.SPACES[mu]
            for lam in cuts.SOURCES_ALL:
                sp_lam = base.SPACES[lam]
                lhs_a = cuts.m_from_weights_zero(weights, lam) + cuts.m_from_weights_zero(weights, lam ^ mu)
                dB = int(dB_tbl[(lam, mu)])
                for nu in cuts.SOURCES_ALL:
                    sp_nu = base.SPACES[nu]
                    lhs2 = lhs_a + cuts.m_from_weights_zero(weights, nu) + cuts.m_from_weights_zero(weights, nu ^ mu)
                    K = int(sp_mu.r + sp_lam.r + sp_nu.r - dB - int(dC_tbl[(nu, mu)]))
                    if lhs2 >= 2 * K:
                        continue
                    key = (mu, lam, nu)
                    if key in seen:
                        continue
                    seen.add(key)
                    a = analyze_cut(mu, lam, nu, us)
                    local_imp = a["dlocal"]["implied_by_D_local_Wang"]
                    single = a["single_wang_dominated"]
                    counts[("violated", "single" if single else "not_single", "Dlocal" if local_imp else "not_Dlocal")] += 1
                    counts[("gap", a["gap_K_minus_LD"], "Dlocal" if local_imp else "not_Dlocal")] += 1
                    if max_each == 0 or len(recs) < max_each:
                        recs.append(a)
        result["items"][name] = {
            "support_size": len(us),
            "violated_cut_count": len(seen),
            "classification": {str(k): int(v) for k, v in sorted(counts.items(), key=lambda kv: str(kv[0]))},
            "records_head": recs,
        }
    return result


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("best")
    p.add_argument("--out", default=str(OUTDIR / "dlocal_implication_best_pairs.json"))
    p = sub.add_parser("known-violations")
    p.add_argument("--max-each", type=int, default=20)
    p.add_argument("--out", default=str(OUTDIR / "dlocal_implication_known_violations.json"))
    args = ap.parse_args()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    if args.cmd == "best":
        result = analyze_best()
    elif args.cmd == "known-violations":
        result = analyze_known_violations(max_each=args.max_each)
    else:
        raise ValueError(args.cmd)
    result["elapsed_sec"] = round(time.time() - t0, 3)
    with Path(args.out).open("w") as f:
        json.dump(result, f, indent=2, sort_keys=True)
    compact = json.loads(json.dumps(result))
    # Shorten verbose D-local constraints in stdout.
    for block in compact.get("items", {}).values():
        arr = block if isinstance(block, list) else block.get("records_head", [])
        for rec in arr:
            if "dlocal" in rec:
                rec["dlocal"].pop("constraints_summary", None)
    print(json.dumps(compact, indent=2, sort_keys=True)[:12000])


if __name__ == "__main__":
    main()
