#!/usr/bin/env python3
"""analysis: add extra moving free orbits to Laderman's anti-feasible core.

This is the second exact finite-field Z(F) functional after the Laderman anti-span
basis-change search.  Keep the transported Laderman eight free orbits, which already
force L_anti <= F, then add k=1,2,3 genuinely new free orbits.  This probes the
rank-22 skeletons

    m=9, f=4;  m=10, f=2;  m=11, f=0

because a hit is possible only if qdim(F) = dim(F+L1)-dim(F) <= f = 22-2m
and the tau-fixed rank-one variety Z(F) spans that quotient.  If this happens,
the script recovers A-factor coefficients and replays all 729 tensor coordinates.

The search is scoped: it tests an exact F_p family containing the Laderman anti core;
it is not a global exclusion for moving all free orbits.
"""
from __future__ import annotations
import argparse, json, random, time, importlib.util
from pathlib import Path
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "zF_search"
OUT.mkdir(parents=True, exist_ok=True)

# Import the core Z(F) utilities from the companion script.
spec = importlib.util.spec_from_file_location("zcore", SCRIPT_DIR / "zF_laderman_anti_span_search.py")
z = importlib.util.module_from_spec(spec)
spec.loader.exec_module(z)

def canonical_projective(v, p):
    v = np.asarray(v, dtype=np.int64) % p
    if not np.any(v):
        return None
    first = int(np.nonzero(v)[0][0])
    return (v * z.inv(v[first], p)) % p

def random_projective(rng, p):
    while True:
        v = np.array([rng.randrange(p) for _ in range(9)], dtype=np.int64)
        c = canonical_projective(v, p)
        if c is not None:
            return c

def random_pair(rng, p):
    while True:
        v = random_projective(rng, p)
        w = random_projective(rng, p)
        if z.rank(np.vstack([v, w]) % p, p) == 2:
            return v, w

def build_free_gens_from_pairs(p, pairs):
    gens = []
    for v, w in pairs:
        gens.extend(z.free_slots_from_pair(v, w, p))
    return np.vstack(gens) % p

def light_dims(p, pairs, L1):
    F = build_free_gens_from_pairs(p, pairs)
    F_basis, _ = z.row_basis(F, p)
    rankF = F_basis.shape[0]
    rankS = z.rank(np.vstack([F_basis, L1]) % p, p)
    Fcap = rankF + z.rank(L1, p) - rankS
    qdim = rankS - rankF
    return rankF, rankS, Fcap, qdim

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--p', type=int, default=3)
    ap.add_argument('--samples', type=int, default=5000)
    ap.add_argument('--seed', type=int, default=6802)
    ap.add_argument('--k-list', default='1,2,3')
    ap.add_argument('--time-budget', type=float, default=600.0)
    args = ap.parse_args()
    p = args.p
    rng = random.Random(args.seed)
    t0 = time.time()
    k_list = [int(x) for x in args.k_list.split(',') if x]

    L1 = z.build_L1(p)
    Lsym, Lanti81 = z.build_Lsym_Lanti_81(p)
    Xproj, Sq = z.precompute_fixed_squares(p)
    lad_pairs, lad_terms, delta, R = z.laderman_free_pairs_vectors(p)
    lad_control = z.analyze_configuration(p, lad_pairs, Xproj, Sq, L1, Lsym, Lanti81, f_allowed=6, want_replay=False)

    out = {
        "field": f"F_{p}",
        "seed": args.seed,
        "samples_requested_per_k": args.samples,
        "time_budget_sec": args.time_budget,
        "scaled_transport_delta": int(delta),
        "scaled_transport_R_columns": R.astype(int).tolist(),
        "projective_fixed_vectors_count": int(Xproj.shape[0]),
        "laderman_core_control": lad_control,
        "k_results": {},
        "hits": [],
        "interpretation": (
            "Laderman eight free orbits are kept as an anti-feasible core; k extra arbitrary free orbits are sampled. "
            "For m=8+k, rank<=22 requires qdim(F)<=22-2m and then Z(F) must span qdim. "
            "A hit is replayed exactly; absence of a hit is only a sampled result in this anchored family."
        ),
    }

    for k in k_list:
        m = 8 + k
        f_allowed = 22 - 2*m
        if f_allowed < 0:
            continue
        summary = {
            "k_extra_orbits": k,
            "m": m,
            "f_allowed": f_allowed,
            "samples_done": 0,
            "rankF_hist": {},
            "F_cap_L1_hist": {},
            "qdim_hist": {},
            "candidate_qdim_le_f_count": 0,
            "full_Z_tests": 0,
            "Z_count_hist": {},
            "Z_qrank_hist": {},
            "hit_count": 0,
            "best_by_Fcap": [],
        }
        best = []
        for s in range(args.samples):
            if time.time() - t0 > args.time_budget:
                summary["timed_out"] = True
                break
            extras = [random_pair(rng, p) for _ in range(k)]
            pairs = list(lad_pairs) + extras
            rankF, rankS, Fcap, qdim = light_dims(p, pairs, L1)
            summary["samples_done"] += 1
            for name, val in [("rankF_hist", rankF), ("F_cap_L1_hist", Fcap), ("qdim_hist", qdim)]:
                key = str(int(val)); summary[name][key] = summary[name].get(key, 0) + 1
            rec = None
            if qdim <= f_allowed:
                summary["candidate_qdim_le_f_count"] += 1
                rec = z.analyze_configuration(p, pairs, Xproj, Sq, L1, Lsym, Lanti81, f_allowed=f_allowed, want_replay=False)
                summary["full_Z_tests"] += 1
                zc = rec["Z_fixed_squares_count_over_Fp"]
                zr = rec["Z_quotient_rank"]
                summary["Z_count_hist"][str(zc)] = summary["Z_count_hist"].get(str(zc), 0) + 1
                summary["Z_qrank_hist"][str(zr)] = summary["Z_qrank_hist"].get(str(zr), 0) + 1
                if rec["rank22_condition_met_by_Z"]:
                    rec2 = z.analyze_configuration(p, pairs, Xproj, Sq, L1, Lsym, Lanti81, f_allowed=f_allowed, want_replay=True)
                    hit = {
                        "k": k,
                        "m": m,
                        "sample": s,
                        "record": rec2,
                        "extra_pairs": [
                            {"v": [int(x) for x in v.tolist()], "w": [int(x) for x in w.tolist()]}
                            for v, w in extras
                        ],
                    }
                    summary["hit_count"] += 1
                    out["hits"].append(hit)
                    if rec2["replay"] and rec2["replay"].get("full_T333_replay"):
                        summary["best_by_Fcap"] = best
                        out["k_results"][str(k)] = summary
                        path = OUT / f"laderman_plus_extra_ZF_F{p}.json"
                        path.write_text(json.dumps(out, indent=2) + "\n")
                        print(json.dumps(out, indent=2))
                        print(f"SAVED {path}")
                        return
            score = (Fcap, -qdim, 0 if rec is None else rec.get("Z_quotient_rank", 0), 0 if rec is None else rec.get("Z_fixed_squares_count_over_Fp", 0))
            compact = {
                "score": [int(score[0]), int(score[1]), int(score[2]), int(score[3])],
                "sample": int(s),
                "rankF": int(rankF),
                "rankF_plus_L1": int(rankS),
                "F_cap_L1_dim": int(Fcap),
                "qdim": int(qdim),
                "extra_pairs": [
                    {"v": [int(x) for x in v.tolist()], "w": [int(x) for x in w.tolist()]}
                    for v, w in extras
                ],
            }
            if rec is not None:
                compact["Z_fixed_squares_count_over_Fp"] = int(rec["Z_fixed_squares_count_over_Fp"])
                compact["Z_quotient_rank"] = int(rec["Z_quotient_rank"])
                compact["rank22_condition_met_by_Z"] = bool(rec["rank22_condition_met_by_Z"])
            best.append(compact)
            best = sorted(best, key=lambda x: tuple(x["score"]), reverse=True)[:12]
        summary["best_by_Fcap"] = best
        out["k_results"][str(k)] = summary

    path = OUT / f"laderman_plus_extra_ZF_F{p}.json"
    path.write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))
    print(f"SAVED {path}")

if __name__ == '__main__':
    main()
