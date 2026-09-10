#!/usr/bin/env python3
"""
analysis: BILR tail positive control for the canonical Q-basis block instrument.

The off blocks qz^2, qw^2, pzw determine a size-4 orbit only up to the
non-homogeneous rescaling
    z,w -> t z,t w,   p,q -> t^{-2} p,t^{-2} q.
This preserves the off blocks and multiplies the tail p^3+pq^2 by h=t^{-6}.
Therefore a correct positive control must solve tail equations with two hidden
scalars h1,h2; it must not subtract the unscaled recovered size-4 forms.

This script verifies that rule on the BILR residual over F_65521.  It recovers
the 32 sign/order variants from the generic branch, verifies that their off blocks
match, and checks that the known BILR length-2 plus fixed-p tail is recovered after
solving for h1,h2.  It also checks the 4+4+1+1 rank-22 tail necessity at the BILR
residual: pq^2 would have to vanish after subtracting the two size-4 tails, and
no variant admits such h1,h2.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path

import numpy as np

import z4_qbasis_selftest as qb
from z4_qbasis_generic_extractor import P, inv, pq2_indices, p3_indices, solve_linear_fullrank
import z4_tail_branch_analyzer as ta

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "z4_qbasis"
OUT.mkdir(parents=True, exist_ok=True)


def tail_indices():
    return p3_indices() + pq2_indices()


def solve_h_tail(C_tail, T1_tail, T2_tail, rhs_tail):
    # Solve C_tail - h1*T1_tail - h2*T2_tail = rhs_tail.
    A = np.stack([T1_tail, T2_tail], axis=1) % P
    b = (np.array(C_tail, dtype=object).reshape(-1) - np.array(rhs_tail, dtype=object).reshape(-1)) % P
    sol, rank = solve_linear_fullrank(A, b)
    if sol is None:
        return {"consistent": False, "rank": int(rank), "h": None}
    return {"consistent": True, "rank": int(rank), "h": [int(sol[0]) % P, int(sol[1]) % P], "unique": bool(rank == 2)}


def off_indices():
    out = []
    for mi, m in enumerate(qb.MONOS):
        groups = []
        for j in m:
            groups.append(next(g for g, idxs in qb.GROUPS.items() if j in idxs))
        if any(g in ("z", "w") for g in groups):
            out.append(mi)
    return out


def support_kind(l):
    l = np.array(l, dtype=object).reshape(qb.N) % P
    nz = {g: int(sum(1 for j in idxs if int(l[j]) % P)) for g, idxs in qb.GROUPS.items()}
    if nz["q"] == nz["z"] == nz["w"] == 0:
        kind = "p_only"
    elif nz["z"] == nz["w"] == 0:
        kind = "p_plus_q"
    else:
        kind = "general_size4"
    return kind, nz


def projective_ratios_by_group(actual, candidate):
    actual = np.array(actual, dtype=object).reshape(qb.N) % P
    candidate = np.array(candidate, dtype=object).reshape(qb.N) % P
    ratios = {}
    for g, idxs in qb.GROUPS.items():
        lam = None; ok = True
        for j in idxs:
            a = int(actual[j]) % P
            b = int(candidate[j]) % P
            if b:
                cur = a * inv(b) % P
                if lam is None:
                    lam = cur
                elif lam != cur:
                    ok = False
                    break
            elif a:
                ok = False
                break
        ratios[g] = int(lam) if ok and lam is not None else (0 if ok else None)
    return ratios


def main():
    a0, Q, Qi, mu, weights, diag_ok, ii = qb.q_basis(P)
    assert diag_ok
    scheme = json.loads((WS / "data" / "ballard_z4_cyclic" / "ballard_z4_cyclic_scheme.json").read_text())
    cubes_y = [qb.transform_stored_form_to_y(L, Q, Qi, P) for L in scheme["cubes"]]
    T0_y = np.stack([qb.transform_stored_form_to_y(scheme["free_orbit_representatives"][0][key], Q, Qi, P) for key in ["U", "V", "W"]], axis=1) % P
    C = (qb.target_vec_short(P) - qb.free_contribution(T0_y, weights, P)) % P
    cube_orbits, _ = qb.find_orbits(cubes_y, weights, P)
    clean_orbits = [[x for x in o if x is not None] for o in cube_orbits]
    clean_orbits.sort(key=lambda o: (len(o), o[0]))
    known_tail = np.zeros(len(qb.MONOS), dtype=object)
    actual_size4_reps = []
    orbit_records = []
    for orb in clean_orbits:
        rep = cubes_y[orb[0]]
        kind, nz = support_kind(rep)
        orbit_records.append({"orbit": [int(x) for x in orb], "length": len(orb), "kind": kind, "nonzero_counts": nz})
        if len(orb) == 4:
            actual_size4_reps.append((orb, rep))
        else:
            known_tail = (known_tail + qb.orbit_cube(rep, weights, P, len(orb))) % P

    variants = ta.extract_generic_variants(C, weights)
    t_idx = tail_indices(); pq_idx = pq2_indices(); off_idx = off_indices()
    C_tail = np.array([C[i] for i in t_idx], dtype=object) % P
    K_tail = np.array([known_tail[i] for i in t_idx], dtype=object) % P
    C_pq = np.array([C[i] for i in pq_idx], dtype=object) % P
    records = []
    for vi, var in enumerate(variants):
        l1 = var["l1"]; l2 = var["l2"]
        T1 = qb.orbit_cube(l1, weights, P, 4); T2 = qb.orbit_cube(l2, weights, P, 4)
        # Off blocks must match with no h-scaling.
        off_rem = (C - T1 - T2) % P
        off_nz = int(sum(1 for i in off_idx if int(off_rem[i]) % P))
        T1_tail = np.array([T1[i] for i in t_idx], dtype=object) % P
        T2_tail = np.array([T2[i] for i in t_idx], dtype=object) % P
        T1_pq = np.array([T1[i] for i in pq_idx], dtype=object) % P
        T2_pq = np.array([T2[i] for i in pq_idx], dtype=object) % P
        bilr_tail_h = solve_h_tail(C_tail, T1_tail, T2_tail, K_tail)
        # For 4+4+1+1, length-one fixed p-cubes have no pq^2 contribution, so pq^2 must vanish.
        h_4411 = solve_h_tail(C_pq, T1_pq, T2_pq, np.zeros(len(pq_idx), dtype=object))
        # Compare hidden scales to actual BILR size-4 orbits when possible.
        matches = []
        for name, l in [("l1", l1), ("l2", l2)]:
            for orb, rep in actual_size4_reps:
                ratios = projective_ratios_by_group(rep, l)
                compatible = (
                    ratios["p"] is not None and ratios["q"] is not None and ratios["z"] is not None and ratios["w"] is not None
                    and ratios["p"] == ratios["q"] and ratios["z"] == ratios["w"]
                    and (ratios["p"] * ratios["z"] * ratios["z"]) % P == 1
                )
                if compatible:
                    matches.append({"candidate": name, "actual_orbit": [int(x) for x in orb], "ratios_actual_over_candidate": ratios, "tail_h_alpha_cubed": int(pow(ratios["p"], 3, P))})
        records.append({
            "variant_index": vi,
            "order": [int(x) for x in var["order"]],
            "signs": [int(x) for x in var["signs"]],
            "off_block_nonzero_after_unscaled_size4_subtraction": off_nz,
            "bilr_known_tail_scale_solution": bilr_tail_h,
            "rank22_4411_pq_zero_solution": h_4411,
            "actual_size4_hidden_scale_matches": matches,
        })
    result = {
        "prime": P,
        "scope": "canonical Q-basis BILR positive control for branch-aware tail scaling; finite modular verification of identities in a good split prime",
        "orbit_records": orbit_records,
        "known_tail_nonzero_tail_coeffs": int(sum(1 for x in K_tail if int(x) % P)),
        "generic_variant_count": len(variants),
        "records": records,
        "aggregate": {
            "off_blocks_matched_for_all_variants": bool(all(r["off_block_nonzero_after_unscaled_size4_subtraction"] == 0 for r in records)),
            "known_bilr_tail_recovered_for_all_variants": bool(all(r["bilr_known_tail_scale_solution"]["consistent"] for r in records)),
            "rank22_4411_pq_zero_possible_variants": int(sum(1 for r in records if r["rank22_4411_pq_zero_solution"]["consistent"])),
            "variants_with_actual_hidden_scale_match": int(sum(1 for r in records if len(r["actual_size4_hidden_scale_matches"]) >= 2)),
        },
        "interpretation": "The BILR residual validates the hidden tail-scaling rule: qz/qw/pzw recover the two size-4 orbit directions only modulo two tail scalars h1,h2. The 4+4+1+1 rank-22 tail would force the pq^2 tail to vanish; at the BILR residual this linear necessary condition has no solution in any generic variant. This remains a positive-control/local residual calculation, not a characteristic-zero emptiness proof for the full six-parameter family.",
    }
    out = OUT / "tail_positive_control_bilr_v2.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"out": str(out), "aggregate": result["aggregate"], "sample_h": records[0]["bilr_known_tail_scale_solution"]}, indent=2))


if __name__ == "__main__":
    main()
