#!/usr/bin/env python3
"""
analysis: numerical candidate search for Z4-stable ten-cube residual systems.

This is a candidate-finding instrument, not an exclusion proof.  It uses the
corrected characteristic-zero single-free-Z4-orbit model:

  C_M = tr(X^3) - 3 sum_{k=0}^3 (Ad(a0)^k A_M)(Ad(a0)^k B_M)(Ad(a0)^k C_M),
  (A_M,B_M,C_M) = (A0,B0,C0) M, det(M)=1.

It then tries to solve C_M = sum of ten Z4-stable cubes for orbit patterns such
as 4+4+2, 4+4+1+1, and 4+2+2+1+1.  A zero solution would be an exact rank-22
candidate to rationalize and verify; failure to find one is only heuristic.
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import least_squares

WS = Path(__file__).resolve().parent.parent
OUT = WS / "data" / "z4_rank10_search"
OUT.mkdir(parents=True, exist_ok=True)
sys.path.insert(0, str(WS / "scripts"))
import z4_symmetry_kernel_residual as s42  # noqa: E402
import ballard_z4_cyclic_scheme as bilr  # noqa: E402

N = 9
MONOS = s42.MONOS
PERMS = s42.PERMS


def vec_to_coeff_float(u, v, w):
    u = np.asarray(u, dtype=float).reshape(9)
    v = np.asarray(v, dtype=float).reshape(9)
    w = np.asarray(w, dtype=float).reshape(9)
    out = np.zeros(len(MONOS), dtype=float)
    for mi, mono in enumerate(MONOS):
        total = 0.0
        for perm in PERMS[mono]:
            total += u[perm[0]] * v[perm[1]] * w[perm[2]]
        out[mi] = total
    return out


def cube_coeff_float(l):
    return vec_to_coeff_float(l, l, l)


def orbit_cube_float(l, Ad_pows, part):
    out = np.zeros(len(MONOS), dtype=float)
    for k in range(part):
        out += cube_coeff_float(Ad_pows[k].astype(float) @ l)
    return out


def target_trM3_float():
    out = np.zeros(len(MONOS), dtype=float)
    idx = {m: i for i, m in enumerate(MONOS)}
    for a, b, c in itertools.product(range(3), repeat=3):
        out[idx[tuple(sorted([3*a+b, 3*b+c, 3*c+a]))]] += 1.0
    return out


def free_orbit_diag_float(Tcols, Ad_pows):
    A, B, C = Tcols[:, 0], Tcols[:, 1], Tcols[:, 2]
    out = np.zeros(len(MONOS), dtype=float)
    for k in range(4):
        out += 3.0 * vec_to_coeff_float(Ad_pows[k].astype(float) @ A,
                                        Ad_pows[k].astype(float) @ B,
                                        Ad_pows[k].astype(float) @ C)
    return out


def det3_float(M):
    return float(np.linalg.det(np.asarray(M, dtype=float).reshape(3, 3)))


def get_orbit_reps_from_bilr(Ad_pows):
    terms, cubes, free, _, _ = bilr.build_scheme()
    cube_vecs = [np.array(bilr.flatten(C), dtype=float) for C in cubes]
    keys = {tuple(int(x) for x in v.astype(int)): i for i, v in enumerate(cube_vecs)}
    seen = set()
    reps = []
    for i, v in enumerate(cube_vecs):
        key = tuple(int(x) for x in v.astype(int))
        if key in seen:
            continue
        orbit = []
        for k in range(4):
            vk = Ad_pows[k].astype(object) @ np.array(v.astype(int), dtype=object)
            orbit.append(tuple(int(x) for x in vk))
        uniq = []
        for o in orbit:
            if o not in uniq:
                uniq.append(o)
        for o in uniq:
            seen.add(o)
        reps.append({"length": len(uniq), "rep": np.array(uniq[0], dtype=float), "orbit_keys": uniq})
    reps.sort(key=lambda r: (-r["length"], tuple(r["rep"].astype(int).tolist())))
    return reps


def basis_coords(v, B):
    Bf = np.asarray(B, dtype=float)
    c, *_ = np.linalg.lstsq(Bf, np.asarray(v, dtype=float), rcond=None)
    if np.linalg.norm(Bf @ c - np.asarray(v, dtype=float)) > 1e-8:
        raise ValueError("representative not in requested fixed space")
    return c


def pack_x(M, coords):
    return np.concatenate([np.asarray(M, dtype=float).reshape(9)] + [np.asarray(c, dtype=float).reshape(-1) for c in coords])


def unpack_x(x, pattern, bases):
    M = np.asarray(x[:9], dtype=float).reshape(3, 3)
    pos = 9
    forms = []
    for part in pattern:
        d = bases[part].shape[1]
        c = np.asarray(x[pos:pos+d], dtype=float)
        pos += d
        forms.append(np.asarray(bases[part], dtype=float) @ c)
    return M, forms


def objective_factory(pattern, bases, Ad_pows, T0, tr_vec, coeff_weight=1.0, det_weight=1.0):
    def obj(x):
        M, forms = unpack_x(x, pattern, bases)
        Tcols = np.asarray(T0, dtype=float) @ M
        residual = tr_vec - free_orbit_diag_float(Tcols, Ad_pows)
        cube_sum = np.zeros_like(residual)
        for part, l in zip(pattern, forms):
            cube_sum += orbit_cube_float(l, Ad_pows, part)
        diff = coeff_weight * (residual - cube_sum)
        det_res = det_weight * (det3_float(M) - 1.0)
        return np.concatenate([diff, [det_res]])
    return obj


def x_from_bilr_reps(pattern, reps_by_len, bases, rng, random_scale=0.4):
    M = np.eye(3)
    coords = []
    available = {k: [r["rep"] for r in v] for k, v in reps_by_len.items()}
    for part in pattern:
        if available.get(part):
            rep = available[part].pop(0)
            coords.append(basis_coords(rep, bases[part]))
        else:
            coords.append(random_scale * rng.standard_normal(bases[part].shape[1]))
    return pack_x(M, coords)


def random_x(pattern, bases, rng, scale=0.8):
    # Random near-SL3 matrix: start at identity plus traceless-ish perturbation, then rescale determinant if real positive.
    M = np.eye(3) + scale * rng.standard_normal((3, 3))
    d = np.linalg.det(M)
    if abs(d) > 1e-8:
        M = M / np.cbrt(d)
    coords = [scale * rng.standard_normal(bases[part].shape[1]) for part in pattern]
    return pack_x(M, coords)


def run_pattern(pattern, starts, max_nfev, seed):
    a0, powers, Ad, Ad_pows, S4 = s42.build_a0_ad_s4()
    I9 = np.eye(9, dtype=object)
    V1 = s42.nullspace_int(Ad - I9)
    V2 = s42.nullspace_int(Ad @ Ad - I9)
    V4 = I9
    bases = {1: np.asarray(V1, dtype=float), 2: np.asarray(V2, dtype=float), 4: np.asarray(V4, dtype=float)}

    scheme = json.loads((WS / "data" / "ballard_z4_cyclic" / "ballard_z4_cyclic_scheme.json").read_text())
    U0 = np.array(scheme["free_orbit_representatives"][0]["U"], dtype=float).reshape(9)
    V0 = np.array(scheme["free_orbit_representatives"][0]["V"], dtype=float).reshape(9)
    W0 = np.array(scheme["free_orbit_representatives"][0]["W"], dtype=float).reshape(9)
    T0 = np.stack([U0, V0, W0], axis=1)
    tr_vec = target_trM3_float()
    obj = objective_factory(pattern, bases, [np.asarray(A, dtype=float) for A in Ad_pows], T0, tr_vec)
    rng = np.random.default_rng(seed)

    reps = get_orbit_reps_from_bilr(Ad_pows)
    reps_by_len = {}
    for r in reps:
        reps_by_len.setdefault(r["length"], []).append(r)

    init_list = []
    init_list.append(("bilr_drop_or_random_fill", x_from_bilr_reps(pattern, {k: list(v) for k, v in reps_by_len.items()}, bases, rng)))
    for i in range(max(0, starts - 1)):
        init_list.append((f"random_{i}", random_x(pattern, bases, rng, scale=0.7)))

    records = []
    best = None
    for si, (label, x0) in enumerate(init_list):
        r0 = obj(x0)
        n0 = float(np.linalg.norm(r0))
        max0 = float(np.max(np.abs(r0)))
        res = least_squares(obj, x0, method="trf", x_scale="jac", ftol=1e-12, xtol=1e-12, gtol=1e-12,
                            max_nfev=max_nfev, verbose=0)
        r = obj(res.x)
        rec = {
            "start": si,
            "label": label,
            "initial_norm": n0,
            "initial_max_abs": max0,
            "final_norm": float(np.linalg.norm(r)),
            "final_max_abs": float(np.max(np.abs(r))),
            "cost": float(res.cost),
            "optimality": float(res.optimality),
            "nfev": int(res.nfev),
            "status": int(res.status),
            "message": str(res.message),
            "detM": det3_float(res.x[:9]),
            "x_norm": float(np.linalg.norm(res.x)),
        }
        records.append(rec)
        if best is None or rec["final_norm"] < best["final_norm"]:
            best = rec
        print(f"pattern {pattern} start {si} {label}: initial {n0:.3e}/{max0:.3e} -> final {rec['final_norm']:.3e}/{rec['final_max_abs']:.3e}, nfev={rec['nfev']}, status={rec['status']}", flush=True)

    return {
        "pattern": list(pattern),
        "variable_count": int(9 + sum(bases[p].shape[1] for p in pattern)),
        "equation_count_including_det": int(len(MONOS) + 1),
        "starts": int(len(init_list)),
        "records": records,
        "best": best,
        "scope": "numerical candidate search only; nonzero residual does not prove nonexistence",
    }


def positive_control():
    a0, powers, Ad, Ad_pows, S4 = s42.build_a0_ad_s4()
    I9 = np.eye(9, dtype=object)
    bases = {1: np.asarray(s42.nullspace_int(Ad - I9), dtype=float),
             2: np.asarray(s42.nullspace_int(Ad @ Ad - I9), dtype=float),
             4: np.asarray(I9, dtype=float)}
    pattern = (4, 4, 2, 1)
    scheme = json.loads((WS / "data" / "ballard_z4_cyclic" / "ballard_z4_cyclic_scheme.json").read_text())
    U0 = np.array(scheme["free_orbit_representatives"][0]["U"], dtype=float).reshape(9)
    V0 = np.array(scheme["free_orbit_representatives"][0]["V"], dtype=float).reshape(9)
    W0 = np.array(scheme["free_orbit_representatives"][0]["W"], dtype=float).reshape(9)
    T0 = np.stack([U0, V0, W0], axis=1)
    tr_vec = target_trM3_float()
    obj = objective_factory(pattern, bases, [np.asarray(A, dtype=float) for A in Ad_pows], T0, tr_vec)
    reps = get_orbit_reps_from_bilr(Ad_pows)
    reps_by_len = {}
    for r in reps:
        reps_by_len.setdefault(r["length"], []).append(r)
    x = x_from_bilr_reps(pattern, {k: list(v) for k, v in reps_by_len.items()}, bases, np.random.default_rng(1), random_scale=0.0)
    r = obj(x)
    return {
        "pattern": list(pattern),
        "orbit_lengths_found_in_BILR_cubes": [int(rp["length"]) for rp in reps],
        "norm": float(np.linalg.norm(r)),
        "max_abs": float(np.max(np.abs(r))),
        "passes_zero_tolerance_1e_9": bool(np.max(np.abs(r)) < 1e-9),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--patterns", default="4,4,2;4,4,1,1;4,2,2,1,1")
    ap.add_argument("--starts", type=int, default=6)
    ap.add_argument("--max-nfev", type=int, default=3000)
    ap.add_argument("--seed", type=int, default=4242)
    args = ap.parse_args()
    pc = positive_control()
    print("positive control", pc, flush=True)
    pats = []
    for raw in args.patterns.split(";"):
        raw = raw.strip()
        if raw:
            pats.append(tuple(int(x) for x in raw.split(",") if x.strip()))
    results = []
    for pi, pat in enumerate(pats):
        results.append(run_pattern(pat, args.starts, args.max_nfev, args.seed + 100*pi))
    summary = {
        "positive_control": pc,
        "search_settings": vars(args),
        "results": results,
        "overall_best": min((r["best"] | {"pattern": r["pattern"]} for r in results), key=lambda x: x["final_norm"]),
        "interpretation": "A zero or rationalizable near-zero solution would be a rank-22 candidate in the stated Z4-stable residual model. No finite nonzero search residual is a proof of nonexistence.",
    }
    out = OUT / "z4_rank10_orbit_numeric_search.json"
    out.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"out": str(out), "positive_control_max_abs": pc["max_abs"], "overall_best": summary["overall_best"]}, indent=2), flush=True)


if __name__ == "__main__":
    main()
