#!/usr/bin/env python3
"""
analysis: six-parameter LU chart for the Z4-stable ten-cube residual equations.

The residual C_M is invariant under right multiplication of M by a diagonal
matrix of determinant 1, because each product of the three recombined columns is
scaled by det(D)=1.  On an open cell of SL3 modulo this diagonal torus we use
M = U(u12,u13,u23) L(l21,l31,l32), with U and L unitriangular.  This removes the
determinant penalty and the two residual-invariant internal torus directions from
least-squares candidate search.

This is a candidate finder only, not an exclusion proof.
"""
from __future__ import annotations

import argparse, itertools, json, sys
from pathlib import Path
import numpy as np
from scipy.optimize import least_squares

WS = Path(__file__).resolve().parent.parent
OUT = WS / "data" / "z4_rank10_search"
OUT.mkdir(parents=True, exist_ok=True)
sys.path.insert(0, str(WS / "scripts"))
import z4_symmetry_kernel_residual as s42  # noqa: E402
import z4_rank10_orbit_numeric_search as base  # noqa: E402

MONOS = s42.MONOS


def M_from_lu(z):
    u12, u13, u23, l21, l31, l32 = z
    U = np.array([[1.0, u12, u13], [0.0, 1.0, u23], [0.0, 0.0, 1.0]])
    L = np.array([[1.0, 0.0, 0.0], [l21, 1.0, 0.0], [l31, l32, 1.0]])
    return U @ L


def pack(z, coords):
    return np.concatenate([np.asarray(z, dtype=float).reshape(6)] + [np.asarray(c, dtype=float).reshape(-1) for c in coords])


def unpack(x, pattern, bases):
    z = np.asarray(x[:6], dtype=float)
    pos = 6
    forms = []
    for part in pattern:
        d = bases[part].shape[1]
        c = np.asarray(x[pos:pos+d], dtype=float)
        pos += d
        forms.append(np.asarray(bases[part], dtype=float) @ c)
    return z, forms


def objective_factory(pattern, bases, Ad_pows, T0, tr_vec):
    def obj(x):
        z, forms = unpack(x, pattern, bases)
        M = M_from_lu(z)
        Tcols = np.asarray(T0, dtype=float) @ M
        residual = tr_vec - base.free_orbit_diag_float(Tcols, Ad_pows)
        cube_sum = np.zeros_like(residual)
        for part, l in zip(pattern, forms):
            cube_sum += base.orbit_cube_float(l, Ad_pows, part)
        return residual - cube_sum
    return obj


def setup():
    a0, powers, Ad, Ad_pows_obj, S4 = s42.build_a0_ad_s4()
    I9 = np.eye(9, dtype=object)
    bases = {
        1: np.asarray(s42.nullspace_int(Ad - I9), dtype=float),
        2: np.asarray(s42.nullspace_int(Ad @ Ad - I9), dtype=float),
        4: np.asarray(I9, dtype=float),
    }
    Ad_pows = [np.asarray(A, dtype=float) for A in Ad_pows_obj]
    scheme = json.loads((WS / "data" / "ballard_z4_cyclic" / "ballard_z4_cyclic_scheme.json").read_text())
    U0 = np.array(scheme["free_orbit_representatives"][0]["U"], dtype=float).reshape(9)
    V0 = np.array(scheme["free_orbit_representatives"][0]["V"], dtype=float).reshape(9)
    W0 = np.array(scheme["free_orbit_representatives"][0]["W"], dtype=float).reshape(9)
    T0 = np.stack([U0, V0, W0], axis=1)
    return bases, Ad_pows, T0, base.target_trM3_float()


def bilr_initial(pattern, bases, Ad_pows, rng):
    reps = base.get_orbit_reps_from_bilr([np.asarray(A, dtype=object) for A in Ad_pows])
    by_len = {}
    for r in reps:
        by_len.setdefault(r["length"], []).append(r["rep"])
    coords = []
    for part in pattern:
        if by_len.get(part):
            rep = by_len[part].pop(0)
            coords.append(base.basis_coords(rep, bases[part]))
        else:
            coords.append(0.3 * rng.standard_normal(bases[part].shape[1]))
    return pack(np.zeros(6), coords)


def random_initial(pattern, bases, rng, scale):
    z = scale * rng.standard_normal(6)
    coords = [scale * rng.standard_normal(bases[part].shape[1]) for part in pattern]
    return pack(z, coords)


def run(pattern, starts, max_nfev, seed, scale):
    bases, Ad_pows, T0, tr_vec = setup()
    obj = objective_factory(pattern, bases, Ad_pows, T0, tr_vec)
    rng = np.random.default_rng(seed)
    initials = [("bilr_drop_or_fill", bilr_initial(pattern, bases, Ad_pows, rng))]
    for i in range(max(0, starts - 1)):
        initials.append((f"random_{i}", random_initial(pattern, bases, rng, scale)))
    records=[]; best=None
    for si,(label,x0) in enumerate(initials):
        r0=obj(x0)
        res=least_squares(obj, x0, method="trf", x_scale="jac", ftol=1e-12, xtol=1e-12, gtol=1e-12,
                          max_nfev=max_nfev, verbose=0)
        r=obj(res.x)
        rec={
            "start":si,"label":label,
            "initial_norm":float(np.linalg.norm(r0)),"initial_max_abs":float(np.max(np.abs(r0))),
            "final_norm":float(np.linalg.norm(r)),"final_max_abs":float(np.max(np.abs(r))),
            "cost":float(res.cost),"optimality":float(res.optimality),"nfev":int(res.nfev),
            "status":int(res.status),"message":str(res.message),
            "M_det":float(np.linalg.det(M_from_lu(res.x[:6]))),"z_norm":float(np.linalg.norm(res.x[:6])),
            "x_norm":float(np.linalg.norm(res.x)),
        }
        records.append(rec)
        if best is None or rec["final_norm"] < best["final_norm"]:
            best=rec
        print(f"LU pattern {pattern} start {si} {label}: {rec['initial_norm']:.3e}/{rec['initial_max_abs']:.3e} -> {rec['final_norm']:.3e}/{rec['final_max_abs']:.3e}, nfev={rec['nfev']}, opt={rec['optimality']:.2e}", flush=True)
    return {"pattern":list(pattern),"variable_count":int(6+sum(bases[p].shape[1] for p in pattern)),"records":records,"best":best}


def positive_control():
    bases, Ad_pows, T0, tr_vec = setup()
    pattern=(4,4,2,1)
    obj=objective_factory(pattern,bases,Ad_pows,T0,tr_vec)
    x=bilr_initial(pattern,bases,Ad_pows,np.random.default_rng(1))
    r=obj(x)
    return {"pattern":list(pattern),"max_abs":float(np.max(np.abs(r))),"norm":float(np.linalg.norm(r)),"passes_1e_9":bool(np.max(np.abs(r))<1e-9)}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--patterns",default="4,4,2;4,4,1,1;4,2,2,1,1")
    ap.add_argument("--starts",type=int,default=4)
    ap.add_argument("--max-nfev",type=int,default=2500)
    ap.add_argument("--seed",type=int,default=42520)
    ap.add_argument("--scale",type=float,default=0.8)
    args=ap.parse_args()
    pc=positive_control(); print("positive control",pc,flush=True)
    pats=[]
    for raw in args.patterns.split(';'):
        raw=raw.strip()
        if raw: pats.append(tuple(int(x) for x in raw.split(',') if x.strip()))
    results=[]
    for i,pat in enumerate(pats):
        results.append(run(pat,args.starts,args.max_nfev,args.seed+100*i,args.scale))
    overall=min((r["best"]|{"pattern":r["pattern"]} for r in results), key=lambda x:x["final_norm"])
    summary={"positive_control":pc,"settings":vars(args),"results":results,"overall_best":overall,
             "interpretation":"six-parameter LU chart numerical candidate search only; nonzero residuals are not lower-bound evidence"}
    out=OUT/'z4_rank10_orbit_numeric_search_lu.json'
    out.write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({"out":str(out),"overall_best":overall},indent=2),flush=True)

if __name__=='__main__':
    main()
