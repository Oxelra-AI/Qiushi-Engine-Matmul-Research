#!/usr/bin/env python3
"""
analysis: build an exact modular off-W projection system for the corrected
characteristic-zero Z4 single-free-orbit residual problem.

The purpose is to make the next algebraic computation concrete.  Over a good
prime p, construct:
  * a 43-dimensional basis of (Sym^3 V)^{Z4};
  * its 19-dimensional subspace H_W = (Sym^3 ker(g^2-I))^{Z4};
  * a 24 x 165 matrix pi_off whose kernel on invariant cubics is H_W;
  * the 24 off-W equations for
        C_M - Phi4(x) - Phi4(y) in H_W
    on one SL3/T chart M[0,0]=1, M[1,1]=1, det(M)=1.

The generated Singular file is a modular pilot for the concise patterns
4+4+2 and 4+4+1+1.  Modular unit ideal would be exploration only; a
characteristic-zero proof needs rational/number-field certificates and all
SL3/T charts.
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
from pathlib import Path

import numpy as np
import sympy as sp

WS = Path(__file__).resolve().parent.parent
OUT = WS / "data" / "z4_off_system"
OUT.mkdir(parents=True, exist_ok=True)
sys.path.insert(0, str(WS / "scripts"))
import z4_symmetry_kernel_residual as s42  # noqa: E402

N = 9
MONOS = s42.MONOS
PERMS = s42.PERMS
MONO_IDX = {m: i for i, m in enumerate(MONOS)}


def rank_mod(A, p):
    return s42.rank_mod(np.array(A, dtype=object), p)


def rref_mod(A, p):
    A = np.array(A, dtype=object)
    m, n = A.shape
    B = [[int(A[i, j]) % p for j in range(n)] for i in range(m)]
    pivots = []
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if B[i][c] % p:
                piv = i
                break
        if piv is None:
            continue
        B[r], B[piv] = B[piv], B[r]
        inv = pow(B[r][c] % p, -1, p)
        B[r] = [(x * inv) % p for x in B[r]]
        for i in range(m):
            if i != r and B[i][c] % p:
                f = B[i][c] % p
                B[i] = [(B[i][j] - f * B[r][j]) % p for j in range(n)]
        pivots.append(c)
        r += 1
        if r == m:
            break
    return np.array(B, dtype=np.int64), pivots


def independent_columns(M, target_rank, p):
    chosen = []
    cur = np.zeros((M.shape[0], 0), dtype=object)
    cur_rank = 0
    for j in range(M.shape[1]):
        test = np.concatenate([cur, M[:, j:j+1]], axis=1)
        rt = rank_mod(test, p)
        if rt > cur_rank:
            chosen.append(j)
            cur = test
            cur_rank = rt
            if cur_rank == target_rank:
                break
    return chosen, cur


def independent_rows(M, target_rank, p):
    chosen = []
    cur = np.zeros((0, M.shape[1]), dtype=object)
    cur_rank = 0
    for i in range(M.shape[0]):
        test = np.concatenate([cur, M[i:i+1, :]], axis=0)
        rt = rank_mod(test, p)
        if rt > cur_rank:
            chosen.append(i)
            cur = test
            cur_rank = rt
            if cur_rank == target_rank:
                break
    return chosen, cur


def inv_mod_square(A, p):
    A = np.array(A, dtype=object)
    n = A.shape[0]
    aug = np.concatenate([A, np.eye(n, dtype=object)], axis=1)
    R, piv = rref_mod(aug, p)
    if piv[:n] != list(range(n)):
        raise ValueError("matrix not invertible")
    return R[:, n:] % p


def kernel_mod_mat(A, p):
    K, rk = s42.kernel_mod(np.array(A, dtype=object), p)
    return np.array(K, dtype=np.int64) % p, rk


def cube_coeff_mod(l, p):
    l = [int(x) % p for x in np.array(l, dtype=object).reshape(9)]
    out = np.zeros(len(MONOS), dtype=np.int64)
    for mi, mono in enumerate(MONOS):
        s = 0
        for perm in PERMS[mono]:
            s = (s + l[perm[0]] * l[perm[1]] * l[perm[2]]) % p
        out[mi] = s
    return out


def orbit_cube_mod(l, Ad_pows, p, steps=4):
    out = np.zeros(len(MONOS), dtype=np.int64)
    for k in range(steps):
        out = (out + cube_coeff_mod(Ad_pows[k] @ l, p)) % p
    return out


def generate_orbit_span(Ad_pows, p, target, restrict_basis=None, seed=1):
    rng = np.random.default_rng(seed)
    cols = []
    # deterministic basis sums first
    if restrict_basis is None:
        B = np.eye(9, dtype=object)
    else:
        B = np.array(restrict_basis, dtype=object)
    basis_cols = [B[:, i] for i in range(B.shape[1])]
    candidates = []
    for r in range(1, min(4, len(basis_cols)) + 1):
        for comb in itertools.combinations(range(len(basis_cols)), r):
            v = np.zeros(9, dtype=object)
            for i in comb:
                v += basis_cols[i]
            candidates.append(v)
    for v in candidates:
        cols.append(orbit_cube_mod(v, Ad_pows, p, steps=4))
        M = np.stack(cols, axis=1)
        if rank_mod(M, p) >= target:
            chosen, cur = independent_columns(M, target, p)
            return cur % p, chosen
    # random fallback
    for _ in range(5000):
        if restrict_basis is None:
            v = rng.integers(0, p, size=9, dtype=np.int64).astype(object)
        else:
            coeff = rng.integers(0, p, size=B.shape[1], dtype=np.int64)
            v = np.zeros(9, dtype=object)
            for i, c in enumerate(coeff):
                v += int(c) * B[:, i]
        cols.append(orbit_cube_mod(v, Ad_pows, p, steps=4))
        M = np.stack(cols, axis=1)
        if rank_mod(M, p) >= target:
            chosen, cur = independent_columns(M, target, p)
            return cur % p, chosen
    raise RuntimeError(f"failed to generate rank {target} orbit span")


def off_projection_matrix(p):
    a0, powers, Ad, Ad_pows_obj, S4 = s42.build_a0_ad_s4()
    Ad_pows = [np.array(A, dtype=object) for A in Ad_pows_obj]
    B_inv, chosen_inv = generate_orbit_span(Ad_pows, p, target=43, restrict_basis=None, seed=42)
    V2 = s42.nullspace_int(Ad @ Ad - np.eye(9, dtype=object))  # W=ker(g^2-I), dim 5
    B_H, chosen_H = generate_orbit_span(Ad_pows, p, target=19, restrict_basis=V2, seed=43)

    row_ids, Brow = independent_rows(B_inv, 43, p)
    Binv_rows = inv_mod_square(Brow, p)  # 43x43; coords = Binv_rows * c[row_ids]
    Linv = np.zeros((43, 165), dtype=np.int64)
    for pos, rid in enumerate(row_ids):
        Linv[:, rid] = Binv_rows[:, pos]
    H_coords = (Linv @ B_H) % p
    Qcols, rkHT = kernel_mod_mat(H_coords.T, p)  # 43 x 24 columns
    Q = Qcols.T % p
    off = (Q @ Linv) % p
    return {
        "p": p,
        "Ad": Ad,
        "Ad_pows": Ad_pows,
        "B_inv": B_inv,
        "B_H": B_H,
        "row_ids": row_ids,
        "Linv": Linv,
        "H_coords": H_coords,
        "Q": Q,
        "off": off,
        "ranks": {
            "invariant_span": rank_mod(B_inv, p),
            "H_W_span": rank_mod(B_H, p),
            "H_coords": rank_mod(H_coords, p),
            "off_rows": rank_mod(off, p),
            "off_on_H_zero": int(np.count_nonzero((off @ B_H) % p)),
        },
    }


def sym_cube_coeff(l, variables, p):
    out = [sp.Integer(0) for _ in MONOS]
    for mi, mono in enumerate(MONOS):
        s = sp.Integer(0)
        for perm in PERMS[mono]:
            s += l[perm[0]] * l[perm[1]] * l[perm[2]]
        out[mi] = s
    return out


def sym_orbit_cube(l, Ad_pows, p):
    out = [sp.Integer(0) for _ in MONOS]
    for A in Ad_pows:
        lk = []
        for i in range(9):
            expr = sp.Integer(0)
            for j in range(9):
                a = int(A[i, j]) % p
                if a:
                    expr += a * l[j]
            lk.append(expr)
        cc = sym_cube_coeff(lk, None, p)
        out = [out[i] + cc[i] for i in range(len(MONOS))]
    return out


def sym_prod_coeff(u, v, w):
    out = [sp.Integer(0) for _ in MONOS]
    for mi, mono in enumerate(MONOS):
        s = sp.Integer(0)
        for perm in PERMS[mono]:
            s += u[perm[0]] * v[perm[1]] * w[perm[2]]
        out[mi] = s
    return out


def build_off_equations(proj, p, chart=(0, 1)):
    # chart=(r,s): M[r,0]=1 and M[s,1]=1.  Default BILR cell r=0,s=1.
    rfix, sfix = chart
    mvars = []
    M = [[None for _ in range(3)] for __ in range(3)]
    for r in range(3):
        for c in range(3):
            if (r, c) == (rfix, 0):
                M[r][c] = sp.Integer(1)
            elif (r, c) == (sfix, 1):
                M[r][c] = sp.Integer(1)
            else:
                name = f"m{r}{c}"
                var = sp.Symbol(name)
                M[r][c] = var
                mvars.append(var)
    xvars = [sp.Symbol(f"x{i}") for i in range(9)]
    yvars = [sp.Symbol(f"y{i}") for i in range(9)]
    variables = mvars + xvars + yvars

    scheme = json.loads((WS / "data" / "ballard_z4_cyclic" / "ballard_z4_cyclic_scheme.json").read_text())
    U0 = [sp.Integer(int(x)) for x in np.array(scheme["free_orbit_representatives"][0]["U"], dtype=object).reshape(9)]
    V0 = [sp.Integer(int(x)) for x in np.array(scheme["free_orbit_representatives"][0]["V"], dtype=object).reshape(9)]
    W0 = [sp.Integer(int(x)) for x in np.array(scheme["free_orbit_representatives"][0]["W"], dtype=object).reshape(9)]
    T0 = [U0, V0, W0]
    cols = []
    for c in range(3):
        vc = []
        for i in range(9):
            expr = sp.Integer(0)
            for j in range(3):
                expr += T0[j][i] * M[j][c]
            vc.append(expr)
        cols.append(vc)

    Ad_pows = proj["Ad_pows"]
    free_vec = [sp.Integer(0) for _ in MONOS]
    for A in Ad_pows:
        transformed = []
        for col in cols:
            tcol = []
            for i in range(9):
                expr = sp.Integer(0)
                for j in range(9):
                    a = int(A[i, j]) % p
                    if a:
                        expr += a * col[j]
                tcol.append(expr)
            transformed.append(tcol)
        pc = sym_prod_coeff(transformed[0], transformed[1], transformed[2])
        free_vec = [free_vec[i] + 3 * pc[i] for i in range(len(MONOS))]

    tr = [sp.Integer(int(x)) for x in s42.target_trM3_vec()]
    phix = sym_orbit_cube(xvars, Ad_pows, p)
    phiy = sym_orbit_cube(yvars, Ad_pows, p)
    coeff = [tr[i] - free_vec[i] - phix[i] - phiy[i] for i in range(len(MONOS))]
    off = proj["off"]
    eqs = []
    for row in range(off.shape[0]):
        expr = sp.Integer(0)
        nz = np.nonzero(off[row] % p)[0]
        for i in nz:
            expr += int(off[row, i]) * coeff[i]
        eqs.append(sp.Poly(sp.expand(expr), *variables, modulus=p).as_expr())

    det_expr = sp.Matrix(M).det() - 1
    det_poly = sp.Poly(sp.expand(det_expr), *variables, modulus=p).as_expr()
    return variables, eqs, det_poly


def singular_poly_str(expr, variables, p):
    poly = sp.Poly(expr, *variables, modulus=p)
    terms = []
    for monom, coeff in poly.terms():
        c = int(coeff) % p
        if c == 0:
            continue
        factors = []
        if c != 1 or all(e == 0 for e in monom):
            factors.append(str(c))
        for var, exp in zip(variables, monom):
            if exp == 0:
                continue
            if exp == 1:
                factors.append(str(var))
            else:
                factors.append(f"{var}^{exp}")
        terms.append("*".join(factors) if factors else "0")
    return " + ".join(terms) if terms else "0"


def write_singular_file(path, variables, eqs, det_poly, p, seconds=300):
    varlist = ",".join(str(v) for v in variables)
    polys = [singular_poly_str(e, variables, p) for e in eqs] + [singular_poly_str(det_poly, variables, p)]
    content = []
    content.append(f"// analysis modular off-W core system over GF({p}); chart M[0,0]=1, M[1,1]=1")
    content.append(f"// 24 off-W equations plus det(M)-1. Modular exploration only.")
    content.append(f"timer=1;")
    content.append(f"ring r = {p},({varlist}),dp;")
    content.append("ideal I =")
    for i, poly in enumerate(polys):
        sep = "," if i < len(polys) - 1 else ";"
        content.append(f"  {poly}{sep}")
    content.append("print(\"vars=\"+string(nvars(basering))+\" eqs=\"+string(size(I))); ")
    content.append("option(redSB);")
    content.append("ideal G = slimgb(I);")
    content.append("print(\"std_size=\"+string(size(G))); ")
    content.append("print(\"dim=\"+string(dim(G))); ")
    content.append("print(\"vdim=\"+string(vdim(G))); ")
    content.append("print(\"contains_one=\"+string(reduce(1,G)==0));")
    content.append("print(\"timer=\"+string(timer));")
    path.write_text("\n".join(content) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--prime", type=int, default=65521)
    ap.add_argument("--chart", default="0,1")
    ap.add_argument("--skip-polys", action="store_true")
    args = ap.parse_args()
    p = args.prime
    chart = tuple(int(x) for x in args.chart.split(","))
    proj = off_projection_matrix(p)
    summary = {
        "prime": p,
        "chart": list(chart),
        "dimensions": {
            "Sym3V": len(MONOS),
            "Z4_invariant": int(proj["ranks"]["invariant_span"]),
            "H_W": int(proj["ranks"]["H_W_span"]),
            "off_quotient": int(proj["ranks"]["off_rows"]),
            "off_on_H_nonzero_entries": int(proj["ranks"]["off_on_H_zero"]),
        },
        "scope": "modular projection and one SL3/T chart; not a characteristic-zero certificate by itself",
    }
    if not args.skip_polys:
        variables, eqs, det_poly = build_off_equations(proj, p, chart=chart)
        sing_path = OUT / f"off_core_chart{chart[0]}{chart[1]}_p{p}.sing"
        write_singular_file(sing_path, variables, eqs, det_poly, p)
        degrees = [int(sp.Poly(e, *variables, modulus=p).total_degree()) for e in eqs]
        summary.update({
            "variables": [str(v) for v in variables],
            "off_equation_count": len(eqs),
            "det_equation_included": True,
            "max_off_equation_degree": max(degrees),
            "det_degree": int(sp.Poly(det_poly, *variables, modulus=p).total_degree()),
            "singular_file": str(sing_path),
        })
    out = OUT / f"off_projection_summary_chart{chart[0]}{chart[1]}_p{p}.json"
    out.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2), flush=True)
    print(f"Saved {out}", flush=True)


if __name__ == "__main__":
    main()
