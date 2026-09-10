#!/usr/bin/env python3
"""
analysis: tail equations after canonical Q-basis off-block extraction.

The off blocks qz^2, qw^2, pzw do not determine the affine scale of a length-4
Z4 cube orbit.  If a recovered form has components (p,q,z,w), then
    z,w -> t z,t w,    p,q -> t^{-2}p,t^{-2}q
preserves qz^2, qw^2, and pzw but multiplies the p^3+pq^2 tail by t^{-6}.
Thus the two size-4 orbits introduce two tail scalars h1,h2 after off-block
extraction.  This script makes that hidden degree of freedom explicit and tests
BILR as a positive control for the tail logic.

It checks two rank-22 residual patterns in the generic q-independent branch:
  4+4+1+1: pq^2 tail after subtracting h1,h2 size-4 tails must vanish; the
            remaining p^3 ternary cubic must be a sum of two cubes.
  4+4+2:   pq^2 tail must be rank-one with a square q-quadratic; then the
            remaining p^3 must be proportional to the same p-direction cubed.
For BILR the correct pattern is 4+4+2+1, so both rank-22 tests should fail while
allowing one additional fixed p-cube should recover the known tail.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path

import numpy as np
import sympy as sp

import z4_qbasis_selftest as qb
from z4_qbasis_generic_extractor import (
    P,
    conic_points_in_pencil,
    exact_vector_from_quad,
    inv,
    p3_indices,
    pq2_indices,
    solve_linear_fullrank,
    solve_p_from_pzw,
    solve_q_from_qz,
    solve_t_from_q,
    square_vector_from_projective_quad,
)

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "z4_qbasis"
OUT.mkdir(parents=True, exist_ok=True)

h1_sym, h2_sym = sp.symbols("h1 h2")


def vec_mod(v):
    return np.array(v, dtype=object).reshape(-1) % P


def cube_p3_from_p(pvec):
    l = np.zeros(qb.N, dtype=object)
    l[qb.GROUPS["p"]] = np.array(pvec, dtype=object) % P
    C = qb.cube_vec(l, P)
    return vec_mod([C[i] for i in p3_indices()])


def rank1_p3_test(F):
    """Return whether a p-space ternary cubic is proportional to one cube over F_P."""
    F = vec_mod(F)
    # Brute-force via first catalecticant rank one plus coefficient consistency.
    # For a cube lambda*(a,b,c)^3, the first partial/catalectic matrix below has rank 1.
    cat = np.array([
        [F[0], F[1], F[2], F[3], F[4], F[5]],
        [F[1], F[3], F[4], F[6], F[7], F[8]],
        [F[2], F[4], F[5], F[7], F[8], F[9]],
    ], dtype=object) % P
    if qb.rank_mod(cat, P) > 1:
        return False, None
    # Try to reconstruct from a projective vector by scanning a nonzero partial row.
    # This is enough for the small controls; if cat is zero, F is zero.
    if not any(int(x) % P for x in F):
        return True, {"zero": True}
    # Exhaustive over projective P^2 is 65521^2, too large; use equations from nonzero coefficients.
    # Use sympy solve over modulus for the parameterization lambda*(a,b,c)^3 with chart a/b/c=1.
    a, b, c, lam = sp.symbols("a b c lam")
    mons = [a**3, a**2*b, a**2*c, a*b**2, a*b*c, a*c**2, b**3, b**2*c, b*c**2, c**3]
    # Our coefficient convention for cube_vec has multinomial coefficients: a^2 b coefficient is 3a^2b, abc is 6abc.
    coeff_mons = [a**3, 3*a**2*b, 3*a**2*c, 3*a*b**2, 6*a*b*c, 3*a*c**2, b**3, 3*b**2*c, 3*b*c**2, c**3]
    # Rather than full solve, try charts with one coordinate fixed to 1 and Groebner; controls have simple roots.
    for fixed_var, fixed_val in [(a, 1), (b, 1), (c, 1)]:
        eqs = []
        for val, expr in zip(F, coeff_mons):
            eqs.append((lam * expr - int(val)) % P)
        eqs = [sp.Poly(e.subs(fixed_var, fixed_val), a, b, c, lam, modulus=P).as_expr() for e in eqs]
        vars_chart = [v for v in [a, b, c, lam] if v != fixed_var]
        try:
            G = sp.groebner(eqs, *vars_chart, modulus=P, order="lex")
            if not any(g.as_expr() == 1 for g in G.polys):
                return True, {"chart_fixed": str(fixed_var), "groebner_basis_size": len(G.polys)}
        except Exception:
            pass
    return False, {"cat_rank": 1, "param_solve_failed": True}


def p3_catalecticant_rank(F):
    F = vec_mod(F)
    cat = np.array([
        [F[0], F[1], F[2], F[3], F[4], F[5]],
        [F[1], F[3], F[4], F[6], F[7], F[8]],
        [F[2], F[4], F[5], F[7], F[8], F[9]],
    ], dtype=object) % P
    return int(qb.rank_mod(cat, P))


def affine_linear_h_solutions(A, b):
    sol, rk = solve_linear_fullrank(A, b)
    if sol is None:
        return {"consistent": False, "rank": int(rk), "solutions": []}
    # Determine if unique by rank.
    return {"consistent": True, "rank": int(rk), "unique": bool(rk == 2), "solutions": [[int(x) for x in sol[:2]]]} if rk == 2 else {"consistent": True, "rank": int(rk), "unique": False, "solutions": [[int(x) for x in sol[:2]]]}


def poly_mod_expr(coeff0, coeff1, coeff2):
    # Return a plain integer polynomial; SymPy's modulus=P handles reduction.
    # Do not use Python `% P`, which creates a non-polynomial Mod(...) expression.
    return int(coeff0) - int(coeff1) * h1_sym - int(coeff2) * h2_sym


def factor_roots_univar(poly, var):
    poly = sp.Poly(poly, var, modulus=P)
    if poly.is_zero:
        return None
    fl = sp.factor_list(poly.as_expr(), modulus=P)[1]
    roots = set()
    for fac, mult in fl:
        fp = sp.Poly(fac, var, modulus=P)
        if fp.degree() == 1:
            a = int(fp.nth(1)) % P
            b = int(fp.nth(0)) % P
            roots.add((-b * inv(a)) % P)
        else:
            # Low-degree fallback: brute only if cheap.
            if fp.degree() <= 4:
                for t in range(P):
                    if int(fp.eval(t)) % P == 0:
                        roots.add(t)
    return sorted(roots)


def solve_two_var_poly(eqs, max_roots=100):
    eqs = [sp.Poly(e, h1_sym, h2_sym, modulus=P).as_expr() for e in eqs]
    eqs = [e for e in eqs if sp.Poly(e, h1_sym, h2_sym, modulus=P).total_degree() >= 0 and int(sp.Poly(e, h1_sym, h2_sym, modulus=P).as_expr()) % P != 0] if False else eqs
    # Remove identically zero polynomials.
    clean = []
    for e in eqs:
        pe = sp.Poly(e, h1_sym, h2_sym, modulus=P)
        if not pe.is_zero:
            clean.append(pe.as_expr())
    if not clean:
        return {"status": "all_zero", "roots": []}
    try:
        G = sp.groebner(clean, h1_sym, h2_sym, modulus=P, order="lex")
    except Exception as exc:
        return {"status": "groebner_exception", "error": repr(exc), "roots": []}
    if any(sp.Poly(g.as_expr(), h1_sym, h2_sym, modulus=P).total_degree() == 0 and int(g.as_expr()) % P != 0 for g in G.polys):
        return {"status": "inconsistent", "basis_size": len(G.polys), "roots": []}
    # Find a univariate in h2.
    univar = None
    for g in G.polys:
        pg = sp.Poly(g.as_expr(), h1_sym, h2_sym, modulus=P)
        if pg.degree(h1_sym) == 0 and pg.degree(h2_sym) > 0:
            univar = sp.Poly(pg.as_expr(), h2_sym, modulus=P)
            break
    if univar is None:
        return {"status": "positive_dim_or_no_univar", "basis_size": len(G.polys), "basis_degrees": [int(sp.Poly(g.as_expr(), h1_sym, h2_sym, modulus=P).total_degree()) for g in G.polys], "roots": []}
    roots_h2 = factor_roots_univar(univar, h2_sym)
    roots = []
    if roots_h2 is None:
        return {"status": "univar_zero", "basis_size": len(G.polys), "roots": []}
    for y in roots_h2:
        # Solve for h1 by substituting h2=y in the original clean equations.
        candidates = None
        for e in clean:
            pe = sp.Poly(e.subs(h2_sym, y), h1_sym, modulus=P)
            if pe.is_zero:
                continue
            rts = factor_roots_univar(pe, h1_sym)
            if rts is None:
                continue
            rset = set(rts)
            candidates = rset if candidates is None else candidates & rset
        if candidates is None:
            candidates = set(range(P))  # should not happen in zero-dim controls
        for x in sorted(candidates):
            ok = True
            for e in clean:
                if int(sp.Poly(e, h1_sym, h2_sym, modulus=P).eval({h1_sym: x, h2_sym: y})) % P != 0:
                    ok = False
                    break
            if ok:
                roots.append((x, y))
                if len(roots) >= max_roots:
                    return {"status": "root_cap", "basis_size": len(G.polys), "roots": roots}
    return {"status": "ok", "basis_size": len(G.polys), "univar_degree": int(univar.degree()), "roots": roots}


def extract_generic_variants(C, weights):
    blocks = qb.extract_blocks(C, P)
    qz = np.array(blocks["qz2"], dtype=object) % P
    qw = np.array(blocks["qw2"], dtype=object) % P
    pzw = np.array(blocks["pzw"], dtype=object) % P
    qzN = (qz * inv(12)) % P
    qwN = (qw * inv(12)) % P
    pts = conic_points_in_pencil(qzN)
    variants = []
    for order in itertools.permutations(range(len(pts)), 2):
        s1, s2 = pts[order[0]], pts[order[1]]
        try:
            z1_base = square_vector_from_projective_quad(s1)
            z2_base = square_vector_from_projective_quad(s2)
        except ValueError:
            continue
        qs = solve_q_from_qz(qzN, s1, s2)
        if qs is None:
            continue
        q1, q2 = qs
        if (int(q1[0]) * int(q2[1]) - int(q1[1]) * int(q2[0])) % P == 0:
            continue
        ts = solve_t_from_q(qwN, q1, q2)
        if ts is None:
            continue
        t1, t2 = ts
        w1_base = exact_vector_from_quad(t1)
        w2_base = exact_vector_from_quad(t2)
        if w1_base is None or w2_base is None:
            continue
        for sz1, sz2, sw1, sw2 in itertools.product([1, P - 1], repeat=4):
            z1 = (z1_base * sz1) % P; z2 = (z2_base * sz2) % P
            w1 = (w1_base * sw1) % P; w2 = (w2_base * sw2) % P
            ps, prank = solve_p_from_pzw(pzw, z1, z2, w1, w2)
            if ps is None:
                continue
            p1, p2 = ps
            l1 = np.zeros(qb.N, dtype=object); l2 = np.zeros(qb.N, dtype=object)
            l1[qb.GROUPS["p"]] = p1; l1[qb.GROUPS["q"]] = q1; l1[qb.GROUPS["z"]] = z1; l1[qb.GROUPS["w"]] = w1
            l2[qb.GROUPS["p"]] = p2; l2[qb.GROUPS["q"]] = q2; l2[qb.GROUPS["z"]] = z2; l2[qb.GROUPS["w"]] = w2
            off_resid = (C - qb.orbit_cube(l1, weights, P, 4) - qb.orbit_cube(l2, weights, P, 4)) % P
            off_nonzero = int(sum(1 for i in off_indices() if int(off_resid[i]) % P))
            variants.append({"order": order, "signs": [sz1, sz2, sw1, sw2], "l1": l1, "l2": l2, "pzw_rank": prank, "off_nonzero_at_h1_h2_1": off_nonzero})
    return variants


def off_indices():
    idx = []
    for mi, m in enumerate(qb.MONOS):
        groups = []
        for j in m:
            groups.append(next(g for g, arr in qb.GROUPS.items() if j in arr))
        if any(g in ("z", "w") for g in groups):
            idx.append(mi)
    return idx


def analyze_variant(C, weights, var, known_extra_fixed=None):
    l1 = var["l1"]; l2 = var["l2"]
    T1 = qb.orbit_cube(l1, weights, P, 4)
    T2 = qb.orbit_cube(l2, weights, P, 4)
    pq_idx = pq2_indices(); p3_idx = p3_indices()
    Cpq = vec_mod([C[i] for i in pq_idx]); C3 = vec_mod([C[i] for i in p3_idx])
    T1pq = vec_mod([T1[i] for i in pq_idx]); T2pq = vec_mod([T2[i] for i in pq_idx])
    T13 = vec_mod([T1[i] for i in p3_idx]); T23 = vec_mod([T2[i] for i in p3_idx])
    # 4+4+1+1: Cpq - h1 T1pq - h2 T2pq = 0.
    A = np.stack([T1pq, T2pq], axis=1)
    sol4411 = affine_linear_h_solutions(A, Cpq)
    tests4411 = []
    for sol in sol4411.get("solutions", []):
        h1, h2 = sol
        F = (C3 - h1 * T13 - h2 * T23) % P
        tests4411.append({"h": [int(h1), int(h2)], "p3_catalecticant_rank": p3_catalecticant_rank(F), "rank1_cube_test": rank1_p3_test(F)[0]})
    # 4+4+2: Ppq(h) must be rank-one and square in q.
    mats = []
    for row in range(3):
        mats.append([poly_mod_expr(Cpq[3 * row + col], T1pq[3 * row + col], T2pq[3 * row + col]) for col in range(3)])
    eqs = []
    # 2x2 minors
    for r1, r2 in itertools.combinations(range(3), 2):
        for c1, c2 in itertools.combinations(range(3), 2):
            eqs.append(mats[r1][c1] * mats[r2][c2] - mats[r1][c2] * mats[r2][c1])
    # row discriminants for square q-quadratic
    for r in range(3):
        eqs.append(mats[r][1] ** 2 - 4 * mats[r][0] * mats[r][2])
    roots442 = solve_two_var_poly(eqs, max_roots=50)
    tests442 = []
    for h1, h2 in roots442.get("roots", []):
        Pmat = np.array([[int((mats[r][c]).subs({h1_sym: h1, h2_sym: h2})) % P for c in range(3)] for r in range(3)], dtype=object)
        if qb.rank_mod(Pmat, P) == 0:
            continue
        # Extract p direction from rank-one matrix: choose first nonzero square row.
        row_idx = next(r for r in range(3) if any(int(Pmat[r, c]) % P for c in range(3)))
        qsq = vec_mod(Pmat[row_idx, :])
        # Normalize p direction by that row coefficient = 1; pdir entries are row scalars.
        pdir = []
        # choose a nonzero column to compare row scalars
        col = next(c for c in range(3) if int(qsq[c]) % P)
        denom = int(qsq[col]) % P
        for r in range(3):
            pdir.append((int(Pmat[r, col]) * inv(denom)) % P)
        pdir = vec_mod(pdir)
        F = (C3 - h1 * T13 - h2 * T23) % P
        cube = cube_p3_from_p(pdir)
        # Proportional test F = gamma*cube.
        ok_prop, gamma = qb.projective_equal(cube, F, P)
        extra = None
        if known_extra_fixed is not None and ok_prop:
            pass
        # For BILR's true 4+4+2+1 tail: test if F - gamma*cube is one p-cube.
        one_more = False
        if any(int(x) % P for x in cube):
            ok, lam = qb.projective_equal(cube, F, P)
            if ok:
                gamma_val = lam
            else:
                gamma_val = None
            # Try all scalar gamma suggested by matching first nonzero cube coordinate if not proportional? no.
        # More useful: minimize by solving gamma from first nonzero cube coord and testing remainder rank one.
        gammas = []
        for a, b in zip(cube, F):
            if int(a) % P:
                gammas.append((int(b) * inv(int(a))) % P)
        gamma0 = gammas[0] if gammas else 0
        rem_after_len2 = (F - gamma0 * cube) % P
        one_more_rank1, one_more_info = rank1_p3_test(rem_after_len2)
        tests442.append({
            "h": [int(h1), int(h2)],
            "Ppq_rank": int(qb.rank_mod(Pmat, P)),
            "p_direction": [int(x) for x in pdir],
            "p3_proportional_to_p_direction_cube": bool(ok_prop),
            "gamma_from_first_cube_coord": int(gamma0),
            "p3_remainder_after_one_length2_cube_cat_rank": p3_catalecticant_rank(rem_after_len2),
            "p3_remainder_after_one_length2_cube_is_one_cube": bool(one_more_rank1),
        })
    return {"test_4411": {"pq2_linear": sol4411, "p3_tests": tests4411}, "test_442": {"pq2_rank_one_square_system": roots442, "p3_tests": tests442}}


def main():
    a0, Q, Qi, mu, weights, diag_ok, ii = qb.q_basis(P)
    assert diag_ok
    scheme = json.loads((WS / "data" / "ballard_z4_cyclic" / "ballard_z4_cyclic_scheme.json").read_text())
    T0_y = np.stack([qb.transform_stored_form_to_y(scheme["free_orbit_representatives"][0][key], Q, Qi, P) for key in ["U", "V", "W"]], axis=1) % P
    C = (qb.target_vec_short(P) - qb.free_contribution(T0_y, weights, P)) % P
    variants = extract_generic_variants(C, weights)
    summaries = []
    for idx, var in enumerate(variants[:32]):
        an = analyze_variant(C, weights, var)
        summaries.append({
            "variant_index": idx,
            "order": [int(x) for x in var["order"]],
            "signs": [int(x) for x in var["signs"]],
            "off_nonzero_at_h1_h2_1": int(var["off_nonzero_at_h1_h2_1"]),
            "analysis": an,
        })
    count_4411_pq_consistent = sum(1 for s in summaries if s["analysis"]["test_4411"]["pq2_linear"].get("consistent"))
    count_4411_rank2_possible_necessary = sum(1 for s in summaries for t in s["analysis"]["test_4411"]["p3_tests"] if t["p3_catalecticant_rank"] <= 2)
    count_442_pq_roots = sum(len(s["analysis"]["test_442"]["pq2_rank_one_square_system"].get("roots", [])) for s in summaries)
    count_442_full = sum(1 for s in summaries for t in s["analysis"]["test_442"]["p3_tests"] if t["p3_proportional_to_p_direction_cube"])
    count_442_plus_fixed = sum(1 for s in summaries for t in s["analysis"]["test_442"]["p3_tests"] if t["p3_remainder_after_one_length2_cube_is_one_cube"])
    result = {
        "prime": P,
        "scope": "BILR residual tail analysis in canonical Q-basis generic branch; rank-22 tests plus rank-23 positive-control behavior",
        "hidden_scale_rule": "Off blocks are invariant under z,w -> t z,t w and p,q -> t^{-2}p,t^{-2}q; the p^3+pq^2 tail is multiplied by h=t^{-6}. Therefore two size-4 orbits leave two tail scalars h1,h2 not determined by qz/qw/pzw.",
        "generic_variant_count": len(variants),
        "summaries": summaries,
        "aggregate": {
            "4411_variants_with_pq2_linear_solution": int(count_4411_pq_consistent),
            "4411_p3_catalecticant_rank_le_2_after_pq_solution": int(count_4411_rank2_possible_necessary),
            "442_total_pq_rank_one_square_h_roots": int(count_442_pq_roots),
            "442_p3_exact_proportional_cube_hits": int(count_442_full),
            "442_plus_one_fixed_cube_positive_hits": int(count_442_plus_fixed),
        },
        "interpretation": "For the BILR residual, the rank-22 patterns 4+4+1+1 and 4+4+2 do not pass these tail tests, while the appearance of 4+4+2 plus one fixed cube is the expected rank-23 positive control. The computation also shows why a generic off-block extractor without h1,h2 would be mathematically incomplete.",
    }
    out = OUT / "tail_branch_analyzer_bilr.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"out": str(out), "generic_variant_count": len(variants), "aggregate": result["aggregate"]}, indent=2))


if __name__ == "__main__":
    main()
