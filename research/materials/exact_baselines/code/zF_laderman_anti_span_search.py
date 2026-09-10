#!/usr/bin/env python3
"""analysis: finite-field Z(F) search for tau-symmetric rank-22 skeletons.

Scientific target.
------------------
For a tau-stable free-orbit family with m free pairs, let F be the row span of
the 2m rank-one slice generators

    v_j \otimes P(w_j),  w_j \otimes P(v_j),

where P is 3x3 transpose on row-major 9-vectors and w_j = vec(C_j^T).
If the anti condition L_anti <= F is satisfied, the remaining fixed terms must
be tau-fixed rank-one matrices

    x \otimes P(x)

lying in S(F)=F+L_1 whose quotient images span S(F)/F.  Thus for a skeleton
(f,m), f=22-2m, the exact finite-field test is

    qdim(F):=dim(F+L_1)-dim(F) <= f,
    rank span{ [x P(x)] mod F : x P(x) in F+L_1 } = qdim(F).

A hit recovers A-factor coefficients linearly and replays all 729 tensor
coordinates.  A miss is only for the sampled anti family.

This script explores a controlled anti-feasible family: the projective
decomposable bivectors inside the 8-dimensional anti span of the transported
Laderman standard-tau witness over F_p.  It then changes the basis of each
2-plane by random GL_2 transformations, so the symmetric points vary while the
anti span remains the Laderman 8-plane.  This is not a global exclusion; it is
a first exact Z(F) functional on a nontrivial moving family anchored at the
known (7,8) rank-23 control.
"""
from __future__ import annotations
import argparse, itertools, json, random, time
from pathlib import Path
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "zF_search"
OUT.mkdir(parents=True, exist_ok=True)

# ---------------- finite-field linear algebra ----------------
def inv(a, p):
    return pow(int(a) % p, -1, p)

def mod(A, p):
    return np.asarray(A, dtype=np.int64) % p

def rref(M, p):
    M = mod(M, p).copy()
    m, n = M.shape
    r = 0
    piv = []
    for c in range(n):
        pivrow = None
        for i in range(r, m):
            if M[i, c] % p:
                pivrow = i
                break
        if pivrow is None:
            continue
        if pivrow != r:
            M[[r, pivrow]] = M[[pivrow, r]]
        M[r, :] = (M[r, :] * inv(M[r, c], p)) % p
        for i in range(m):
            if i != r and M[i, c] % p:
                M[i, :] = (M[i, :] - M[i, c] * M[r, :]) % p
        piv.append(c)
        r += 1
        if r == m:
            break
    return M, r, piv

def rank(M, p):
    return rref(M, p)[1]

def row_basis(M, p):
    R, r, piv = rref(M, p)
    return R[:r].copy(), piv

def nullspace_rows(M, p):
    R, r, piv = rref(M, p)
    n = M.shape[1]
    pset = set(piv)
    free = [c for c in range(n) if c not in pset]
    out = []
    for f in free:
        x = np.zeros(n, dtype=np.int64)
        x[f] = 1
        for row, col in enumerate(piv):
            x[col] = (-R[row, f]) % p
        out.append(x % p)
    return np.vstack(out) % p if out else np.zeros((0, n), dtype=np.int64)

def solve_linear(A, b, p):
    A = mod(A, p)
    b = mod(b, p).reshape(A.shape[0], 1)
    m, n = A.shape
    aug = np.concatenate([A.copy(), b], axis=1) % p
    r = 0
    piv = []
    for c in range(n):
        pivrow = None
        for i in range(r, m):
            if aug[i, c] % p:
                pivrow = i
                break
        if pivrow is None:
            continue
        if pivrow != r:
            aug[[r, pivrow]] = aug[[pivrow, r]]
        aug[r, :] = (aug[r, :] * inv(aug[r, c], p)) % p
        for i in range(m):
            if i != r and aug[i, c] % p:
                aug[i, :] = (aug[i, :] - aug[i, c] * aug[r, :]) % p
        piv.append(c)
        r += 1
        if r == m:
            break
    for i in range(r, m):
        if np.all(aug[i, :n] % p == 0) and aug[i, n] % p:
            return None
    x = np.zeros(n, dtype=np.int64)
    for row, col in enumerate(piv):
        x[col] = aug[row, n] % p
    return x % p

def row_contains(B, L, p):
    B = mod(B, p); L = mod(L, p)
    rB = rank(B, p)
    rBL = rank(np.vstack([B, L]) % p, p)
    return rB == rBL, rB, rBL, rBL - rB

# ---------------- tensor/tau conventions ----------------
P9 = np.array([3 * (k % 3) + k // 3 for k in range(9)], dtype=np.int64)
WEDGE_PAIRS = [(a, b) for a in range(9) for b in range(a + 1, 9)]

def Pvec(v):
    return np.asarray(v, dtype=np.int64)[P9]

def mat_from_vec(v):
    return np.asarray(v, dtype=np.int64).reshape(3, 3)

def vec9(M):
    return np.asarray(M, dtype=np.int64).reshape(9)

def slot_from_vw(v, w, p):
    # v = vec(B), w = vec(C^T), so vec(C)=P(w)
    return np.outer(v % p, Pvec(w) % p).reshape(81) % p

def fixed_slot(x, p):
    return np.outer(x % p, Pvec(x) % p).reshape(81) % p

def free_slots_from_pair(v, w, p):
    return [slot_from_vw(v, w, p), slot_from_vw(w, v, p)]

def wedge_vec(v, w, p):
    out = np.zeros(36, dtype=np.int64)
    for t, (i, j) in enumerate(WEDGE_PAIRS):
        out[t] = (v[i] * w[j] - v[j] * w[i]) % p
    return out

def wedge_to_skew(beta, p):
    K = np.zeros((9, 9), dtype=np.int64)
    for t, (i, j) in enumerate(WEDGE_PAIRS):
        K[i, j] = beta[t] % p
        K[j, i] = (-beta[t]) % p
    return K % p

def factor_decomposable(beta, p):
    """Return v,w with v∧w=beta if beta is a nonzero rank-2 skew form."""
    beta = np.asarray(beta, dtype=np.int64) % p
    if np.all(beta == 0):
        return None
    K = wedge_to_skew(beta, p)
    if rank(K, p) != 2:
        return None
    pivot = None
    for i in range(9):
        for j in range(i + 1, 9):
            if K[i, j] % p:
                pivot = (i, j)
                break
        if pivot is not None:
            break
    if pivot is None:
        return None
    i, j = pivot
    lam = K[i, j] % p
    ilam = inv(lam, p)
    v = (K[:, j] * ilam) % p
    w = K[i, :].copy() % p
    test = wedge_vec(v, w, p)
    if not np.array_equal(test % p, beta % p):
        # Try the opposite sign if the convention above disagrees.
        w = (-w) % p
        test = wedge_vec(v, w, p)
    if not np.array_equal(test % p, beta % p):
        raise RuntimeError("rank-2 skew factorization convention failed")
    return v % p, w % p

def build_L1(p):
    rows = []
    for a in range(3):
        for b in range(3):
            M = np.zeros((9, 9), dtype=np.int64)
            for k in range(3):
                M[3*b+k, 3*k+a] = 1
            rows.append(M.reshape(81) % p)
    return np.vstack(rows) % p

def build_Lsym_Lanti_81(p):
    L1 = build_L1(p)
    sym, anti = [], []
    for a in range(3):
        sym.append(L1[3*a+a])
    for a in range(3):
        for b in range(a + 1, 3):
            sym.append((L1[3*a+b] + L1[3*b+a]) % p)
            anti.append((L1[3*a+b] - L1[3*b+a]) % p)
    return np.vstack(sym) % p, np.vstack(anti) % p

def anti_target_wedge(p):
    # Same convention as analysis: theta_ab = -sum_k e_{a,k}∧e_{b,k} up to row basis.
    T = np.zeros((3, 36), dtype=np.int64)
    for r, (a, b) in enumerate([(0, 1), (0, 2), (1, 2)]):
        vrows = []
        beta = np.zeros(36, dtype=np.int64)
        for k in range(3):
            e1 = 3*b + k
            e2 = 3*a + k
            # Matrix L1 anti uses rows (3*b+k,3*k+a) - (3*a+k,3*k+b).
            # In v∧w coordinates from analysis this target is represented by
            # -sum e_{a,k}∧e_{b,k}; sign is immaterial for row containment.
            i, j = sorted((3*a + k, 3*b + k))
            sign = 1 if (3*a+k) < (3*b+k) else -1
            beta[WEDGE_PAIRS.index((i, j))] = (beta[WEDGE_PAIRS.index((i, j))] - sign) % p
        T[r] = beta % p
    return T % p

# ---------------- load transported Laderman over F_p ----------------
def mat_inv(A, p):
    A = mod(A, p)
    n = A.shape[0]
    aug = np.concatenate([A.copy(), np.eye(n, dtype=np.int64)], axis=1) % p
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, n):
            if aug[i, c] % p:
                piv = i; break
        if piv is None:
            raise ValueError('singular')
        if piv != r:
            aug[[r, piv]] = aug[[piv, r]]
        aug[r, :] = (aug[r, :] * inv(aug[r, c], p)) % p
        for i in range(n):
            if i != r and aug[i, c] % p:
                aug[i, :] = (aug[i, :] - aug[i, c] * aug[r, :]) % p
        r += 1
    return aug[:, n:] % p

def dot3(u, v, p):
    return int(np.dot(u % p, v % p)) % p

def find_R_delta(p):
    vecs = [np.array(v, dtype=np.int64) for v in itertools.product(range(p), repeat=3) if any(v)]
    for delta in range(1, p):
        targets = [(-delta) % p, delta % p, delta % p]
        cand = [[v for v in vecs if dot3(v, v, p) == t] for t in targets]
        for c0 in cand[0]:
            for c1 in cand[1]:
                if dot3(c0, c1, p):
                    continue
                for c2 in cand[2]:
                    if dot3(c0, c2, p) == 0 and dot3(c1, c2, p) == 0:
                        R = np.column_stack([c0, c1, c2]) % p
                        if rank(R, p) == 3:
                            return delta, R
    raise RuntimeError(f"no scaled congruence R over F_{p}")

def load_transported(p):
    src_path = SCRIPT_DIR / "laderman_tau_decomp.py"
    src = src_path.read_text()
    prefix = src.split('print(f"Sum matches T333')[0]
    ns = {"__file__": str(src_path), "__name__": "defs_only"}
    exec(compile(prefix, str(src_path), "exec"), ns)
    terms = [(mod(a, p), mod(b, p), mod(c, p)) for a, b, c in ns['terms']]
    eps1 = mod(ns['eps1'], p)
    pi12 = mod(ns['pi12'], p)
    Q0 = eps1 @ pi12 % p
    delta, R = find_R_delta(p)
    Q = (delta * Q0) % p
    Qinv = mat_inv(Q, p)
    Rinv = mat_inv(R, p)
    def g(a, b, c):
        return (a @ Qinv % p, Q @ b @ Rinv % p, R @ c % p)
    return [g(a, b, c) for a, b, c in terms], delta, R

FREE_PAIRS = [(1,4),(2,5),(6,15),(7,17),(8,16),(10,13),(12,14),(19,21)]  # 0-based
FIXED_INDICES = [i for i in range(23) if i not in {x for pr in FREE_PAIRS for x in pr}]

def laderman_free_pairs_vectors(p):
    terms, delta, R = load_transported(p)
    pairs = []
    for i, j in FREE_PAIRS:
        _, b, c = terms[i]
        v = vec9(b) % p
        w = vec9(c.T) % p
        pairs.append((v, w))
    return pairs, terms, delta, R

# ---------------- projective enumeration and GL2 ----------------
def projective_vectors(n, p):
    for tup in itertools.product(range(p), repeat=n):
        if not any(tup):
            continue
        first = next(i for i, x in enumerate(tup) if x % p)
        if tup[first] != 1:
            continue
        yield np.array(tup, dtype=np.int64)

def GL2_list(p):
    out = []
    for a,b,c,d in itertools.product(range(p), repeat=4):
        det = (a*d - b*c) % p
        if det:
            out.append((a,b,c,d,det))
    return out

def apply_GL2(pair, g, p):
    v, w = pair
    a,b,c,d,det = g
    return ((a*v + b*w) % p, (c*v + d*w) % p)

# ---------------- Z(F) analysis ----------------
def precompute_fixed_squares(p):
    xs = []
    sqs = []
    for x in projective_vectors(9, p):
        xs.append(x)
        sqs.append(fixed_slot(x, p))
    return np.vstack(xs) % p, np.vstack(sqs) % p

def quotient_functionals(F_basis, L1, p):
    # Choose Lext rows extending F_basis to F+L1. Return qdim and Phi such that x@Phi are quotient coords.
    current = F_basis.copy()
    cur = rank(current, p) if current.size else 0
    Lext = []
    Lext_idx = []
    for i, row in enumerate(L1):
        nr = rank(np.vstack([current, row]) % p, p) if current.size else 1
        if nr > cur:
            Lext.append(row)
            Lext_idx.append(i)
            current = np.vstack([current, row]) % p if current.size else row.reshape(1, -1) % p
            cur = nr
    if Lext:
        Lext = np.vstack(Lext) % p
    else:
        Lext = np.zeros((0, 81), dtype=np.int64)
    constraints = np.vstack([F_basis, Lext]) % p if F_basis.size else Lext
    Phi = []
    for k in range(len(Lext_idx)):
        rhs = np.zeros(constraints.shape[0], dtype=np.int64)
        rhs[F_basis.shape[0] + k] = 1
        sol = solve_linear(constraints, rhs, p)
        if sol is None:
            raise RuntimeError("failed to build quotient functional")
        Phi.append(sol)
    Phi = np.vstack(Phi).T % p if Phi else np.zeros((81, 0), dtype=np.int64)
    return len(Lext_idx), Lext_idx, Phi

def build_T333(p):
    T = np.zeros((9, 9, 9), dtype=np.int64)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*k+i] = 1
    return T % p

def recover_u(gens, L1, p):
    X = np.vstack(gens) % p
    A = X.T
    coeffs = []
    for row in L1:
        sol = solve_linear(A, row, p)
        if sol is None:
            return None
        coeffs.append(sol)
    C = np.vstack(coeffs) % p
    us = []
    for ell in range(X.shape[0]):
        U = np.zeros((3, 3), dtype=np.int64)
        for a in range(3):
            for b in range(3):
                U[a, b] = C[3*a+b, ell] % p
        us.append(U)
    return us

def tensor_from_terms(terms, p):
    T = np.zeros((9, 9, 9), dtype=np.int64)
    for U, B, C in terms:
        uu = vec9(U) % p
        vv = vec9(B) % p
        ww = vec9(C) % p
        nz_u = np.nonzero(uu % p)[0]
        nz_v = np.nonzero(vv % p)[0]
        nz_w = np.nonzero(ww % p)[0]
        for i in nz_u:
            for j in nz_v:
                val = uu[i] * vv[j] % p
                for k in nz_w:
                    T[i, j, k] = (T[i, j, k] + val * ww[k]) % p
    return T % p

def analyze_configuration(p, pairs, Xproj, Sq, L1, Lsym, Lanti81, f_allowed=None, want_replay=False):
    free_gens = []
    term_BC = []
    wedge_rows = []
    for v, w in pairs:
        free_gens.extend(free_slots_from_pair(v, w, p))
        term_BC.append((mat_from_vec(v) % p, mat_from_vec(Pvec(w)) % p))
        term_BC.append((mat_from_vec(w) % p, mat_from_vec(Pvec(v)) % p))
        wedge_rows.append(wedge_vec(v, w, p))
    F = np.vstack(free_gens) % p
    F_basis, _ = row_basis(F, p)
    rankF = F_basis.shape[0]
    anti_ok, _, _, anti_def = row_contains(F_basis, Lanti81, p)
    S = np.vstack([F_basis, L1]) % p
    S_basis, _ = row_basis(S, p)
    rankS = S_basis.shape[0]
    qdim, Lext_idx, Phi = quotient_functionals(F_basis, L1, p)
    FcapL1 = rankF + rank(L1, p) - rankS
    sym_intersection_dim = max(0, FcapL1 - 3) if anti_ok else None
    # Z(F): tau-fixed rank-one squares in S=F+L1.
    N = nullspace_rows(S_basis, p)
    if N.shape[0] == 0:
        mask = np.ones(Sq.shape[0], dtype=bool)
    else:
        vals = (Sq @ N.T) % p
        mask = np.all(vals == 0, axis=1)
    Z_idx = np.nonzero(mask)[0]
    if qdim == 0:
        qcoords = np.zeros((len(Z_idx), 0), dtype=np.int64)
        qrank = 0
    elif len(Z_idx) == 0:
        qcoords = np.zeros((0, qdim), dtype=np.int64)
        qrank = 0
    else:
        qcoords = (Sq[Z_idx] @ Phi) % p
        # remove zero quotient rows for rank calculation; zeros do not help but count in Z.
        qrank = rank(qcoords, p) if qcoords.size else 0
    selected_idx = []
    if qdim > 0 and len(Z_idx):
        current = np.zeros((0, qdim), dtype=np.int64)
        cur = 0
        for local, global_idx in enumerate(Z_idx):
            q = qcoords[local]
            if np.all(q == 0):
                continue
            nr = rank(np.vstack([current, q]) % p, p) if current.size else 1
            if nr > cur:
                selected_idx.append(int(global_idx))
                current = np.vstack([current, q]) % p if current.size else q.reshape(1, -1) % p
                cur = nr
                if cur == qdim:
                    break
    hit = (anti_ok and qrank == qdim and (f_allowed is None or qdim <= f_allowed))
    replay = None
    if hit and want_replay:
        gens = list(F)
        fixed_BC = []
        for idx in selected_idx[:qdim]:
            x = Xproj[idx]
            gens.append(fixed_slot(x, p))
            fixed_BC.append((mat_from_vec(x) % p, mat_from_vec(Pvec(x)) % p))
        contains, rG, rGL, defect = row_contains(np.vstack(gens) % p, L1, p)
        us = recover_u(gens, L1, p)
        replay_ok = None
        if us is not None:
            terms = []
            for ell, (B, C) in enumerate(term_BC):
                terms.append((us[ell], B, C))
            base = len(term_BC)
            for j, (B, C) in enumerate(fixed_BC):
                terms.append((us[base+j], B, C))
            replay_ok = bool(np.array_equal(tensor_from_terms(terms, p), build_T333(p)))
        replay = {
            "combined_contains_L1": bool(contains),
            "combined_rank": int(rG),
            "combined_aug_rank_with_L1": int(rGL),
            "combined_defect": int(defect),
            "recovered_u_exists": us is not None,
            "full_T333_replay": bool(replay_ok) if replay_ok is not None else None,
            "num_terms_used": int(2*len(pairs) + qdim),
            "selected_fixed_projective_indices": selected_idx[:qdim],
            "selected_fixed_vectors": [[int(z) for z in Xproj[idx].tolist()] for idx in selected_idx[:qdim]],
        }
    return {
        "m": int(len(pairs)),
        "f_allowed_for_rank22": None if f_allowed is None else int(f_allowed),
        "rankF": int(rankF),
        "rankF_plus_L1": int(rankS),
        "F_cap_L1_dim": int(FcapL1),
        "anti_contained_in_F": bool(anti_ok),
        "anti_defect": int(anti_def),
        "sym_intersection_dim_in_F_cap_L1": None if sym_intersection_dim is None else int(sym_intersection_dim),
        "quotient_dimension_qdim": int(qdim),
        "Lext_indices": [int(i) for i in Lext_idx],
        "Z_fixed_squares_count_over_Fp": int(len(Z_idx)),
        "Z_quotient_rank": int(qrank),
        "rank22_condition_met_by_Z": bool(hit),
        "term_count_if_Z_spans": int(2*len(pairs) + qdim),
        "selected_Z_indices_for_basis": selected_idx,
        "replay": replay,
    }

# ---------------- search driver ----------------
def enumerate_decomposable_points_in_laderman_anti_span(p, lad_pairs):
    B0 = np.vstack([wedge_vec(v, w, p) for v, w in lad_pairs]) % p
    B0_basis, _ = row_basis(B0, p)
    assert B0_basis.shape[0] == 8, f"expected 8-dimensional Laderman anti span, got {B0_basis.shape[0]}"
    seen = set()
    points = []
    for coeff in projective_vectors(8, p):
        beta = coeff @ B0_basis % p
        if np.all(beta == 0):
            continue
        # canonical projective normalization of beta itself
        first = int(np.nonzero(beta % p)[0][0])
        beta = beta * inv(beta[first], p) % p
        key = tuple(int(x) for x in beta.tolist())
        if key in seen:
            continue
        fac = factor_decomposable(beta, p)
        if fac is None:
            continue
        seen.add(key)
        points.append({"beta": beta, "pair": fac})
    return B0_basis, points

def random_independent_points(rng, points, m, p, require_span_rank=8, max_tries=2000):
    """Choose m decomposable anti points spanning the requested anti space.

    Over F3 the Laderman anti 8-plane contains only the eight Laderman
    decomposable points.  For m>8 we therefore must allow repeated planes;
    distinct GL2 choices on the same plane still change the symmetric/tau-fixed
    span F even though the bivector row is projectively repeated.
    """
    n = len(points)
    if n == 0:
        return None
    for _ in range(max_tries):
        if m <= n:
            idxs = rng.sample(range(n), m)
        else:
            idxs = list(range(n)) + [rng.randrange(n) for _ in range(m - n)]
            rng.shuffle(idxs)
        B = np.vstack([points[i]["beta"] for i in idxs]) % p
        if rank(B, p) >= require_span_rank:
            return idxs
    return None

def config_from_indices(rng, points, idxs, gl2s, p):
    pairs = []
    gl2_choices = []
    for idx in idxs:
        base = points[idx]["pair"]
        g = rng.choice(gl2s)
        pairs.append(apply_GL2(base, g, p))
        gl2_choices.append(g)
    return pairs, gl2_choices

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--p', type=int, default=3)
    ap.add_argument('--samples', type=int, default=1000)
    ap.add_argument('--seed', type=int, default=6801)
    ap.add_argument('--m-list', default='8,9,10,11')
    ap.add_argument('--time-budget', type=float, default=600.0)
    ap.add_argument('--save-every-hit', action='store_true')
    args = ap.parse_args()
    p = args.p
    rng = random.Random(args.seed)
    t0 = time.time()
    m_list = [int(x) for x in args.m_list.split(',') if x]

    L1 = build_L1(p)
    Lsym, Lanti81 = build_Lsym_Lanti_81(p)
    Xproj, Sq = precompute_fixed_squares(p)
    lad_pairs, lad_terms, delta, R = laderman_free_pairs_vectors(p)
    B0_basis, points = enumerate_decomposable_points_in_laderman_anti_span(p, lad_pairs)
    gl2s = GL2_list(p)

    # Sanity: the analysis Laderman eight anti rows contain L_anti.
    lad_result = analyze_configuration(p, lad_pairs, Xproj, Sq, L1, Lsym, Lanti81, f_allowed=6, want_replay=False)

    results = {
        "field": f"F_{p}",
        "seed": args.seed,
        "samples_requested": args.samples,
        "time_budget_sec": args.time_budget,
        "scaled_transport_delta": int(delta),
        "scaled_transport_R_columns": R.astype(int).tolist(),
        "projective_fixed_vectors_count": int(Xproj.shape[0]),
        "laderman_anti_span_rank": int(B0_basis.shape[0]),
        "decomposable_projective_points_inside_laderman_anti_span": int(len(points)),
        "GL2_choices_per_plane": int(len(gl2s)),
        "laderman_control_ZF": lad_result,
        "m_results": {},
        "hits": [],
        "interpretation": (
            "Search is restricted to free-orbit planes whose bivectors lie in and span the transported "
            "Laderman 8-dimensional anti span. It is an exact finite-field moving-family test of the Z(F) "
            "functional, not a global nonexistence theorem. A hit replays T333 and is an exact rank<=22 "
            "scheme over the displayed field."
        ),
    }

    for m in m_list:
        f_allowed = 22 - 2*m
        if f_allowed < 0:
            continue
        summary = {
            "m": m,
            "f_allowed": f_allowed,
            "samples_done": 0,
            "rankF_hist": {},
            "F_cap_L1_hist": {},
            "sym_intersection_hist": {},
            "qdim_hist": {},
            "Z_count_hist": {},
            "Z_qrank_hist": {},
            "best_records": [],
            "hit_count": 0,
        }
        best_records = []
        for s in range(args.samples):
            if time.time() - t0 > args.time_budget:
                summary["timed_out"] = True
                break
            idxs = random_independent_points(rng, points, m, p, require_span_rank=8)
            if idxs is None:
                summary["failed_to_choose_independent_points"] = True
                break
            pairs, gl2_choices = config_from_indices(rng, points, idxs, gl2s, p)
            rec = analyze_configuration(p, pairs, Xproj, Sq, L1, Lsym, Lanti81, f_allowed=f_allowed, want_replay=False)
            summary["samples_done"] += 1
            for key, val in [("rankF_hist", rec["rankF"]), ("F_cap_L1_hist", rec["F_cap_L1_dim"]),
                             ("sym_intersection_hist", rec["sym_intersection_dim_in_F_cap_L1"]),
                             ("qdim_hist", rec["quotient_dimension_qdim"]), ("Z_qrank_hist", rec["Z_quotient_rank"] )]:
                k = str(val)
                summary[key][k] = summary[key].get(k, 0) + 1
            # Bin Z counts coarsely to keep JSON compact.
            zc = rec["Z_fixed_squares_count_over_Fp"]
            zbin = str(zc if zc < 20 else (20 + 10*((zc-20)//10)))
            summary["Z_count_hist"][zbin] = summary["Z_count_hist"].get(zbin, 0) + 1
            score = (1 if rec["rank22_condition_met_by_Z"] else 0,
                     -max(0, rec["quotient_dimension_qdim"] - f_allowed),
                     rec["Z_quotient_rank"] - rec["quotient_dimension_qdim"],
                     -rec["quotient_dimension_qdim"],
                     rec["Z_fixed_squares_count_over_Fp"])
            compact = {
                "score": score,
                "sample": s,
                "indices": idxs,
                "gl2_choices": [list(map(int, g[:4])) for g in gl2_choices],
                "record": {k: rec[k] for k in rec if k not in ("replay", "selected_Z_indices_for_basis")},
                "selected_Z_indices_for_basis": rec["selected_Z_indices_for_basis"][:10],
            }
            best_records.append(compact)
            best_records = sorted(best_records, key=lambda x: x["score"], reverse=True)[:8]
            if rec["rank22_condition_met_by_Z"]:
                # Recompute with replay and store exact vectors.
                rec2 = analyze_configuration(p, pairs, Xproj, Sq, L1, Lsym, Lanti81, f_allowed=f_allowed, want_replay=True)
                hit = {
                    "m": m,
                    "sample": s,
                    "indices": idxs,
                    "gl2_choices": [list(map(int, g[:4])) for g in gl2_choices],
                    "record": rec2,
                    "pairs": [
                        {"v": [int(x) for x in v.tolist()], "w": [int(x) for x in w.tolist()]}
                        for v, w in pairs
                    ],
                }
                summary["hit_count"] += 1
                results["hits"].append(hit)
        # Stop on a verified replay hit unless --save-every-hit is enabled.
                if rec2["replay"] and rec2["replay"].get("full_T333_replay") and not args.save_every_hit:
                    summary["best_records"] = best_records
                    results["m_results"][str(m)] = summary
                    out_path = OUT / f"zF_laderman_anti_span_search_F{p}.json"
                    out_path.write_text(json.dumps(results, indent=2) + "\n")
                    print(json.dumps(results, indent=2))
                    print(f"SAVED {out_path}")
                    return
        summary["best_records"] = best_records
        results["m_results"][str(m)] = summary

    out_path = OUT / f"zF_laderman_anti_span_search_F{p}.json"
    out_path.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))
    print(f"SAVED {out_path}")

if __name__ == '__main__':
    main()
