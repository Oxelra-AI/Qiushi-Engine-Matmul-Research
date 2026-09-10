#!/usr/bin/env python3
"""Integrated quotient construction pipeline: support supply -> trace filter -> Brent completion.

Stage 1  CP-SAT generates Wang-admissible multisets m_q (q in 1..255) with
         sum m_q = n and, for every Wang row U, sum_{q in U} m_q <= cap_U.
         Multiplicity upper bounds come from the codim-1 line caps.
Stage 2  Tight-contraction independent-verification-record filter (milliseconds).  A support that
         fails is rejected with a small inconsistent lambda subset and blocked.
Stage 3  Fixed-A Brent completion in CNF, solved with CaDiCaL.  SAT gives exact
         B/C vectors; the quotient decomposition is verified coordinatewise.
Stage 4  For pivot 1 (E11) a verified rank-n quotient decomposition lifts to a
         full rank-(n+3) decomposition of T<3,3,3>, verified coordinatewise.

Every accepted object is stored with its own verification record.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import time
from pathlib import Path

import numpy as np

import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
from quotient_saturation_incidence import (  # noqa: E402
    full_tensor, quotient_tensor, mat_rank, codim1_ranks,
)


# ---------------------------------------------------------------- Wang rows

def load_rows(path: Path) -> tuple[list[int], list[int]]:
    raw = path.read_bytes()
    assert raw[:8] == b"E11WANG1", raw[:8]
    nrows = int.from_bytes(raw[8:16], "little")
    rec = 36
    off = 16
    masks, caps = [], []
    for _ in range(nrows):
        m = int.from_bytes(raw[off:off + 32], "little")
        cap = int.from_bytes(raw[off + 32:off + 36], "little", signed=True)
        masks.append(m)
        caps.append(cap)
        off += rec
    return masks, caps


def mask_points(m: int) -> list[int]:
    pts = []
    x = m
    while x:
        b = (x & -x).bit_length() - 1
        pts.append(b)
        x ^= 1 << b
    return pts


# ---------------------------------------------------------------- stage 1

def generate_supports(masks, caps, line_caps, n, want, seed, per_sol_sec, blocked):
    from ortools.sat.python import cp_model
    model = cp_model.CpModel()
    m = [model.NewIntVar(0, int(line_caps.get(q, 1)), f"m{q}") for q in range(256)]
    model.Add(m[0] == 0)
    model.Add(sum(m[1:]) == n)
    kept = 0
    for mask, cap in zip(masks, caps):
        pts = [p for p in mask_points(mask) if p >= 1]
        if not pts:
            continue
        if cap >= n:
            continue
        model.Add(sum(m[p] for p in pts) <= int(cap))
        kept += 1
    for sup in blocked:
        cnt = {}
        for q in sup:
            cnt[q] = cnt.get(q, 0) + 1
        lits = []
        for q, c in cnt.items():
            b = model.NewBoolVar("")
            model.Add(m[q] != c).OnlyEnforceIf(b)
            model.Add(m[q] == c).OnlyEnforceIf(b.Not())
            lits.append(b)
        model.AddBoolOr(lits)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = per_sol_sec
    solver.parameters.random_seed = seed
    solver.parameters.num_workers = 8
    solver.parameters.randomize_search = True
    solver.parameters.search_branching = cp_model.PORTFOLIO_SEARCH
    st = solver.Solve(model)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return None, solver.StatusName(st), kept
    sup = []
    for q in range(1, 256):
        v = solver.Value(m[q])
        sup.extend([q] * v)
    return sup, solver.StatusName(st), kept


def check_support_rows(masks, caps, sup, n):
    cnt = {}
    for q in sup:
        cnt[q] = cnt.get(q, 0) + 1
    viol = 0
    for mask, cap in zip(masks, caps):
        s = 0
        for q, c in cnt.items():
            if (mask >> q) & 1:
                s += c
        if s > cap:
            viol += 1
    return viol


# ---------------------------------------------------------------- stage 2

def rank_int(rows) -> int:
    basis = {}
    r = 0
    for row in rows:
        x = int(row)
        while x:
            p = x.bit_length() - 1
            b = basis.get(p)
            if b is None:
                basis[p] = x
                r += 1
                break
            x ^= b
    return r


def generalized_inverse(M: np.ndarray):
    A = (M.copy() & 1).astype(np.uint8)
    n = A.shape[0]
    P = np.eye(n, dtype=np.uint8)
    Qm = np.eye(n, dtype=np.uint8)
    r = 0
    while r < n:
        piv = None
        for i in range(r, n):
            for j in range(r, n):
                if A[i, j]:
                    piv = (i, j)
                    break
            if piv:
                break
        if piv is None:
            break
        i0, j0 = piv
        if i0 != r:
            A[[r, i0]] = A[[i0, r]]
            P[[r, i0]] = P[[i0, r]]
        if j0 != r:
            A[:, [r, j0]] = A[:, [j0, r]]
            Qm[:, [r, j0]] = Qm[:, [j0, r]]
        for i in range(n):
            if i != r and A[i, r]:
                A[i] ^= A[r]
                P[i] ^= P[r]
        for j in range(n):
            if j != r and A[r, j]:
                A[:, j] ^= A[:, r]
                Qm[:, j] ^= Qm[:, r]
        r += 1
    Dp = np.zeros((n, n), dtype=np.uint8)
    for i in range(r):
        Dp[i, i] = 1
    G = ((Qm @ Dp @ P) & 1).astype(np.uint8)
    if not np.array_equal((M @ G @ M) & 1, M & 1):
        raise RuntimeError("generalized inverse failed")
    # left null space of M: rows f with f^T M = 0; right null space g with M g = 0
    return G, int(r)


def nullspaces(M: np.ndarray):
    """Return basis of left-null (f^T M = 0) and right-null (M g = 0)."""
    def rn(A):
        A = (A.copy() & 1).astype(np.uint8)
        m, n = A.shape
        piv_cols = []
        r = 0
        for c in range(n):
            p = None
            for i in range(r, m):
                if A[i, c]:
                    p = i
                    break
            if p is None:
                continue
            if p != r:
                A[[r, p]] = A[[p, r]]
            for i in range(m):
                if i != r and A[i, c]:
                    A[i] ^= A[r]
            piv_cols.append(c)
            r += 1
        free = [c for c in range(n) if c not in piv_cols]
        basis = []
        for fc in free:
            v = np.zeros(n, dtype=np.uint8)
            v[fc] = 1
            for i, pc in enumerate(piv_cols):
                if A[i, fc]:
                    v[pc] = 1
            basis.append(v)
        return basis
    right = rn(M)
    left = rn(M.T & 1)
    return left, right


def trace_filter(Q: np.ndarray, support: list[int], ranks: dict[int, int]) -> dict:
    t0 = time.time()
    nt = len(support)
    nvars = 81 * nt
    rows, rhs = [], []
    for s in range(8):
        act = [t for t, u in enumerate(support) if (u >> s) & 1]
        for b in range(9):
            for c in range(9):
                x = 0
                loc = 9 * b + c
                for t in act:
                    x |= 1 << (81 * t + loc)
                rows.append(x)
                rhs.append(int(Q[s, b, c]))
    n_tensor = len(rows)
    tight = []
    for lam in range(1, 256):
        act = [t for t, u in enumerate(support) if ((lam & u).bit_count() & 1)]
        r = ranks[lam]
        if r == 0 or len(act) != r:
            continue
        M = np.zeros((9, 9), dtype=np.uint8)
        for s in range(8):
            if (lam >> s) & 1:
                M ^= Q[s]
        G, rr = generalized_inverse(M)
        left, right = nullspaces(M)
        tight.append({"lambda": lam, "rank": rr, "active": act})
        for t in act:
            base = 81 * t
            # trace(G X_t) = 1
            x = 0
            for i in range(9):
                for j in range(9):
                    if G[j, i] & 1:
                        x |= 1 << (base + 9 * i + j)
            rows.append(x)
            rhs.append(1)
            # f^T X_t = 0 for f in left null space  (v_t in col M)
            for f in left:
                for c in range(9):
                    x = 0
                    for i in range(9):
                        if f[i]:
                            x |= 1 << (base + 9 * i + c)
                    rows.append(x)
                    rhs.append(0)
            # X_t g = 0 for g in right null space  (w_t in row M)
            for g in right:
                for i in range(9):
                    x = 0
                    for c in range(9):
                        if g[c]:
                            x |= 1 << (base + 9 * i + c)
                    rows.append(x)
                    rhs.append(0)
    r1 = rank_int(rows)
    aug = [row | ((b & 1) << nvars) for row, b in zip(rows, rhs)]
    r2 = rank_int(aug)
    return {
        "consistent": r1 == r2,
        "rank_aug": [r1, r2],
        "tight_count": len(tight),
        "tight_ranks": sorted(t["rank"] for t in tight),
        "tensor_equations": n_tensor,
        "extra_equations": len(rows) - n_tensor,
        "elapsed_sec": time.time() - t0,
    }


# ---------------------------------------------------------------- stage 3

def build_fixed_a_cnf(Q: np.ndarray, support: list[int], path: Path) -> dict:
    nt = len(support)
    nv = 0

    def newv():
        nonlocal nv
        nv += 1
        return nv

    V = [[newv() for _ in range(9)] for _ in range(nt)]
    W = [[newv() for _ in range(9)] for _ in range(nt)]
    clauses: list[list[int]] = []
    prod: dict[tuple[int, int, int], int] = {}

    def get_prod(t, b, c):
        key = (t, b, c)
        if key in prod:
            return prod[key]
        p = newv()
        prod[key] = p
        clauses.append([-p, V[t][b]])
        clauses.append([-p, W[t][c]])
        clauses.append([-V[t][b], -W[t][c], p])
        return p

    def xor_eq(lits, val):
        # chain
        if not lits:
            return
        cur = lits[0]
        for nxt in lits[1:]:
            z = newv()
            clauses.append([-z, cur, nxt])
            clauses.append([-z, -cur, -nxt])
            clauses.append([z, -cur, nxt])
            clauses.append([z, cur, -nxt])
            cur = z
        clauses.append([cur] if val else [-cur])

    for s in range(8):
        act = [t for t, u in enumerate(support) if (u >> s) & 1]
        for b in range(9):
            for c in range(9):
                lits = [get_prod(t, b, c) for t in act]
                if not lits:
                    if Q[s, b, c]:
                        clauses.append([])  # unsat
                    continue
                xor_eq(lits, int(Q[s, b, c]))
    # nonzero v,w per term
    for t in range(nt):
        clauses.append([V[t][b] for b in range(9)])
        clauses.append([W[t][c] for c in range(9)])
    lines = [f"p cnf {nv} {len(clauses)}"]
    for cl in clauses:
        lines.append(" ".join(str(x) for x in cl) + " 0")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n")
    return {"vars": nv, "clauses": len(clauses), "V": V, "W": W}


def solve_cnf(path: Path, timeout: int) -> tuple[str, dict]:
    try:
        r = subprocess.run(["cadical", "-q", str(path)], capture_output=True,
                           text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "TIMEOUT", {}
    out = r.stdout
    if r.returncode == 10:
        assign = {}
        for line in out.splitlines():
            if line.startswith("v "):
                for tok in line[2:].split():
                    v = int(tok)
                    if v == 0:
                        continue
                    assign[abs(v)] = v > 0
        return "SAT", assign
    if r.returncode == 20:
        return "UNSAT", {}
    return f"UNKNOWN_rc{r.returncode}", {}


def verify_quotient(Q, support, vvecs, wvecs) -> bool:
    R = np.zeros_like(Q)
    for t, u in enumerate(support):
        outer = np.outer(vvecs[t], wvecs[t]) & 1
        for s in range(8):
            if (u >> s) & 1:
                R[s] ^= outer
    return bool(np.array_equal(R & 1, Q & 1))


# ---------------------------------------------------------------- stage 4 lift

def lift_e11(support, vvecs, wvecs) -> dict:
    """pivot=1 (E11): quotient A index q (1..255) corresponds to full A mask q<<1.
    The deleted slice T[a_bit=0] must be added back; it has rank 3."""
    T = full_tensor()
    S0 = T[0].copy()
    r = mat_rank(S0)
    # decompose S0 into r rank-one terms by row reduction
    A = (S0.copy() & 1).astype(np.uint8)
    terms = []
    # Gaussian: S0 = sum e_i * row_i for pivot rows
    for i in range(9):
        if A[i].any():
            e = np.zeros(9, dtype=np.uint8)
            e[i] = 1
            terms.append((e, A[i].copy()))
    if len(terms) != r:
        # fall back: full row list still reconstructs S0
        pass
    chk = np.zeros((9, 9), dtype=np.uint8)
    for e, row in terms:
        chk ^= np.outer(e, row) & 1
    assert np.array_equal(chk, S0 & 1), "slice split failed"
    full_a, full_v, full_w = [], [], []
    for t, q in enumerate(support):
        full_a.append(int(q) << 1)
        full_v.append(vvecs[t])
        full_w.append(wvecs[t])
    for e, row in terms:
        full_a.append(1)
        full_v.append(e)
        full_w.append(row)
    R = np.zeros((9, 9, 9), dtype=np.uint8)
    for t in range(len(full_a)):
        outer = np.outer(full_v[t], full_w[t]) & 1
        for s in range(9):
            if (full_a[t] >> s) & 1:
                R[s] ^= outer
    ok = bool(np.array_equal(R & 1, T & 1))
    return {"rank": len(full_a), "verified": ok, "slice_terms": len(terms),
            "A": [int(x) for x in full_a],
            "V": [[int(x) for x in v] for v in full_v],
            "W": [[int(x) for x in w] for w in full_w]}


# ---------------------------------------------------------------- driver

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot", type=int, required=True)
    ap.add_argument("--pivot-name", default="")
    ap.add_argument("--rows", type=Path, required=True)
    ap.add_argument("--n", type=int, default=19)
    ap.add_argument("--trials", type=int, default=20)
    ap.add_argument("--cpsat-sec", type=float, default=60.0)
    ap.add_argument("--sat-sec", type=int, default=60)
    ap.add_argument("--outdir", type=Path, required=True)
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args()

    args.outdir.mkdir(parents=True, exist_ok=True)
    Q = quotient_tensor(args.pivot)
    ranks = codim1_ranks(Q)
    masks, caps = load_rows(args.rows)
    line_caps = {}
    for q in range(1, 256):
        line_caps[q] = args.n - max(1, ranks[q] if False else 0)
    # correct line cap: multiplicity of q is bounded by cap of the 2-dim original
    # subspace <p,a>, which equals the quotient point-row cap in the binary.
    pt_cap = {}
    for mask, cap in zip(masks, caps):
        pts = [p for p in mask_points(mask) if p >= 1]
        if len(pts) == 1:
            pt_cap[pts[0]] = min(pt_cap.get(pts[0], 10**9), cap)
    for q in range(1, 256):
        line_caps[q] = max(0, args.n - (args.n - pt_cap.get(q, args.n - 1)))
    # multiplicity bound for q: q may repeat up to (n - cap_of_complement)?  Use
    # the direct bound: any row U containing q gives m_q <= cap_U.
    mult_bound = {q: args.n for q in range(1, 256)}
    for mask, cap in zip(masks, caps):
        for p in mask_points(mask):
            if p >= 1 and cap < mult_bound[p]:
                mult_bound[p] = cap
    line_caps = mult_bound

    summary = {"pivot": args.pivot, "pivot_name": args.pivot_name, "n": args.n,
               "rows": str(args.rows), "trials": args.trials,
               "line_cap_hist": {}, "records": []}
    from collections import Counter
    summary["line_cap_hist"] = dict(sorted(Counter(line_caps.values()).items()))

    blocked: list[list[int]] = []
    t_start = time.time()
    for trial in range(args.trials):
        sup, status, kept = generate_supports(masks, caps, line_caps, args.n,
                                             1, args.seed + trial,
                                             args.cpsat_sec, blocked)
        rec = {"trial": trial, "cpsat_status": status, "rows_kept": kept}
        if sup is None:
            rec["note"] = "no support from CP-SAT"
            summary["records"].append(rec)
            if status == "INFEASIBLE":
                rec["note"] = "CP-SAT INFEASIBLE: no Wang-admissible support remains"
                break
            continue
        rec["support"] = sup
        rec["distinct"] = len(set(sup))
        viol = check_support_rows(masks, caps, sup, args.n)
        rec["full_row_violations"] = viol
        blocked.append(sup)
        if viol:
            rec["note"] = "not fully admissible"
            summary["records"].append(rec)
            continue
        tf = trace_filter(Q, sup, ranks)
        rec["trace"] = tf
        if not tf["consistent"]:
            rec["note"] = "rejected by tight-contraction filter"
            summary["records"].append(rec)
            continue
        cnf = args.outdir / f"fixedA_trial{trial:03d}.cnf"
        info = build_fixed_a_cnf(Q, sup, cnf)
        rec["cnf"] = {"path": str(cnf), "vars": info["vars"], "clauses": info["clauses"]}
        st, assign = solve_cnf(cnf, args.sat_sec)
        rec["sat_status"] = st
        if st == "SAT":
            nt = len(sup)
            vv = [np.array([1 if assign.get(info["V"][t][b], False) else 0
                            for b in range(9)], dtype=np.uint8) for t in range(nt)]
            ww = [np.array([1 if assign.get(info["W"][t][c], False) else 0
                            for c in range(9)], dtype=np.uint8) for t in range(nt)]
            ok = verify_quotient(Q, sup, vv, ww)
            rec["quotient_verified"] = ok
            if ok:
                out = {"pivot": args.pivot, "support": sup,
                       "V": [[int(x) for x in v] for v in vv],
                       "W": [[int(x) for x in w] for w in ww]}
                p = args.outdir / f"quotient_decomp_trial{trial:03d}.json"
                p.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
                rec["quotient_decomp"] = str(p)
                if args.pivot == 1:
                    lift = lift_e11(sup, vv, ww)
                    lp = args.outdir / f"full_lift_trial{trial:03d}.json"
                    lp.write_text(json.dumps(lift, indent=2, sort_keys=True) + "\n")
                    rec["lift"] = {"rank": lift["rank"], "verified": lift["verified"],
                                   "path": str(lp)}
        summary["records"].append(rec)
        if rec.get("lift", {}).get("verified"):
            summary["BREAKTHROUGH"] = f"verified full rank-{rec['lift']['rank']} decomposition"
            break
    summary["elapsed_sec"] = time.time() - t_start
    out = args.outdir / "pipeline_summary.json"
    out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    brief = {k: v for k, v in summary.items() if k != "records"}
    brief["record_count"] = len(summary["records"])
    brief["admissible_found"] = sum(1 for r in summary["records"]
                                    if r.get("full_row_violations") == 0)
    brief["trace_rejected"] = sum(1 for r in summary["records"]
                                  if r.get("trace") and not r["trace"]["consistent"])
    brief["sat_status_hist"] = dict(Counter(r.get("sat_status", "-")
                                            for r in summary["records"]))
    print(json.dumps(brief, indent=2, sort_keys=True))
    print(f"Saved {out}")


if __name__ == "__main__":
    main()
