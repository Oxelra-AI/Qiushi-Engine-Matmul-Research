#!/usr/bin/env python3
"""Enumerate Wang-admissible rank-2 supports and apply enhanced trace filter.

Goal: measure how many distinct rank-2 n=19 supports exist (up to stabilizer).
Each found support is tested by the enhanced trace+nullspace filter.
"""
from __future__ import annotations
import argparse, json, struct, time
from pathlib import Path
from collections import Counter
import numpy as np
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))


def quotient_tensor(pivot):
    T = np.zeros((9,9,9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    h = int(pivot).bit_length() - 1
    Q = np.zeros((8,9,9), dtype=np.uint8)
    for a_bit in range(9):
        qa = 1 << a_bit
        if (qa >> h) & 1: qa ^= int(pivot)
        low = qa & ((1 << h) - 1)
        high = (qa >> (h+1)) << h
        q_idx = low | high
        if q_idx:
            for qb in range(8):
                if (q_idx >> qb) & 1:
                    Q[qb] ^= T[a_bit]
    return Q


def mat_rank(M):
    A = (M.copy() & 1).astype(np.uint8)
    m, n = A.shape; r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i, c]: piv = i; break
        if piv is None: continue
        if piv != r: A[[r, piv]] = A[[piv, r]]
        for i in range(m):
            if i != r and A[i, c]: A[i] ^= A[r]
        r += 1
        if r == m: break
    return int(r)


def load_rows(path):
    raw = path.read_bytes()
    assert raw[:8] == b"E11WANG1"
    nrows = int.from_bytes(raw[8:16], "little")
    masks, caps = [], []
    off = 16
    for _ in range(nrows):
        m = int.from_bytes(raw[off:off+32], "little")
        cap = int.from_bytes(raw[off+32:off+36], "little", signed=True)
        masks.append(m); caps.append(cap)
        off += 36
    return masks, caps


def mask_pts(m):
    pts = []; x = m
    while x:
        b = (x & -x).bit_length() - 1
        pts.append(b); x ^= 1 << b
    return pts


def check_all_rows(masks, caps, sup):
    cnt = Counter(sup)
    violated = []
    for i, (mask, cap) in enumerate(zip(masks, caps)):
        s = sum(cnt[p] for p in mask_pts(mask) if p in cnt)
        if s > cap: violated.append(i)
    return violated


def generalized_inverse(M):
    A = (M.copy() & 1).astype(np.uint8)
    n = A.shape[0]
    P = np.eye(n, dtype=np.uint8)
    Qm = np.eye(n, dtype=np.uint8)
    r = 0
    while r < n:
        piv = None
        for i in range(r, n):
            for j in range(r, n):
                if A[i,j]: piv = (i,j); break
            if piv: break
        if piv is None: break
        i0, j0 = piv
        if i0 != r: A[[r,i0]] = A[[i0,r]]; P[[r,i0]] = P[[i0,r]]
        if j0 != r: A[:,[r,j0]] = A[:,[j0,r]]; Qm[:,[r,j0]] = Qm[:,[j0,r]]
        for i in range(n):
            if i != r and A[i,r]: A[i] ^= A[r]; P[i] ^= P[r]
        for j in range(n):
            if j != r and A[r,j]: A[:,j] ^= A[:,r]; Qm[:,j] ^= Qm[:,r]
        r += 1
    Dp = np.zeros((n,n), dtype=np.uint8)
    for i in range(r): Dp[i,i] = 1
    G = ((Qm @ Dp @ P) & 1).astype(np.uint8)
    return G, int(r)


def nullspace(M):
    A = (M.copy() & 1).astype(np.uint8)
    m, n = A.shape; pivs = []; r = 0
    for c in range(n):
        p = None
        for i in range(r, m):
            if A[i, c]: p = i; break
        if p is None: continue
        if p != r: A[[r, p]] = A[[p, r]]
        for i in range(m):
            if i != r and A[i, c]: A[i] ^= A[r]
        pivs.append(c); r += 1
    free = [c for c in range(n) if c not in pivs]
    basis = []
    for fc in free:
        v = np.zeros(n, dtype=np.uint8); v[fc] = 1
        for i, pc in enumerate(pivs):
            if A[i, fc]: v[pc] = 1
        basis.append(v)
    return basis


def rank_int(rows):
    basis = {}; r = 0
    for row in rows:
        x = int(row)
        while x:
            p = x.bit_length() - 1
            b = basis.get(p)
            if b is None: basis[p] = x; r += 1; break
            x ^= b
    return r


def enhanced_trace_filter(Q, support, ranks):
    """Trace + left/right nullspace filter."""
    nt = len(support); nvars = 81 * nt
    rows, rhs = [], []
    for s in range(8):
        act = [t for t, u in enumerate(support) if (u >> s) & 1]
        for b in range(9):
            for c in range(9):
                x = 0
                for t in act: x |= 1 << (81*t + 9*b + c)
                rows.append(x); rhs.append(int(Q[s,b,c]))
    n_tensor = len(rows)
    tight_count = 0
    for lam in range(1, 256):
        act = [t for t, u in enumerate(support) if ((lam & u).bit_count() & 1)]
        r = ranks[lam]
        if r == 0 or len(act) != r: continue
        tight_count += 1
        M = np.zeros((9,9), dtype=np.uint8)
        for s in range(8):
            if (lam >> s) & 1: M ^= Q[s]
        G, rr = generalized_inverse(M)
        left_n = nullspace(M.T & 1)
        right_n = nullspace(M)
        for t in act:
            base = 81 * t
            # trace(G X_t) = 1
            x = 0
            for i in range(9):
                for j in range(9):
                    if G[j,i] & 1: x |= 1 << (base + 9*i + j)
            rows.append(x); rhs.append(1)
            # nullspace conditions
            for f in left_n:
                for c in range(9):
                    x = 0
                    for i in range(9):
                        if f[i]: x |= 1 << (base + 9*i + c)
                    rows.append(x); rhs.append(0)
            for g in right_n:
                for i in range(9):
                    x = 0
                    for c in range(9):
                        if g[c]: x |= 1 << (base + 9*i + c)
                    rows.append(x); rhs.append(0)
    r1 = rank_int(rows)
    aug = [row | ((b & 1) << nvars) for row, b in zip(rows, rhs)]
    r2 = rank_int(aug)
    return {"consistent": r1 == r2, "rank_aug": [r1, r2],
            "tight_count": tight_count, "extra_eq": len(rows) - n_tensor}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot", type=int, default=17)
    ap.add_argument("--pivot-name", default="rank2")
    ap.add_argument("--rows", type=Path, required=True)
    ap.add_argument("--n", type=int, default=19)
    ap.add_argument("--max-supports", type=int, default=200)
    ap.add_argument("--per-sol-sec", type=float, default=120)
    ap.add_argument("--max-cap-init", type=int, default=2)
    ap.add_argument("--outdir", type=Path, required=True)
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)

    Q = quotient_tensor(args.pivot)
    ranks = {}
    for lam in range(1, 256):
        M = np.zeros((9,9), dtype=np.uint8)
        for s in range(8):
            if (lam >> s) & 1: M ^= Q[s]
        ranks[lam] = mat_rank(M)

    masks, caps = load_rows(args.rows)
    # For rank-2/rank-3 at n=19: all line caps = 1, so binary variables
    init_idx = set(i for i, c in enumerate(caps) if 0 < c <= args.max_cap_init)

    from ortools.sat.python import cp_model

    blocked_sets = []
    records = []
    t_start = time.time()

    for trial in range(args.max_supports):
        if time.time() - t_start > 3600:
            break
        # CEGAR loop
        active_idx = set(init_idx)
        sup = None
        cegar_rounds = 0
        for rnd in range(30):
            model = cp_model.CpModel()
            m = {q: model.new_bool_var(f"x{q}") for q in range(1, 256)}
            model.add(sum(m.values()) == args.n)
            for i in active_idx:
                pts = [p for p in mask_pts(masks[i]) if p >= 1]
                if pts and caps[i] < args.n:
                    model.add(sum(m[p] for p in pts if p in m) <= int(caps[i]))
            for bs in blocked_sets:
                lits = [m[q].negated() for q in bs]
                model.add_bool_or(lits)
            solver = cp_model.CpSolver()
            solver.parameters.max_time_in_seconds = args.per_sol_sec
            solver.parameters.random_seed = args.seed + trial * 37 + rnd
            solver.parameters.num_workers = 8
            solver.parameters.randomize_search = True
            solver.parameters.search_branching = cp_model.PORTFOLIO_SEARCH
            st = solver.solve(model)
            cegar_rounds = rnd + 1
            if st == cp_model.INFEASIBLE:
                sup = None; break
            if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
                sup = None; break
            found = sorted(q for q in range(1, 256) if solver.value(m[q]))
            viols = check_all_rows(masks, caps, found)
            if not viols:
                sup = found; break
            for vi in viols:
                active_idx.add(vi)
        rec = {"trial": trial, "cegar_rounds": cegar_rounds}
        if sup is None:
            if st == cp_model.INFEASIBLE:
                rec["status"] = "ALL_EXHAUSTED"
                records.append(rec)
                print(f"Trial {trial}: ALL SUPPORTS EXHAUSTED")
                break
            rec["status"] = "NO_SUPPORT"
            records.append(rec)
            print(f"Trial {trial}: no support found")
            continue
        rec["support"] = sup
        rec["status"] = "ADMISSIBLE"
        blocked_sets.append(set(sup))
        # trace filter
        tf = enhanced_trace_filter(Q, sup, ranks)
        rec["trace_consistent"] = tf["consistent"]
        rec["trace_rank_aug"] = tf["rank_aug"]
        rec["trace_tight"] = tf["tight_count"]
        rec["trace_extra_eq"] = tf["extra_eq"]
        records.append(rec)
        status_str = "PASS" if tf["consistent"] else "REJECT"
        print(f"Trial {trial}: support found, trace {status_str} "
              f"(tight={tf['tight_count']}, rank_aug={tf['rank_aug']}), "
              f"elapsed={time.time()-t_start:.1f}s")

    n_admissible = sum(1 for r in records if r.get("status") == "ADMISSIBLE")
    n_trace_pass = sum(1 for r in records if r.get("trace_consistent"))
    n_trace_fail = sum(1 for r in records if r.get("trace_consistent") is False)
    exhausted = any(r.get("status") == "ALL_EXHAUSTED" for r in records)
    summary = {
        "pivot": args.pivot, "pivot_name": args.pivot_name, "n": args.n,
        "supports_found": n_admissible,
        "trace_pass": n_trace_pass, "trace_reject": n_trace_fail,
        "all_exhausted": exhausted,
        "elapsed_sec": time.time() - t_start,
        "records": records,
    }
    out = args.outdir / "rank2_support_census.json"
    out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    brief = {k: v for k, v in summary.items() if k != "records"}
    print(f"\n{'='*60}")
    print(json.dumps(brief, indent=2, sort_keys=True))
    print(f"Saved {out}")


if __name__ == "__main__":
    main()
