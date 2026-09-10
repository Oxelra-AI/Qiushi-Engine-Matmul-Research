#!/usr/bin/env python3
"""E11 CEGAR construction pipeline: find Wang-admissible supports, trace-filter, complete.

Key differences from the failed pipeline:
1. CEGAR start with cap<=2 rows, iteratively add violated rows
2. Handles E11 multiplicities (6 directions can repeat)
3. Uses trace+nullspace filter before expensive SAT
4. Blocks previously found supports
"""
from __future__ import annotations
import argparse, json, struct, subprocess, time
from pathlib import Path
from collections import Counter
import numpy as np
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))


def quotient_tensor(pivot: int) -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    h = int(pivot).bit_length() - 1
    Q = np.zeros((8, 9, 9), dtype=np.uint8)
    for a_bit in range(9):
        qa = 1 << a_bit
        if (qa >> h) & 1:
            qa ^= int(pivot)
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
        masks.append(m)
        caps.append(cap)
        off += 36
    return masks, caps


def mask_pts(m):
    pts = []
    x = m
    while x:
        b = (x & -x).bit_length() - 1
        pts.append(b)
        x ^= 1 << b
    return pts


def check_all_rows(masks, caps, sup):
    cnt = Counter(sup)
    violated_idx = []
    for i, (mask, cap) in enumerate(zip(masks, caps)):
        s = sum(cnt[p] for p in mask_pts(mask) if p >= 1 and p in cnt)
        if s > cap:
            violated_idx.append(i)
    return violated_idx


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
                if A[i, j]: piv = (i, j); break
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
    """Return basis of right null space of M over F2."""
    A = (M.copy() & 1).astype(np.uint8)
    m, n = A.shape
    pivs = []
    r = 0
    for c in range(n):
        p = None
        for i in range(r, m):
            if A[i, c]: p = i; break
        if p is None: continue
        if p != r: A[[r, p]] = A[[p, r]]
        for i in range(m):
            if i != r and A[i, c]: A[i] ^= A[r]
        pivs.append(c)
        r += 1
    free = [c for c in range(n) if c not in pivs]
    basis = []
    for fc in free:
        v = np.zeros(n, dtype=np.uint8)
        v[fc] = 1
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


def trace_nullspace_filter(Q, support, ranks):
    """Enhanced trace + nullspace filter (strengthening)."""
    t0 = time.time()
    nt = len(support)
    nvars = 81 * nt
    rows, rhs = [], []
    for s in range(8):
        act = [t for t, u in enumerate(support) if (u >> s) & 1]
        for b in range(9):
            for c in range(9):
                x = 0
                for t in act: x |= 1 << (81*t + 9*b + c)
                rows.append(x); rhs.append(int(Q[s,b,c]))
    n_tensor = len(rows)
    tight_info = []
    for lam in range(1, 256):
        act = [t for t, u in enumerate(support) if ((lam & u).bit_count() & 1)]
        r = ranks[lam]
        if r == 0 or len(act) != r: continue
        M = np.zeros((9,9), dtype=np.uint8)
        for s in range(8):
            if (lam >> s) & 1: M ^= Q[s]
        G, rr = generalized_inverse(M)
        left_null = nullspace(M.T & 1)  # f with f^T M = 0
        right_null = nullspace(M)       # g with M g = 0
        tight_info.append({"lambda": lam, "rank": rr, "active": act,
                          "G": G, "left_null": left_null, "right_null": right_null})
        for t in act:
            base = 81 * t
            # trace(G X_t) = 1
            x = 0
            for i in range(9):
                for j in range(9):
                    if G[j, i] & 1: x |= 1 << (base + 9*i + j)
            rows.append(x); rhs.append(1)
            # f^T X_t = 0 for each f in left null space
            for f in left_null:
                for c in range(9):
                    x = 0
                    for i in range(9):
                        if f[i]: x |= 1 << (base + 9*i + c)
                    rows.append(x); rhs.append(0)
            # X_t g = 0 for each g in right null space
            for g in right_null:
                for i in range(9):
                    x = 0
                    for c in range(9):
                        if g[c]: x |= 1 << (base + 9*i + c)
                    rows.append(x); rhs.append(0)
    r1 = rank_int(rows)
    aug = [row | ((b & 1) << nvars) for row, b in zip(rows, rhs)]
    r2 = rank_int(aug)
    return {
        "consistent": r1 == r2,
        "rank_aug": [r1, r2],
        "tight_count": len(tight_info),
        "tight_ranks": sorted(Counter(t["rank"] for t in tight_info).items()),
        "tensor_eq": n_tensor,
        "extra_eq": len(rows) - n_tensor,
        "elapsed_sec": time.time() - t0,
    }


def build_e11_cnf(Q, support, path):
    nt = len(support); nv = 0
    def newv():
        nonlocal nv; nv += 1; return nv
    V = [[newv() for _ in range(9)] for _ in range(nt)]
    W = [[newv() for _ in range(9)] for _ in range(nt)]
    clauses = []
    prod = {}
    def get_prod(t, b, c):
        key = (t, b, c)
        if key in prod: return prod[key]
        p = newv(); prod[key] = p
        clauses.append([-p, V[t][b]]); clauses.append([-p, W[t][c]])
        clauses.append([-V[t][b], -W[t][c], p])
        return p
    def xor_eq(lits, val):
        if not lits: return
        cur = lits[0]
        for nxt in lits[1:]:
            z = newv()
            clauses.extend([[-z,cur,nxt],[-z,-cur,-nxt],[z,-cur,nxt],[z,cur,-nxt]])
            cur = z
        clauses.append([cur] if val else [-cur])
    for s in range(8):
        act = [t for t, u in enumerate(support) if (u >> s) & 1]
        for b in range(9):
            for c in range(9):
                lits = [get_prod(t, b, c) for t in act]
                if not lits:
                    if Q[s, b, c]: clauses.append([])
                    continue
                xor_eq(lits, int(Q[s, b, c]))
    for t in range(nt):
        clauses.append([V[t][b] for b in range(9)])
        clauses.append([W[t][c] for c in range(9)])
    lines = [f"p cnf {nv} {len(clauses)}"]
    for cl in clauses: lines.append(" ".join(str(x) for x in cl) + " 0")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n")
    return {"vars": nv, "clauses": len(clauses), "V": V, "W": W}


def solve_cnf(path, timeout):
    try:
        r = subprocess.run(["cadical", "-q", str(path)], capture_output=True,
                          text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "TIMEOUT", {}
    if r.returncode == 10:
        assign = {}
        for line in r.stdout.splitlines():
            if line.startswith("v "):
                for tok in line[2:].split():
                    v = int(tok)
                    if v: assign[abs(v)] = v > 0
        return "SAT", assign
    if r.returncode == 20:
        return "UNSAT", {}
    return f"UNKNOWN_rc{r.returncode}", {}


def verify_quotient(Q, support, vv, ww):
    R = np.zeros_like(Q)
    for t, u in enumerate(support):
        outer = np.outer(vv[t], ww[t]) & 1
        for s in range(8):
            if (u >> s) & 1: R[s] ^= outer
    return bool(np.array_equal(R & 1, Q & 1))


def lift_e11(support, vv, ww):
    T = np.zeros((9,9,9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    S0 = T[0].copy()
    A = (S0.copy() & 1).astype(np.uint8)
    terms = []
    for i in range(9):
        if A[i].any():
            e = np.zeros(9, dtype=np.uint8); e[i] = 1
            terms.append((e, A[i].copy()))
            for j in range(9):
                if j != i and A[j, :].any():
                    row_i = A[i]
                    # Check if row j is affected
                    pass
            for j in range(i+1, 9):
                if A[j].any():
                    # eliminate using pivot row i
                    overlap = False
                    for c in range(9):
                        if A[i, c] and A[j, c]:
                            overlap = True; break
                    if overlap:
                        A[j] ^= A[i]
    # Verify reconstruction
    chk = np.zeros((9,9), dtype=np.uint8)
    for e, row in terms:
        chk ^= np.outer(e, row) & 1
    if not np.array_equal(chk, S0 & 1):
        # fallback: use standard row reduction
        A2 = (S0.copy() & 1).astype(np.uint8)
        terms = []
        r = 0
        for c in range(9):
            piv = None
            for i in range(r, 9):
                if A2[i, c]: piv = i; break
            if piv is None: continue
            if piv != r: A2[[r, piv]] = A2[[piv, r]]
            for i in range(9):
                if i != r and A2[i, c]: A2[i] ^= A2[r]
            e = np.zeros(9, dtype=np.uint8); e[r] = 1
            terms.append((e, A2[r].copy()))
            r += 1
        chk = np.zeros((9,9), dtype=np.uint8)
        for e, row in terms:
            chk ^= np.outer(e, row) & 1
        assert np.array_equal(chk, S0 & 1)

    full_a, full_v, full_w = [], [], []
    for t, q in enumerate(support):
        full_a.append(int(q) << 1)
        full_v.append(vv[t])
        full_w.append(ww[t])
    for e, row in terms:
        full_a.append(1)
        full_v.append(e)
        full_w.append(row)
    R = np.zeros((9,9,9), dtype=np.uint8)
    for t in range(len(full_a)):
        outer = np.outer(full_v[t], full_w[t]) & 1
        for s in range(9):
            if (full_a[t] >> s) & 1: R[s] ^= outer
    ok = bool(np.array_equal(R & 1, T & 1))
    return {"rank": len(full_a), "verified": ok, "lift_terms": len(terms),
            "A": [int(x) for x in full_a]}


def cegar_find_support(masks, caps, n, mult_bound, seed, max_sec, blocked,
                       max_cap_init=2):
    """CEGAR: start with cap<=max_cap_init rows, iterate."""
    from ortools.sat.python import cp_model
    # select initial rows
    init_idx = [i for i, c in enumerate(caps) if 0 < c <= max_cap_init]
    active_idx = set(init_idx)
    round_log = []
    t0 = time.time()
    for rnd in range(50):
        if time.time() - t0 > max_sec:
            return None, round_log, "TIMEOUT"
        model = cp_model.CpModel()
        m = [model.new_int_var(0, int(mult_bound.get(q, 0)), f"m{q}") for q in range(256)]
        model.add(m[0] == 0)
        model.add(sum(m[1:]) == n)
        for i in active_idx:
            pts = [p for p in mask_pts(masks[i]) if p >= 1]
            if pts and caps[i] < n:
                model.add(sum(m[p] for p in pts) <= int(caps[i]))
        for sup in blocked:
            cnt = Counter(sup)
            lits = []
            for q, c in cnt.items():
                b = model.new_bool_var("")
                model.add(m[q] != c).only_enforce_if(b)
                model.add(m[q] == c).only_enforce_if(b.negated())
                lits.append(b)
            model.add_bool_or(lits)
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = min(120, max_sec - (time.time() - t0))
        solver.parameters.random_seed = seed + rnd
        solver.parameters.num_workers = 8
        solver.parameters.randomize_search = True
        solver.parameters.search_branching = cp_model.PORTFOLIO_SEARCH
        st = solver.solve(model)
        if st == cp_model.INFEASIBLE:
            round_log.append({"round": rnd, "status": "INFEASIBLE",
                              "active_rows": len(active_idx)})
            return None, round_log, "INFEASIBLE"
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            round_log.append({"round": rnd, "status": solver.status_name(st),
                              "active_rows": len(active_idx),
                              "elapsed": time.time() - t0})
            return None, round_log, "UNKNOWN"
        sup = []
        for q in range(1, 256):
            v = solver.value(m[q])
            sup.extend([q] * v)
        viols = check_all_rows(masks, caps, sup)
        round_log.append({"round": rnd, "status": "FOUND",
                          "support_size": len(sup), "distinct": len(set(sup)),
                          "violations": len(viols), "active_rows": len(active_idx)})
        if not viols:
            return sup, round_log, "ADMISSIBLE"
        for vi in viols:
            active_idx.add(vi)
    return None, round_log, "MAX_ROUNDS"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot", type=int, default=1)
    ap.add_argument("--pivot-name", default="e11")
    ap.add_argument("--rows", type=Path, required=True)
    ap.add_argument("--n", type=int, default=19)
    ap.add_argument("--trials", type=int, default=50)
    ap.add_argument("--cegar-sec", type=float, default=300)
    ap.add_argument("--sat-sec", type=int, default=30)
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
    # compute per-point multiplicity bounds
    mult_bound = {q: args.n for q in range(256)}
    mult_bound[0] = 0
    for i, (mask, cap) in enumerate(zip(masks, caps)):
        for p in mask_pts(mask):
            if p >= 1 and cap < mult_bound[p]:
                mult_bound[p] = cap
    print(f"Mult bound hist: {dict(sorted(Counter(mult_bound[q] for q in range(1,256)).items()))}")
    blocked = []
    records = []
    t_start = time.time()
    for trial in range(args.trials):
        if time.time() - t_start > 3600:
            break
        print(f"\n=== Trial {trial} ===")
        sup, log, status = cegar_find_support(masks, caps, args.n, mult_bound,
                                              args.seed + trial * 100,
                                              args.cegar_sec, blocked,
                                              args.max_cap_init)
        rec = {"trial": trial, "cegar_status": status, "cegar_rounds": len(log)}
        if sup is None:
            rec["note"] = f"no support: {status}"
            if log: rec["last_round"] = log[-1]
            records.append(rec)
            print(f"  No support: {status}")
            if status == "INFEASIBLE":
                rec["note"] = "ALL supports exhausted by blocking"
                break
            continue
        rec["support"] = sup
        rec["distinct"] = len(set(sup))
        rec["repeats"] = {str(q): c for q, c in Counter(sup).items() if c > 1}
        blocked.append(sup)
        print(f"  Found support: {len(sup)} terms, {len(set(sup))} distinct")
        # Stage 2: trace + nullspace filter
        tf = trace_nullspace_filter(Q, sup, ranks)
        rec["trace"] = {"consistent": tf["consistent"], "rank_aug": tf["rank_aug"],
                        "tight_count": tf["tight_count"], "elapsed_sec": tf["elapsed_sec"]}
        if not tf["consistent"]:
            rec["note"] = "rejected by trace+nullspace filter"
            records.append(rec)
            print(f"  REJECTED by trace filter in {tf['elapsed_sec']:.3f}s")
            continue
        print(f"  Trace-consistent ({tf['tight_count']} tight, {tf['elapsed_sec']:.3f}s)")
        # Stage 3: fixed-A Brent completion
        cnf_path = args.outdir / f"fixedA_{trial:03d}.cnf"
        info = build_e11_cnf(Q, sup, cnf_path)
        rec["cnf"] = {"vars": info["vars"], "clauses": info["clauses"]}
        print(f"  CNF: {info['vars']} vars, {info['clauses']} clauses")
        st, assign = solve_cnf(cnf_path, args.sat_sec)
        rec["sat_status"] = st
        print(f"  SAT result: {st}")
        if st == "SAT":
            nt = len(sup)
            vv = [np.array([1 if assign.get(info["V"][t][b], False) else 0
                            for b in range(9)], dtype=np.uint8) for t in range(nt)]
            ww = [np.array([1 if assign.get(info["W"][t][c], False) else 0
                            for c in range(9)], dtype=np.uint8) for t in range(nt)]
            ok = verify_quotient(Q, sup, vv, ww)
            rec["quotient_verified"] = ok
            print(f"  Quotient verified: {ok}")
            if ok and args.pivot == 1:
                lift = lift_e11(sup, vv, ww)
                rec["lift"] = {"rank": lift["rank"], "verified": lift["verified"]}
                print(f"  LIFT: rank={lift['rank']}, verified={lift['verified']}")
                if lift["verified"]:
                    p = args.outdir / f"RANK22_decomposition_trial{trial:03d}.json"
                    p.write_text(json.dumps(lift, indent=2, sort_keys=True) + "\n")
                    rec["BREAKTHROUGH"] = str(p)
                    records.append(rec)
                    break
                save = args.outdir / f"quotient_decomp_{trial:03d}.json"
                save.write_text(json.dumps({
                    "pivot": args.pivot, "support": sup,
                    "V": [[int(x) for x in v] for v in vv],
                    "W": [[int(x) for x in w] for w in ww]
                }, indent=2) + "\n")
                rec["quotient_decomp"] = str(save)
        records.append(rec)
    summary = {
        "pivot": args.pivot, "pivot_name": args.pivot_name, "n": args.n,
        "trials_run": len(records),
        "admissible_found": sum(1 for r in records if "support" in r),
        "trace_rejected": sum(1 for r in records
                              if r.get("trace") and not r["trace"]["consistent"]),
        "trace_passed": sum(1 for r in records
                            if r.get("trace") and r["trace"]["consistent"]),
        "sat_results": dict(Counter(r.get("sat_status", "-") for r in records)),
        "breakthrough": any("BREAKTHROUGH" in r for r in records),
        "elapsed_sec": time.time() - t_start,
        "records": records,
    }
    out = args.outdir / "e11_cegar_pipeline_summary.json"
    out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    brief = {k: v for k, v in summary.items() if k != "records"}
    print(f"\n{'='*60}")
    print(json.dumps(brief, indent=2, sort_keys=True))
    print(f"Saved {out}")


if __name__ == "__main__":
    main()
