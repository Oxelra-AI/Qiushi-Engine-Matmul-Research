#!/usr/bin/env python3
"""E11 n=19 support search via hill-climb + perturbation + trace filter + completion.

Strategy: 
1. Hill-climb to minimize Wang violations (known to reach ~8 for E11 n=19)
2. Attempt targeted repairs (swap one point to fix violations)
3. Apply trace+nullspace filter
4. Fixed-A Brent completion
"""
import json, time, subprocess, random, struct, sys
from pathlib import Path
from collections import Counter
import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
WORKSPACE = SCRIPT_DIR.parent


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
        p = None
        for i in range(r, m):
            if A[i,c]: p = i; break
        if p is None: continue
        if p != r: A[[r,p]] = A[[p,r]]
        for i in range(m):
            if i != r and A[i,c]: A[i] ^= A[r]
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
        c = int.from_bytes(raw[off+32:off+36], "little", signed=True)
        masks.append(m); caps.append(c)
        off += 36
    return masks, caps


def mask_pts(m):
    pts = []; x = m
    while x:
        b = (x & -x).bit_length() - 1; pts.append(b); x ^= 1 << b
    return pts


def count_violations(masks, caps, cnt):
    viol = 0
    for mask, cap in zip(masks, caps):
        s = sum(cnt.get(pt, 0) for pt in mask_pts(mask))
        if s > cap: viol += 1
    return viol


def delta_violations(masks, caps, cnt, old_q, new_q):
    """Incremental violation count change when replacing one copy of old_q with new_q."""
    delta = 0
    for mask, cap in zip(masks, caps):
        pts = set(mask_pts(mask))
        old_s = sum(cnt.get(pt, 0) for pt in pts)
        new_s = old_s
        if old_q in pts: new_s -= 1
        if new_q in pts: new_s += 1
        was_viol = old_s > cap
        now_viol = new_s > cap
        delta += int(now_viol) - int(was_viol)
    return delta


def hillclimb(masks, caps, n, mult_bound, rng, max_steps=50000):
    """Standard hill-climb with random restarts."""
    # random initial support respecting mult bounds
    pool = []
    for q in range(1, 256):
        pool.extend([q] * mult_bound.get(q, 1))
    sup = sorted(rng.sample(pool, min(n, len(pool))))
    cnt = Counter(sup)
    best_viol = count_violations(masks, caps, cnt)
    best_sup = list(sup)
    
    for step in range(max_steps):
        if best_viol == 0:
            break
        # try swapping: remove one copy of a random point, add one copy of another
        present = [q for q in cnt if cnt[q] > 0]
        remove_q = rng.choice(present)
        candidates = [q for q in range(1, 256) 
                      if q != remove_q and cnt.get(q, 0) < mult_bound.get(q, 1)]
        if not candidates:
            continue
        add_q = rng.choice(candidates)
        d = delta_violations(masks, caps, cnt, remove_q, add_q)
        if d <= 0:
            cnt[remove_q] -= 1
            if cnt[remove_q] == 0: del cnt[remove_q]
            cnt[add_q] = cnt.get(add_q, 0) + 1
            new_viol = best_viol + d
            if new_viol < best_viol:
                best_viol = new_viol
                best_sup = sorted(cnt.elements())
    return best_sup, best_viol


def generalized_inverse(M):
    A = (M.copy() & 1).astype(np.uint8)
    n = A.shape[0]
    P = np.eye(n, dtype=np.uint8); Qm = np.eye(n, dtype=np.uint8)
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
            if A[i,c]: p = i; break
        if p is None: continue
        if p != r: A[[r,p]] = A[[p,r]]
        for i in range(m):
            if i != r and A[i,c]: A[i] ^= A[r]
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


def trace_filter(Q, support, ranks):
    nt = len(support); nvars = 81 * nt
    rows, rhs = [], []
    for s in range(8):
        act = [t for t, u in enumerate(support) if (u >> s) & 1]
        for b in range(9):
            for c in range(9):
                x = 0
                for t in act: x |= 1 << (81*t + 9*b + c)
                rows.append(x); rhs.append(int(Q[s,b,c]))
    tight_count = 0; tight_ranks = Counter()
    for lam in range(1, 256):
        act = [t for t, u in enumerate(support) if ((lam & u).bit_count() & 1)]
        r = ranks[lam]
        if r == 0 or len(act) != r: continue
        tight_count += 1; tight_ranks[r] += 1
        M = np.zeros((9,9), dtype=np.uint8)
        for s in range(8):
            if (lam >> s) & 1: M ^= Q[s]
        G, rr = generalized_inverse(M)
        left_n = nullspace(M.T & 1)
        right_n = nullspace(M)
        for t in act:
            base = 81*t
            x = 0
            for i in range(9):
                for j in range(9):
                    if G[j,i] & 1: x |= 1 << (base + 9*i + j)
            rows.append(x); rhs.append(1)
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
            "tight": tight_count, "tight_ranks": dict(sorted(tight_ranks.items()))}


def build_cnf(Q, support, path):
    nt = len(support); nv = 0
    def newv():
        nonlocal nv; nv += 1; return nv
    V = [[newv() for _ in range(9)] for _ in range(nt)]
    W = [[newv() for _ in range(9)] for _ in range(nt)]
    clauses = []; prod = {}
    def get_prod(t, b, c):
        key = (t,b,c)
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
                lits = [get_prod(t,b,c) for t in act]
                if not lits:
                    if Q[s,b,c]: clauses.append([])
                    continue
                xor_eq(lits, int(Q[s,b,c]))
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
    return f"UNKNOWN", {}


def verify_quotient(Q, support, vv, ww):
    R = np.zeros_like(Q)
    for t, u in enumerate(support):
        outer = np.outer(vv[t], ww[t]) & 1
        for s in range(8):
            if (u >> s) & 1: R[s] ^= outer
    return bool(np.array_equal(R & 1, Q & 1))


def main():
    outdir = WORKSPACE / "data" / "construction_pipeline" / "e11_hillclimb_pipeline"
    outdir.mkdir(parents=True, exist_ok=True)
    rows_path = WORKSPACE / "data" / "wang_native" / "quotient_binaries" / "e11_all_n19.bin"
    masks, caps = load_rows(rows_path)
    Q = quotient_tensor(1)
    ranks = {}
    for lam in range(1, 256):
        M = np.zeros((9,9), dtype=np.uint8)
        for s in range(8):
            if (lam >> s) & 1: M ^= Q[s]
        ranks[lam] = mat_rank(M)

    mult_bound = {q: 19 for q in range(256)}
    mult_bound[0] = 0
    for m, c in zip(masks, caps):
        for pt in mask_pts(m):
            if pt >= 1 and c < mult_bound[pt]:
                mult_bound[pt] = c
    print(f"Mult bound hist: {dict(sorted(Counter(mult_bound[q] for q in range(1,256)).items()))}")

    records = []
    t_start = time.time()
    best_global = 999

    for trial in range(200):
        if time.time() - t_start > 1500:
            break
        rng = random.Random(trial + 1000)
        sup, viol = hillclimb(masks, caps, 19, mult_bound, rng, max_steps=100000)
        if viol < best_global:
            best_global = viol
        rec = {"trial": trial, "violations": viol, "distinct": len(set(sup)),
               "repeats": {str(q): c for q, c in Counter(sup).items() if c > 1}}
        if viol == 0:
            print(f"Trial {trial}: ZERO violations! Support: {sup}")
            rec["support"] = sup
            tf = trace_filter(Q, sup, ranks)
            rec["trace"] = tf
            print(f"  Trace: consistent={tf['consistent']}, tight={tf['tight']}, ranks={tf['tight_ranks']}")
            if tf["consistent"]:
                cnf_path = outdir / f"e11_fixedA_{trial:03d}.cnf"
                info = build_cnf(Q, sup, cnf_path)
                rec["cnf"] = {"vars": info["vars"], "clauses": info["clauses"]}
                print(f"  CNF: {info['vars']} vars, {info['clauses']} clauses. Running CaDiCaL...")
                st, assign = solve_cnf(cnf_path, 30)
                rec["sat"] = st
                print(f"  SAT: {st}")
                if st == "SAT":
                    nt = len(sup)
                    vv = [np.array([1 if assign.get(info["V"][t][b], False) else 0
                                    for b in range(9)], dtype=np.uint8) for t in range(nt)]
                    ww = [np.array([1 if assign.get(info["W"][t][c], False) else 0
                                    for c in range(9)], dtype=np.uint8) for t in range(nt)]
                    ok = verify_quotient(Q, sup, vv, ww)
                    rec["verified"] = ok
                    if ok:
                        print(f"  *** E11 RANK-19 QUOTIENT DECOMPOSITION FOUND! ***")
                        dp = outdir / f"e11_decomp_{trial:03d}.json"
                        dp.write_text(json.dumps({
                            "support": sup, "pivot": 1,
                            "V": [[int(x) for x in v] for v in vv],
                            "W": [[int(x) for x in w] for w in ww],
                        }, indent=2) + "\n")
                        rec["decomp_path"] = str(dp)
            records.append(rec)
        else:
            if trial % 20 == 0:
                print(f"Trial {trial}: best_viol={viol} (global_best={best_global}), "
                      f"elapsed={time.time()-t_start:.0f}s")
            records.append(rec)

    summary = {
        "trials": len(records),
        "zero_violation_found": sum(1 for r in records if r.get("violations") == 0),
        "trace_passed": sum(1 for r in records if r.get("trace", {}).get("consistent")),
        "sat_found": sum(1 for r in records if r.get("sat") == "SAT"),
        "best_violation": min(r["violations"] for r in records),
        "elapsed_sec": time.time() - t_start,
    }
    # Save only interesting records
    interesting = [r for r in records if r.get("violations", 999) <= 2 or r.get("support")]
    summary["interesting_records"] = interesting
    summary["violation_hist"] = dict(sorted(Counter(r["violations"] for r in records).items()))
    out = outdir / "hillclimb_pipeline_summary.json"
    out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(f"\n{'='*60}")
    print(json.dumps({k: v for k, v in summary.items() if k != "interesting_records"},
                     indent=2, sort_keys=True))
    print(f"Saved {out}")


if __name__ == "__main__":
    main()
