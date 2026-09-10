#!/usr/bin/env python3
"""Fixed-A Brent completion for quotient tensor over F2.

Given a quotient tensor Q[s,b,c] (8x9x9) and a fixed A-support (19 quotient directions),
find B-vectors v_t and C-vectors w_t such that:
  XOR_{t=0..18} u_t[s] * v_t[b] * w_t[c] = Q[s,b,c]  for all s,b,c

Encodes as SAT with Tseytin product variables.
"""
import numpy as np
import subprocess
import sys
import time
import json
import argparse
from pathlib import Path


def quotient_tensor(pivot: int) -> np.ndarray:
    """Build corrected quotient tensor for given pivot."""
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    
    h = pivot.bit_length() - 1
    Q = np.zeros((8, 9, 9), dtype=np.uint8)
    
    for a_bit in range(9):
        a_val = 1 << a_bit
        if a_val == pivot:
            continue
        # Project
        qa = a_val
        if (qa >> h) & 1:
            qa ^= pivot
        low = qa & ((1 << h) - 1)
        high = (qa >> (h + 1)) << h
        q_idx = low | high
        if q_idx == 0:
            continue
        q_bit = q_idx.bit_length() - 1
        Q[q_bit] = (Q[q_bit] + T[a_bit]) % 2
    
    return Q


def encode_fixed_a(Q: np.ndarray, support: list[int], cnf_path: str) -> dict:
    """Encode fixed-A Brent completion as CNF.
    
    Variables:
      v[t][b] for t=0..18, b=0..8: B-vector bits (19*9 = 171 vars)
      w[t][c] for t=0..18, c=0..8: C-vector bits (19*9 = 171 vars)
      p[t][b][c] for t=0..18, b=0..8, c=0..8: product v[t][b] AND w[t][c] (19*9*9 = 1539 vars)
    
    Total: 171 + 171 + 1539 = 1881 variables
    """
    n_terms = len(support)
    n_b = 9
    n_c = 9
    n_s = 8
    
    # Variable numbering (1-indexed)
    def v_var(t, b):
        return 1 + t * n_b + b
    
    v_offset = n_terms * n_b
    def w_var(t, c):
        return 1 + v_offset + t * n_c + c
    
    w_offset = v_offset + n_terms * n_c
    def p_var(t, b, c):
        return 1 + w_offset + t * n_b * n_c + b * n_c + c
    
    total_vars = w_offset + n_terms * n_b * n_c
    
    clauses = []
    
    # Product constraints: p[t][b][c] = v[t][b] AND w[t][c]
    for t in range(n_terms):
        for b in range(n_b):
            for c in range(n_c):
                pv = p_var(t, b, c)
                vv = v_var(t, b)
                wv = w_var(t, c)
                # p => v: -p v v
                clauses.append([-pv, vv])
                # p => w: -p v w
                clauses.append([-pv, wv])
                # v AND w => p: -v v -w v p
                clauses.append([-vv, -wv, pv])
    
    # Brent equations: for each (s, b, c):
    #   XOR_{t: u_t has bit s set} p[t][b][c] = Q[s][b][c]
    for s in range(n_s):
        for b in range(n_b):
            for c in range(n_c):
                # Active terms: those where support[t] has bit s set
                active_terms = [t for t in range(n_terms) if (support[t] >> s) & 1]
                target = int(Q[s, b, c])
                
                if len(active_terms) == 0:
                    if target == 1:
                        clauses.append([])  # empty clause = UNSAT
                    continue
                
                # XOR encoding using Tseytin chain
                # XOR of k variables = target
                pvars = [p_var(t, b, c) for t in active_terms]
                
                if len(pvars) == 1:
                    if target == 1:
                        clauses.append([pvars[0]])
                    else:
                        clauses.append([-pvars[0]])
                else:
                    # Chain XOR: introduce auxiliary variables
                    # x1 XOR x2 XOR ... XOR xk = target
                    # aux[0] = x1
                    # aux[i] = aux[i-1] XOR x[i+1]
                    # aux[k-2] = target (or NOT target)
                    
                    aux_vars = []
                    for i in range(len(pvars) - 1):
                        total_vars += 1
                        aux_vars.append(total_vars)
                    
                    # aux[0] = x[0] XOR x[1]
                    # Tseytin for XOR: a XOR b = c
                    # (-a v -b v -c) (a v b v -c) (a v -b v c) (-a v b v c)
                    def xor_clauses(a, b, c):
                        return [
                            [-a, -b, -c],
                            [a, b, -c],
                            [a, -b, c],
                            [-a, b, c],
                        ]
                    
                    clauses.extend(xor_clauses(pvars[0], pvars[1], aux_vars[0]))
                    for i in range(2, len(pvars)):
                        clauses.extend(xor_clauses(aux_vars[i-2], pvars[i], aux_vars[i-1]))
                    
                    # Final: aux[-1] = target
                    if target == 1:
                        clauses.append([aux_vars[-1]])
                    else:
                        clauses.append([-aux_vars[-1]])
    
    # Write CNF
    with open(cnf_path, "w") as f:
        f.write(f"p cnf {total_vars} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(str(l) for l in cl) + " 0\n")
    
    return {
        "total_vars": total_vars,
        "total_clauses": len(clauses),
        "n_terms": n_terms,
        "v_vars": n_terms * n_b,
        "w_vars": n_terms * n_c,
        "p_vars": n_terms * n_b * n_c,
    }


def extract_solution(stdout: str, support: list[int], n_b: int = 9, n_c: int = 9) -> dict:
    """Extract B and C vectors from SAT solution."""
    n_terms = len(support)
    v_offset = n_terms * n_b
    
    # Parse solution line
    vals = {}
    for line in stdout.split("\n"):
        if line.startswith("v "):
            for tok in line[2:].split():
                v = int(tok)
                if v != 0:
                    vals[abs(v)] = (v > 0)
    
    if not vals:
        return None
    
    b_vecs = []
    c_vecs = []
    for t in range(n_terms):
        bv = 0
        cv = 0
        for b in range(n_b):
            var_id = 1 + t * n_b + b
            if vals.get(var_id, False):
                bv |= (1 << b)
        for c in range(n_c):
            var_id = 1 + v_offset + t * n_c + c
            if vals.get(var_id, False):
                cv |= (1 << c)
        b_vecs.append(bv)
        c_vecs.append(cv)
    
    return {"a_vecs": support, "b_vecs": b_vecs, "c_vecs": c_vecs}


def verify_decomposition(Q: np.ndarray, support: list[int], b_vecs: list[int], c_vecs: list[int]) -> int:
    """Verify the decomposition. Returns number of mismatched entries."""
    n_s, n_b, n_c = Q.shape
    R = np.zeros_like(Q)
    for t in range(len(support)):
        for s in range(n_s):
            if not ((support[t] >> s) & 1):
                continue
            for b in range(n_b):
                if not ((b_vecs[t] >> b) & 1):
                    continue
                for c in range(n_c):
                    if (c_vecs[t] >> c) & 1:
                        R[s, b, c] ^= 1
    return int(np.sum(Q != R))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot", type=int, required=True)
    ap.add_argument("--pivot-name", required=True)
    ap.add_argument("--support", required=True, help="comma-separated quotient directions")
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--timeout", type=int, default=300)
    args = ap.parse_args()
    
    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    
    support = [int(x) for x in args.support.split(",")]
    print(f"Pivot: {args.pivot} ({args.pivot_name})")
    print(f"Support: {support} ({len(support)} terms)")
    
    Q = quotient_tensor(args.pivot)
    nnz = int(np.sum(Q))
    print(f"Quotient tensor: {Q.shape}, nnz={nnz}")
    slice_ranks = [int(np.linalg.matrix_rank(Q[s].astype(float))) for s in range(8)]
    print(f"Slice ranks: {slice_ranks}")
    
    cnf_path = outdir / f"{args.pivot_name}_fixedA.cnf"
    proof_path = outdir / f"{args.pivot_name}_fixedA.drat"
    
    print(f"\nEncoding fixed-A Brent completion...")
    info = encode_fixed_a(Q, support, str(cnf_path))
    print(f"  Variables: {info['total_vars']}")
    print(f"  Clauses: {info['total_clauses']}")
    print(f"  CNF: {cnf_path}")
    
    print(f"\nRunning CaDiCaL (timeout {args.timeout}s)...")
    t0 = time.time()
    proc = subprocess.run(
        ["cadical", str(cnf_path), str(proof_path)],
        capture_output=True, text=True, timeout=args.timeout + 30,
    )
    elapsed = time.time() - t0
    
    sat = None
    if proc.returncode == 10:
        sat = True
    elif proc.returncode == 20:
        sat = False
    
    print(f"CaDiCaL: rc={proc.returncode}, sat={sat}, elapsed={elapsed:.1f}s")
    
    result = {
        "pivot": args.pivot,
        "pivot_name": args.pivot_name,
        "support": support,
        "n_terms": len(support),
        "cnf_vars": info["total_vars"],
        "cnf_clauses": info["total_clauses"],
        "cadical_sat": sat,
        "cadical_elapsed_sec": elapsed,
        "cadical_returncode": proc.returncode,
    }
    
    if sat is True:
        print("\n*** SAT: Decomposition found! ***")
        sol = extract_solution(proc.stdout, support)
        if sol:
            diff = verify_decomposition(Q, support, sol["b_vecs"], sol["c_vecs"])
            print(f"Verification: diff={diff}")
            result["decomposition"] = sol
            result["verification_diff"] = diff
            if diff == 0:
                print("\n*** VERIFIED EXACT RANK-19 QUOTIENT DECOMPOSITION ***")
                print(f"This lifts to a rank-22 full decomposition of T_{{333}} over F2!")
            else:
                print(f"WARNING: Decomposition has {diff} mismatched entries!")
    elif sat is False:
        print("\nUNSAT: No B/C completion exists for this support")
        # Verify DRAT proof
        print("Verifying DRAT proof...")
        vproc = subprocess.run(
            ["drat-trim", str(cnf_path), str(proof_path)],
            capture_output=True, text=True, timeout=600,
        )
        verified = "s VERIFIED" in vproc.stdout
        result["drat_verified"] = verified
        print(f"DRAT verification: {'VERIFIED' if verified else 'FAILED'}")
    else:
        print(f"\nUNKNOWN (rc={proc.returncode})")
    
    # Print key CaDiCaL stats
    for line in proc.stdout.split("\n"):
        for key in ["conflicts", "decisions", "propagations"]:
            if f"c {key}" in line.lower():
                print(f"  {line.strip()}")
    
    out_path = outdir / f"{args.pivot_name}_fixedA_result.json"
    with open(out_path, "w") as f:
        json.dump(result, f, indent=2, sort_keys=True)
    print(f"\nSaved: {out_path}")


if __name__ == "__main__":
    main()
