#!/usr/bin/env python3
"""Quotient support feasibility via SCIP MIP with all Wang rows + unconditional cuts.

Model: 255 binary variables x_1..x_255
  sum x = 19
  For each Wang row (cap c, point set S): sum_{p in S} x_p <= c
  For each unconditional qcut: N_out + sum_q (w_q - r_q) >= R

Tests the full occupation system for infeasibility. Uses SCIP 10.
"""
from __future__ import annotations

import argparse
import json
import os
import struct
import sys
import time
from collections import Counter
from pathlib import Path
import numpy as np

SESSION = Path(os.path.dirname(os.path.abspath(__file__))).parent.parent
MAGIC = b"E11WANG1"


def load_binary(path: str | Path) -> list[tuple[int, int, list[int]]]:
    d = open(path, "rb").read()
    assert d[:8] == MAGIC
    n = struct.unpack("<I", d[8:12])[0]
    REC = struct.calcsize("<BBHQQQQ")
    rows = []
    off = 12
    for _ in range(n):
        cap, dim8, pad, w0, w1, w2, w3 = struct.unpack_from("<BBHQQQQ", d, off)
        off += REC
        pts = []
        for wi, w in enumerate([w0, w1, w2, w3]):
            for b in range(64):
                if (w >> b) & 1:
                    pts.append(64 * wi + b)
        rows.append((cap, dim8, pts))
    return rows


def quotient_tensor(pivot: int) -> np.ndarray:
    """Build the corrected quotient tensor for the given pivot."""
    # Full tensor T[3i+j, 3j+k, 3i+k] = 1
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3*i+j, 3*j+k, 3*i+k] = 1
    
    h = pivot.bit_length() - 1
    # Build 9 original A-basis slices
    slices_9 = [T[a] for a in range(9)]  # T[a, :, :] for basis vector e_a
    
    # Project to quotient
    Q = np.zeros((8, 9, 9), dtype=np.uint8)
    for a in range(9):
        bit_a = 1 << a
        if bit_a == pivot:
            continue  # skip the pivot basis vector
        # Project bit_a to quotient coordinate
        qa = bit_a
        if (qa >> h) & 1:
            qa ^= pivot
        # Remove bit h
        low = qa & ((1 << h) - 1)
        high = (qa >> (h + 1)) << h
        q_idx = low | high
        if q_idx == 0:
            continue
        # q_idx is 1..255, but we need 0..7 as quotient basis index
        q_bit = q_idx.bit_length() - 1  # this only works if q_idx is a power of 2
        # Actually, the quotient has 8 basis vectors, indexed 0..7
        # The quotient coordinate is the 8-bit value after removing bit h
        # We need to XOR the slice into all quotient coordinates appearing in the image
        # For a single basis vector e_a, its image is a single quotient basis vector
        Q[q_bit] = (Q[q_bit] + slices_9[a]) % 2
    
    return Q


def contraction_ranks(Q: np.ndarray) -> dict[int, int]:
    """Compute contraction rank for each quotient direction q=1..255."""
    ranks = {}
    for q in range(1, 256):
        # Sum slices where q has bits set
        M = np.zeros((9, 9), dtype=np.uint8)
        for b in range(8):
            if (q >> b) & 1:
                M = (M + Q[b]) % 2
        ranks[q] = int(np.linalg.matrix_rank(M.astype(float)))
    return ranks


def scan_pair_qcuts(Q: np.ndarray, target: int = 19) -> list[dict]:
    """Scan unconditional pair-source quotient-rank cuts."""
    cr = contraction_ranks(Q)
    cuts = []
    pts = list(range(1, 256))
    
    for i, q1 in enumerate(pts):
        for q2 in pts[i+1:]:
            # B-side: W = span of B-vectors of q1, q2
            M1_b = Q[0] * 0
            M2_b = Q[0] * 0
            for b in range(8):
                if (q1 >> b) & 1:
                    M1_b = M1_b.astype(int)
                    M1_b = np.zeros((9, 9), dtype=np.uint8)
                    break
            # Simpler: compute W dimension and projected rank directly
            # For source pair (q1, q2), B-side:
            # W_B = col_span(M_{q1}) + col_span(M_{q2}) in F2^9
            M1 = np.zeros((9, 9), dtype=np.uint8)
            M2 = np.zeros((9, 9), dtype=np.uint8)
            for b in range(8):
                if (q1 >> b) & 1:
                    M1 = (M1 + Q[b]) % 2
                if (q2 >> b) & 1:
                    M2 = (M2 + Q[b]) % 2
            
            # B-side: column spans
            cols1 = M1.T  # rows are columns of M1
            cols2 = M2.T
            combined_B = np.vstack([cols1, cols2]) % 2
            W_dim_B = int(np.linalg.matrix_rank(combined_B.astype(float)))
            
            # Target contraction in W_B: need to compute rank of target in W_B
            # The "target" is the whole tensor restricted to W_B
            # For unconditional cut: R = rank of projected target in W
            # Actually, the requirement R is the rank of the target tensor
            # contracted/projected onto W.
            # For pair sources q1,q2:
            # w_{q1} = dim(col(M_{q1})) = cr[q1] (the contraction rank)
            # w_{q2} = dim(col(M_{q2})) = cr[q2]
            # r_{q1} = rank of M_{q1} projected onto W = cr[q1] (same)
            # The unconditional inequality is:
            # N_out + (w_{q1} - r_{q1}) + (w_{q2} - r_{q2}) >= R
            # where r_qi = rank of M_qi, w_qi = dim col(M_qi) = r_qi
            # So w_qi - r_qi = 0 for B-side.
            # For C-side the roles switch.
            
            # Actually let me re-read the earlier research derivation more carefully.
            # The unconditional quotient-rank inequality from analysis:
            # For source contractions S = {q1, ..., qm}, target t, side W = sum col(M_qi):
            # N_out >= R - sum_q (w_q - r_q)
            # where N_out = number of support points outside all source subspaces,
            # w_q = rank of M_q, and r_q = rank of M_q projected onto W^perp... 
            # 
            # Actually the correct formula from the earlier research scripts is:
            # N_out + sum_q (w_q - r_q) >= R
            # which becomes N_out >= R when each source's W contribution equals its rank.
            
            # Let me just compute the projected target rank R in W
            # W is the column span of [M1 | M2] in F2^9
            # The projected target rank is the rank of the target tensor
            # when B is restricted to W.
            # For our quotient tensor Q[s,b,c], s=0..7, b=0..8, c=0..8:
            # The B-restricted version sums over b in W.
            # This is the column rank of the flattened [s*c x W] matrix.
            
            # Actually, the requirement is simpler. The contraction rank of 
            # the quotient at direction q gives the rank of the slice M_q.
            # The "projected target rank" R is just the rank of the full tensor's
            # B-flattening restricted to column space W.
            
            # For the unconditional inequality, the key numbers are:
            # - For each source q: excess = w_q - r_q where w_q = rank(M_q) and
            #   r_q = rank of M_q's column vectors within W
            # Since W = col(M_q1) + col(M_q2), r_q = w_q always, so excess = 0.
            # Thus the inequality becomes simply N_out >= R.
            
            # R is the rank of sum_s Q[s] restricted to columns in W.
            # For simplicity, compute R as the F2 rank of the stacked matrix
            # [rows of Q[s] restricted to basis of W] for all s.
            
            # Get basis of W (column space of M1, M2)
            if W_dim_B == 0:
                continue
            # Find basis by row reduction of combined_B
            basis_rows = []
            mat = combined_B.copy()
            pivots = []
            for col in range(9):
                found = False
                for row in range(len(pivots), mat.shape[0]):
                    if mat[row, col] == 1:
                        if row != len(pivots):
                            mat[[len(pivots), row]] = mat[[row, len(pivots)]]
                        for r2 in range(mat.shape[0]):
                            if r2 != len(pivots) and mat[r2, col] == 1:
                                mat[r2] = (mat[r2] + mat[len(pivots)]) % 2
                        pivots.append(col)
                        basis_rows.append(mat[len(pivots)-1].copy())
                        found = True
                        break
                if len(pivots) == W_dim_B:
                    break
            
            # Build projection matrix: restrict B-coordinates to W
            # Stack all Q[s] * basis^T to get the projected tensor
            W_basis = np.array(basis_rows, dtype=np.uint8)  # W_dim_B x 9
            # Projected tensor: Q_proj[s, w, c] = sum_b Q[s,b,c] * W_basis[w,b]
            # Flattened [s*c x w]: for each (s,c), the w-vector is Q[s,:,c] . W_basis^T
            flat = np.zeros((8 * 9, W_dim_B), dtype=np.uint8)
            for s in range(8):
                for c in range(9):
                    for w in range(W_dim_B):
                        flat[s * 9 + c, w] = int(np.dot(Q[s, :, c].astype(int), W_basis[w].astype(int))) % 2
            R_B = int(np.linalg.matrix_rank(flat.astype(float)))
            
            if R_B <= 0:
                continue
            
            # Determine outside points: points not in subspace of q1 or q2
            inside = set()
            for p in range(1, 256):
                if (p & q1) == p or (p & q2) == p:
                    # p is in the subspace generated by bits of q1 or q2
                    pass
                # Actually "inside" means p is in span of sources
                # A point p is "inside" source q if it participates in q's contraction
                # i.e., the q-contraction uses point p's slice.
                # Actually, a point p is inside the source subspace if p is in 
                # the subspace spanned by the source directions.
                # Source q1, q2: the subspace is span(q1, q2) in F2^8.
                pass
            
            # The outside set is just {p : p not in span(q1, q2)}
            # span(q1, q2) = {0, q1, q2, q1^q2}
            source_span = {0, q1, q2, q1 ^ q2}
            outside = [p for p in range(1, 256) if p not in source_span]
            n_out = len(outside)  # = 255 - |source_span \ {0}|
            
            # The inequality: sum_{p in outside} x_p >= R_B
            # (since excess terms are 0 for pair sources with W = col span)
            
            if R_B > n_out:
                # Impossible even without other constraints
                cuts.append({"q1": q1, "q2": q2, "R": R_B, "n_out": n_out, "W_dim": W_dim_B,
                             "side": "B", "outside": outside, "trivially_impossible": True})
                continue
            
            if R_B >= 3:  # Only keep nontrivial cuts
                cuts.append({
                    "q1": q1, "q2": q2, "R": R_B, "n_out": n_out, "W_dim": W_dim_B,
                    "side": "B", "source_span": sorted(source_span - {0}),
                })
    
    return cuts


def write_scip_lp(rows, cuts, target, cr, outpath, pivot_name):
    """Write LP file for SCIP."""
    with open(outpath, "w") as f:
        f.write(f"\\ Quotient support model for {pivot_name} at target {target}\n")
        f.write("Minimize\n obj: x1\n")  # dummy objective
        f.write("Subject To\n")
        
        # Cardinality
        terms = " + ".join(f"x{p}" for p in range(1, 256))
        f.write(f" card: {terms} = {target}\n")
        
        # Wang rows
        for idx, (cap, dim8, pts) in enumerate(rows):
            if cap >= target:
                continue  # trivially satisfied
            expr = " + ".join(f"x{p}" for p in pts)
            f.write(f" w{idx}: {expr} <= {cap}\n")
        
        # Contraction lower bounds
        for q in range(1, 256):
            r = cr.get(q, 0)
            if r > 0:
                f.write(f" clb{q}: x{q} >= 0\n")  # trivial, but we need contraction cuts
        
        # Unconditional cuts: sum_{p in outside} x_p >= R
        for ci, cut in enumerate(cuts):
            if cut.get("trivially_impossible"):
                # Add impossible constraint
                f.write(f" qcut{ci}: x1 >= {target + 1}\n")  # forces infeasibility
                continue
            R = cut["R"]
            outside = cut.get("outside")
            if outside is None:
                src = cut["source_span"]
                outside = [p for p in range(1, 256) if p not in src]
            expr = " + ".join(f"x{p}" for p in outside)
            f.write(f" qcut{ci}: {expr} >= {R}\n")
        
        f.write("Bounds\n")
        f.write("Binary\n")
        f.write(" ".join(f"x{p}" for p in range(1, 256)) + "\n")
        f.write("End\n")
    
    return outpath


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pivot-name", required=True)
    ap.add_argument("--binary", required=True)
    ap.add_argument("--target", type=int, default=19)
    ap.add_argument("--outdir", default=None)
    ap.add_argument("--time-limit", type=int, default=600)
    ap.add_argument("--add-qcuts", action="store_true")
    ap.add_argument("--min-req", type=int, default=6)
    args = ap.parse_args()
    
    outdir = Path(args.outdir) if args.outdir else SESSION / "workspace/data/scip_model"
    outdir.mkdir(parents=True, exist_ok=True)
    
    print(f"Loading {args.binary}...")
    rows = load_binary(args.binary)
    print(f"  {len(rows)} rows")
    
    # Build quotient tensor for contraction ranks
    pivot_map = {"rank2": 17, "rank3": 273, "e11": 1}
    pivot = pivot_map[args.pivot_name]
    Q = quotient_tensor(pivot)
    cr = contraction_ranks(Q)
    print(f"  Contraction rank hist: {dict(Counter(cr.values()))}")
    
    cuts = []
    if args.add_qcuts:
        print("Scanning pair-source qcuts (this takes ~60s)...")
        all_cuts = scan_pair_qcuts(Q, args.target)
        cuts = [c for c in all_cuts if c["R"] >= args.min_req]
        print(f"  Total nontrivial cuts: {len(all_cuts)}, req>={args.min_req}: {len(cuts)}")
    
    # Count binding constraints
    binding = sum(1 for c, d, p in rows if 0 < c < args.target)
    print(f"  Binding Wang rows: {binding}")
    print(f"  Cuts added: {len(cuts)}")
    
    lp_path = outdir / f"{args.pivot_name}_n{args.target}.lp"
    write_scip_lp(rows, cuts, args.target, cr, lp_path, args.pivot_name)
    print(f"  LP file: {lp_path}")
    
    # Count file size and constraints
    with open(lp_path) as f:
        nlines = sum(1 for _ in f)
    print(f"  LP file lines: {nlines}")
    
    # Run SCIP
    import subprocess
    print(f"\nRunning SCIP (time limit {args.time_limit}s)...")
    t0 = time.time()
    
    # Write SCIP settings file
    settings_path = outdir / f"{args.pivot_name}_settings.set"
    with open(settings_path, "w") as f:
        f.write(f"limits/time = {args.time_limit}\n")
        f.write("display/verblevel = 4\n")
    
    result = subprocess.run(
        ["scip", "-s", str(settings_path), "-f", str(lp_path)],
        capture_output=True, text=True, timeout=args.time_limit + 60,
    )
    elapsed = time.time() - t0
    
    # Parse output
    stdout = result.stdout
    status = "unknown"
    if "problem is solved [infeasible]" in stdout.lower() or "infeasible" in stdout.lower():
        status = "infeasible"
    elif "problem is solved [optimal solution found]" in stdout.lower():
        status = "optimal"
    elif "time limit reached" in stdout.lower():
        status = "time_limit"
    
    # Extract solution if found
    sol = None
    if status == "optimal":
        sol = []
        for p in range(1, 256):
            if f"x{p}" in stdout:
                # Try to parse
                for line in stdout.split("\n"):
                    if f"x{p} " in line and "1" in line:
                        sol.append(p)
    
    out = {
        "pivot_name": args.pivot_name,
        "target": args.target,
        "binary": str(args.binary),
        "status": status,
        "elapsed_sec": elapsed,
        "wang_rows": len(rows),
        "binding_rows": binding,
        "qcuts": len(cuts),
        "solution": sol,
        "stdout_tail": stdout[-4000:],
        "stderr_tail": result.stderr[-1000:],
    }
    
    out_path = outdir / f"{args.pivot_name}_n{args.target}_scip_result.json"
    with open(out_path, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
    print(f"\nStatus: {status}")
    print(f"Elapsed: {elapsed:.1f}s")
    print(f"Saved: {out_path}")


if __name__ == "__main__":
    main()
