#!/usr/bin/env python3
"""Augment E11 rank-19 CNF with block-spread certified constraints.

Adds brow/bcol (row/col group membership), R1 (at-least-3 own-block hitters),
and R2 (no singleton off-block hits). These are consequences of the Brent
equations and rank(I_3)=3 on each core block, verified against the full
rank-21 pool in pool_block_spread_check.json.

Block convention: T[3i+j, 3j+k, 3i+k]=1.
  R_j = {3j, 3j+1, 3j+2} (B-side), C_i = {3i, 3i+1, 3i+2} (C-side).
  Slice s has block (j=(s+1)%3, i=(s+1)//3).
  RGROUP = CGROUP = [7, 56, 448].
"""
from __future__ import annotations
import argparse, json, hashlib, time
from pathlib import Path
from typing import List, Dict, Tuple, Optional
import numpy as np

RANK = 19
NSLICE = 8

# Base variable numbering (matches E11CoreEncoder)
def var_u(t, s): return 26*t + s + 1
def var_v(t, b): return 26*t + b + 9
def var_w(t, c): return 26*t + c + 18

# Block structure
def slice_block(s):
    """Slice s -> (j=row_group, i=col_group)."""
    a = s + 1
    return a % 3, a // 3

def augment_cnf(in_path: Path, out_path: Path, rank: int = RANK,
                validate_terms: Optional[list] = None):
    """Read base CNF, add block-spread, write augmented CNF."""
    # Parse base CNF
    base_header = None
    base_clauses = []
    with open(in_path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('c'):
                continue
            if line.startswith('p cnf'):
                parts = line.split()
                base_nv = int(parts[2])
                base_nc = int(parts[3])
                base_header = line
            else:
                base_clauses.append(line)
    
    assert len(base_clauses) == base_nc, f"Clause count mismatch: {len(base_clauses)} vs {base_nc}"
    
    nv = base_nv
    new_clauses: List[str] = []
    
    def new_var():
        nonlocal nv
        nv += 1
        return nv
    
    def clause(lits):
        new_clauses.append(" ".join(str(x) for x in lits) + " 0")
    
    # ── brow_{t,j}: v_t meets row group R_j ─────────────────────────
    brow = {}  # (t, j) -> var
    for t in range(rank):
        for j in range(3):
            brow[(t, j)] = new_var()
            bv = brow[(t, j)]
            vbits = [var_v(t, 3*j + k) for k in range(3)]
            for vb in vbits:
                clause([-vb, bv])          # v_bit -> brow
            clause([-bv] + vbits)           # brow -> OR(v_bits)
    
    # ── bcol_{t,i}: w_t meets col group C_i ─────────────────────────
    bcol = {}  # (t, i) -> var
    for t in range(rank):
        for i in range(3):
            bcol[(t, i)] = new_var()
            bv = bcol[(t, i)]
            wbits = [var_w(t, 3*i + k) for k in range(3)]
            for wb in wbits:
                clause([-wb, bv])
            clause([-bv] + wbits)
    
    # ── block_hit_{t,s,j,i}: u_t[s] AND brow_{t,j} AND bcol_{t,i} ──
    bh = {}  # (t, s, j, i) -> var
    for t in range(rank):
        for s in range(NSLICE):
            for j in range(3):
                for i in range(3):
                    bh[(t, s, j, i)] = new_var()
                    h = bh[(t, s, j, i)]
                    u = var_u(t, s)
                    br = brow[(t, j)]
                    bc = bcol[(t, i)]
                    clause([-h, u])         # hit -> u
                    clause([-h, br])        # hit -> brow
                    clause([-h, bc])        # hit -> bcol
                    clause([-u, -br, -bc, h])  # u&brow&bcol -> hit
    
    # ── R1: at-least-3 own-block hitters per slice ───────────────────
    # Sequential counter: c[s][t][j] = "≥j of first t+1 own-block hits are true"
    r1c = {}
    for s in range(NSLICE):
        j_s, i_s = slice_block(s)
        x = [bh[(t, s, j_s, i_s)] for t in range(rank)]  # own-block hit vars
        
        for t in range(rank):
            for j in range(1, 4):
                r1c[(s, t, j)] = new_var()
        
        # t=0: c[0][1] <-> x[0]; c[0][2]=F; c[0][3]=F
        clause([-x[0], r1c[(s, 0, 1)]])
        clause([-r1c[(s, 0, 1)], x[0]])
        clause([-r1c[(s, 0, 2)]])
        clause([-r1c[(s, 0, 3)]])
        
        # t=1..rank-1
        for t in range(1, rank):
            for j in range(1, 4):
                ct = r1c[(s, t, j)]
                ct1 = r1c[(s, t-1, j)]
                xt = x[t]
                
                # Forward: ct-1 -> ct (propagation)
                clause([-ct1, ct])
                
                if j == 1:
                    # xt -> ct (if hit, at-least-1)
                    clause([-xt, ct])
                else:
                    ct1m = r1c[(s, t-1, j-1)]
                    # xt AND ct-1[j-1] -> ct[j]
                    clause([-xt, -ct1m, ct])
                
                # Backward: ct -> ct-1 OR xt
                clause([-ct, ct1, xt])
                if j > 1:
                    ct1m = r1c[(s, t-1, j-1)]
                    # ct -> ct-1 OR ct-1[j-1]
                    clause([-ct, ct1, ct1m])
        
        # Final: at-least-3 must hold
        clause([r1c[(s, rank-1, 3)]])
    
    # ── R2: no singleton off-block hits ──────────────────────────────
    for s in range(NSLICE):
        j_s, i_s = slice_block(s)
        for j in range(3):
            for i in range(3):
                if j == j_s and i == i_s:
                    continue  # skip own block
                for t in range(rank):
                    # If t hits off-block (j,i) in slice s, some other t' also hits it
                    others = [bh[(tp, s, j, i)] for tp in range(rank) if tp != t]
                    clause([-bh[(t, s, j, i)]] + others)
    
    # ── Validate against known decomposition ─────────────────────────
    validation = None
    if validate_terms is not None:
        # Compute full assignment for base + new variables
        assignment = {}
        for t in range(rank):
            u_val, v_val, w_val = validate_terms[t]
            for s in range(8):
                assignment[var_u(t, s)] = (u_val >> s) & 1
            for b in range(9):
                assignment[var_v(t, b)] = (v_val >> b) & 1
            for c in range(9):
                assignment[var_w(t, c)] = (w_val >> c) & 1
        
        # Compute brow, bcol
        for t in range(rank):
            v_val = validate_terms[t][1]
            w_val = validate_terms[t][2]
            for j in range(3):
                assignment[brow[(t, j)]] = 1 if (v_val & (7 << (3*j))) else 0
            for i in range(3):
                assignment[bcol[(t, i)]] = 1 if (w_val & (7 << (3*i))) else 0
        
        # Compute block_hit
        for t in range(rank):
            u_val = validate_terms[t][0]
            for s in range(8):
                for j in range(3):
                    for i in range(3):
                        u_bit = (u_val >> s) & 1
                        br_val = assignment[brow[(t, j)]]
                        bc_val = assignment[bcol[(t, i)]]
                        assignment[bh[(t, s, j, i)]] = u_bit & br_val & bc_val
        
        # Compute R1 counter
        for s in range(NSLICE):
            j_s, i_s = slice_block(s)
            count = 0
            for t in range(rank):
                h = assignment[bh[(t, s, j_s, i_s)]]
                count += h
                for j_c in range(1, 4):
                    assignment[r1c[(s, t, j_c)]] = 1 if count >= j_c else 0
        
        # Check all new clauses
        bad = 0
        for cl_str in new_clauses:
            lits = [int(x) for x in cl_str.split() if x != '0']
            sat = False
            for lit in lits:
                v = abs(lit)
                if v in assignment:
                    val = assignment[v]
                    if (lit > 0 and val) or (lit < 0 and not val):
                        sat = True
                        break
            if not sat:
                bad += 1
                if bad <= 5:
                    names = []
                    for lit in lits:
                        v = abs(lit)
                        names.append(f"{'~' if lit<0 else ''}v{v}={assignment.get(v,'?')}")
                    print(f"  UNSATISFIED clause: {cl_str[:100]} → {names[:5]}")
        validation = {"clauses_checked": len(new_clauses), "bad": bad, "ok": bad == 0}
        print(f"Validation: {validation}")
    
    # ── Write augmented CNF ──────────────────────────────────────────
    total_nc = base_nc + len(new_clauses)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, 'w') as f:
        f.write(f"c Block-spread augmented E11 rank-{rank} CNF\n")
        f.write(f"c Base: {in_path}\n")
        f.write(f"p cnf {nv} {total_nc}\n")
        for cl in base_clauses:
            f.write(cl + '\n')
        for cl in new_clauses:
            f.write(cl + '\n')
    
    # Compute SHA256
    sha = hashlib.sha256(open(out_path, 'rb').read()).hexdigest()
    
    meta = {
        "base_cnf": str(in_path),
        "cnf_path": str(out_path),
        "sha256": sha,
        "base_vars": base_nv, "base_clauses": base_nc,
        "new_vars": nv - base_nv, "new_clauses": len(new_clauses),
        "total_vars": nv, "total_clauses": total_nc,
        "block_spread_components": {
            "brow": len(brow), "bcol": len(bcol),
            "block_hit": len(bh), "r1_counter": len(r1c),
            "r2_clauses": sum(1 for s in range(NSLICE) for j in range(3) for i in range(3)
                           if (j, i) != slice_block(s) for _ in range(rank)),
        },
        "validation": validation,
        "convention": "T[3i+j,3j+k,3i+k]; R_j=C_j={3j..3j+2}; RGROUP=CGROUP=[7,56,448]",
    }
    meta_path = out_path.with_suffix('.cnf.meta.json')
    meta_path.write_text(json.dumps(meta, indent=2) + '\n')
    return meta


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--base-cnf", type=Path,
                    default=Path("data/core_sat/e11_rank19_certified.cnf"))
    ap.add_argument("--out", type=Path,
                    default=Path("data/core_sat/e11_rank19_blockspread.cnf"))
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--validate-pool", type=Path, default=None,
                    help="Pool .npy file for positive control validation")
    ap.add_argument("--validate-row", type=int, default=0)
    args = ap.parse_args()
    
    t0 = time.time()
    
    # Load validation terms if requested
    validate_terms = None
    if args.validate_pool:
        pool = np.load(args.validate_pool)
        row = pool[args.validate_row]
        R_pool = len(row) // 3
        terms = [(int(row[3*t]), int(row[3*t+1]), int(row[3*t+2])) for t in range(R_pool)]
        # For rank-19 validation with rank-21 pool: pad with zeros
        if R_pool > args.rank:
            # Sort by u to match the sorted encoding, then take first rank terms
            terms_sorted = sorted(terms, key=lambda z: (z[0], z[1], z[2]))
            validate_terms = terms_sorted[:args.rank]
            # Pad remaining with (0,0,0) — but this won't work directly.
            # Actually, the known validation requires rank-R pool with rank-R encoding.
            # For now, skip if rank mismatch.
            print(f"Note: pool has rank {R_pool}, encoding has rank {args.rank} - using rank-21 full for validation")
            validate_terms = terms_sorted  # Use all 21 terms
            # The block-spread vars/clauses are only for 19 terms.
            # We need to validate against a rank-19 known, or skip.
            validate_terms = None
            print("  Skipping validation (rank mismatch; use rank-19 known for proper test)")
    
    meta = augment_cnf(args.base_cnf, args.out, args.rank, validate_terms)
    elapsed = time.time() - t0
    meta["elapsed_sec"] = round(elapsed, 2)
    
    print(json.dumps({
        "status": "ok",
        "cnf": str(args.out),
        "total_vars": meta["total_vars"],
        "total_clauses": meta["total_clauses"],
        "new_vars": meta["new_vars"],
        "new_clauses": meta["new_clauses"],
        "elapsed_sec": meta["elapsed_sec"],
    }, indent=2))


if __name__ == "__main__":
    main()
