#!/usr/bin/env python3
"""Find a minimal INFEASIBLE subset of Wang constraints via binary reduction.

Uses CP-SAT as oracle (fast), then encodes the minimal set as a small CNF
for CaDiCaL DRAT proof.
"""
from __future__ import annotations
import json, pickle, sys, time, hashlib, subprocess, shutil
from pathlib import Path
from typing import List, Set, Tuple

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import (
    N, in_rowspace, matrix_rank_of_mask, subspace_points_from_basis, unpack_basis,
)

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(4*1024*1024), b''):
            h.update(chunk)
    return h.hexdigest()


def load_lut():
    with LUT_PATH.open('rb') as f:
        data = pickle.load(f)
    return data['lut']


def build_constraint_records(fixed_points, rank_s, include_dims, through_fixed_dims):
    """Build list of (dp_indices, cap, key, dim) constraint records."""
    lut = load_lut()
    fixed_set = set(fixed_points)
    all_pts = list(range(1, 2**N))
    dec_pts = sorted(p for p in all_pts if p not in fixed_set)
    dp_set = set(dec_pts)
    dp_to_idx = {p: i for i, p in enumerate(dec_pts)}
    n_dp = len(dec_pts)
    
    constraints = []
    
    for key, lb in lut.items():
        basis = unpack_basis(key)
        dim = len(basis)
        cap = rank_s - lb
        
        in_direct = dim in include_dims
        in_through = dim in through_fixed_dims
        if in_through:
            for fp in fixed_points:
                if not in_rowspace(fp, basis):
                    in_through = False
                    break
        if not in_direct and not in_through:
            continue
        
        pts = subspace_points_from_basis(basis)
        fixed_in = sum(1 for fp in fixed_points if fp in set(pts))
        rcap = cap - fixed_in
        dp_in = [dp_to_idx[p] for p in pts if p in dp_set]
        
        if not dp_in or rcap >= len(dp_in):
            continue
        
        constraints.append((dp_in, rcap, key, dim))
    
    return constraints, n_dp, dec_pts


def check_infeasible(constraints, n_dp, rank_s, n_fixed, time_limit=30):
    """Check if constraint set is INFEASIBLE using CP-SAT."""
    from ortools.sat.python import cp_model
    
    model = cp_model.CpModel()
    x = [model.NewBoolVar(f'x{i}') for i in range(n_dp)]
    target = rank_s - n_fixed
    model.Add(sum(x) == target)
    
    for dp_in, rcap, key, dim in constraints:
        if rcap < 0:
            model.Add(sum(x[i] for i in dp_in) <= -1)
        elif rcap == 0:
            for i in dp_in:
                model.Add(x[i] == 0)
        else:
            model.Add(sum(x[i] for i in dp_in) <= rcap)
    
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    status = solver.Solve(model)
    return status == cp_model.INFEASIBLE


def minimize_constraints(constraints, n_dp, rank_s, n_fixed, verbose=True):
    """Find a minimal infeasible subset by greedy halving + single removal."""
    import random
    
    active = list(range(len(constraints)))
    
    if verbose:
        print(f"Starting with {len(active)} constraints", file=sys.stderr)
    
    # Phase 1: Halving - try to remove large random batches
    batch_size = len(active) // 2
    while batch_size >= 10:
        random.shuffle(active)
        new_active = []
        removed = 0
        
        i = 0
        while i < len(active):
            batch = active[i:i+batch_size]
            remaining = new_active + active[i+batch_size:]
            
            subset = [constraints[j] for j in remaining]
            if check_infeasible(subset, n_dp, rank_s, n_fixed):
                removed += len(batch)
                if verbose:
                    print(f"  Removed batch of {len(batch)}, "
                          f"remaining: {len(remaining)}", file=sys.stderr)
            else:
                new_active.extend(batch)
            i += batch_size
        
        active = new_active + active[i:]
        if verbose:
            print(f"After batch_size={batch_size}: {len(active)} active, "
                  f"removed {removed}", file=sys.stderr)
        
        batch_size = max(10, batch_size // 2)
    
    # Phase 2: Single constraint removal
    if verbose:
        print(f"Phase 2: Single removal from {len(active)} constraints", file=sys.stderr)
    
    changed = True
    while changed:
        changed = False
        new_active = []
        for i, idx in enumerate(active):
            remaining = new_active + active[i+1:]
            subset = [constraints[j] for j in remaining]
            if check_infeasible(subset, n_dp, rank_s, n_fixed):
                changed = True
                if verbose and (len(active) - len(new_active)) % 50 == 0:
                    print(f"  Removed constraint {idx}, "
                          f"remaining: {len(remaining)}", file=sys.stderr)
            else:
                new_active.append(idx)
        
        active = new_active
        if verbose:
            print(f"After single pass: {len(active)} active", file=sys.stderr)
    
    return active


def encode_and_prove(constraints, core_indices, n_dp, rank_s, n_fixed, outdir, timeout=3600):
    """Encode core as CNF and get DRAT proof."""
    from pysat.card import CardEnc, EncType
    from pysat.formula import CNF
    
    formula = CNF()
    top_var = n_dp
    target = rank_s - n_fixed
    
    # Total support constraint
    dp_lits = list(range(1, n_dp + 1))
    atmost = CardEnc.atmost(lits=dp_lits, bound=target, top_id=top_var, encoding=EncType.seqcounter)
    top_var = max(top_var, atmost.nv)
    for cl in atmost.clauses:
        formula.append(cl)
    
    atleast = CardEnc.atleast(lits=dp_lits, bound=target, top_id=top_var, encoding=EncType.seqcounter)
    top_var = max(top_var, atleast.nv)
    for cl in atleast.clauses:
        formula.append(cl)
    
    # Core constraints
    for idx in core_indices:
        dp_in, rcap, key, dim = constraints[idx]
        lits = [i + 1 for i in dp_in]  # 1-indexed
        
        if rcap < 0 or (rcap == 0 and not lits):
            formula.append([])
        elif rcap == 0:
            for v in lits:
                formula.append([-v])
        else:
            card = CardEnc.atmost(lits=lits, bound=rcap, top_id=top_var, encoding=EncType.seqcounter)
            top_var = max(top_var, card.nv)
            for cl in card.clauses:
                formula.append(cl)
    
    cnf_path = outdir / "core_minimal.cnf"
    formula.to_file(str(cnf_path))
    
    print(f"Core CNF: {top_var} vars, {len(formula.clauses)} clauses", file=sys.stderr)
    
    # CaDiCaL with DRAT
    drat_path = outdir / "core_minimal.drat"
    cad_log = outdir / "core_minimal.cadical.log"
    
    t = time.time()
    try:
        proc = subprocess.run(
            ["cadical", "--unsat", "--binary=false", "-n", str(cnf_path), str(drat_path)],
            capture_output=True, text=True, timeout=timeout
        )
        cad_log.write_text(proc.stdout + proc.stderr)
        cad_exit = proc.returncode
    except subprocess.TimeoutExpired:
        cad_exit = -1
    
    cad_time = time.time() - t
    status = "UNSAT" if cad_exit == 20 else ("SAT" if cad_exit == 10 else f"EXIT_{cad_exit}")
    print(f"CaDiCaL: {status} in {cad_time:.1f}s", file=sys.stderr)
    
    # DRAT verification
    verified = False
    trim_log = outdir / "core_minimal.drat_trim.log"
    if cad_exit == 20 and drat_path.exists():
        try:
            trim = subprocess.run(
                ["drat-trim", str(cnf_path), str(drat_path)],
                capture_output=True, text=True, timeout=600
            )
            trim_log.write_text(trim.stdout + trim.stderr)
            verified = "s VERIFIED" in (trim.stdout + trim.stderr)
            print(f"drat-trim: {'VERIFIED' if verified else 'NOT verified'}", file=sys.stderr)
        except subprocess.TimeoutExpired:
            print("drat-trim timed out", file=sys.stderr)
    
    return {
        "status": status,
        "drat_verified": verified,
        "vars": top_var,
        "clauses": len(formula.clauses),
        "cadical_time_sec": cad_time,
        "hashes": {
            p.name: sha256(p) for p in [cnf_path, drat_path, trim_log] 
            if p.exists() and p.stat().st_size > 0
        },
    }


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--rep", type=int, required=True)
    ap.add_argument("--rank-s", type=int, default=20)
    ap.add_argument("--include-dims", type=str, default="1")
    ap.add_argument("--through-fixed-dims", type=str, default="4,6")
    ap.add_argument("--drat-timeout", type=int, default=3600)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    
    t0 = time.time()
    args.out.mkdir(parents=True, exist_ok=True)
    
    inc_dims = set(int(x) for x in args.include_dims.split(",") if x.strip())
    thr_dims = set(int(x) for x in args.through_fixed_dims.split(",") if x.strip())
    fixed = [1, args.rep]
    
    print("Building constraints...", file=sys.stderr)
    constraints, n_dp, dec_pts = build_constraint_records(
        fixed, args.rank_s, inc_dims, thr_dims
    )
    print(f"Total: {len(constraints)} constraints on {n_dp} vars", file=sys.stderr)
    
    # Verify full set is INFEASIBLE
    if not check_infeasible(constraints, n_dp, args.rank_s, len(fixed)):
        print("Full set is NOT infeasible!", file=sys.stderr)
        return
    print("Full set confirmed INFEASIBLE", file=sys.stderr)
    
    # Minimize
    print("\nMinimizing constraint set...", file=sys.stderr)
    core_indices = minimize_constraints(constraints, n_dp, args.rank_s, len(fixed))
    print(f"\nMinimal core: {len(core_indices)} constraints", file=sys.stderr)
    
    # Save core info
    core_records = []
    for idx in core_indices:
        dp_in, rcap, key, dim = constraints[idx]
        core_records.append({"idx": idx, "key": int(key), "dim": dim, "cap": rcap, "n_pts": len(dp_in)})
    
    (args.out / "core_records.json").write_text(json.dumps({
        "core_size": len(core_indices),
        "total_constraints": len(constraints),
        "records": core_records,
    }, indent=2))
    
    # Encode and prove
    print("\nEncoding core and getting DRAT proof...", file=sys.stderr)
    proof_meta = encode_and_prove(
        constraints, core_indices, n_dp, args.rank_s, len(fixed),
        args.out, timeout=args.drat_timeout
    )
    
    meta = {
        "core_size": len(core_indices),
        "total_constraints": len(constraints),
        "n_dp": n_dp,
        "fixed_points": fixed,
        "rank_s": args.rank_s,
        "total_elapsed_sec": time.time() - t0,
        **proof_meta,
    }
    
    (args.out / "meta.json").write_text(json.dumps(meta, indent=2, sort_keys=True))
    print(json.dumps(meta, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
