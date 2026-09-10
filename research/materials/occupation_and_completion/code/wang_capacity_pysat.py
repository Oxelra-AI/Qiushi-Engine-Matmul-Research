#!/usr/bin/env python3
"""PySAT-based Wang capacity encoder with proof-producing CaDiCaL.

Uses sequential counter encoding for cardinality constraints, which produces
~7x fewer clauses than totalizer and is more DRAT-friendly.  PySAT's built-in
CaDiCaL can produce DRAT proofs directly.

This is the proof-producing counterpart to wang_fixed_e11_range_cpsat.py.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import pickle
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Set, Tuple, Optional

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import (
    N, in_rowspace, matrix_rank_of_mask, pack_basis,
    rref_basis, subspace_points_from_basis, unpack_basis, make_actions,
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
    return data['lut']  # {packed_key: lower_bound}


def compute_stab_e11(actions):
    return [a for a in actions if a[0] == 0]


def compute_orbits_of_stab(stab, n_points=511):
    """Compute orbits of Stab(E11) on projective points."""
    parent = list(range(n_points + 1))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    def union(x, y):
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[rx] = ry
    for a in stab:
        for p in range(1, n_points + 1):
            union(p, a[p])
    orbits = {}
    for p in range(1, n_points + 1):
        r = find(p)
        if r not in orbits:
            orbits[r] = []
        orbits[r].append(p)
    return orbits


def build_and_solve(
    fixed_points: List[int],
    exclude_before_reps: List[int],
    rank_s: int,
    include_dims: List[int],
    through_fixed_dims: List[int],
    max_rank1_count: Optional[int],
    include_rank1_proj: bool,
    outdir: Path,
    solver_timeout: int = 3600,
    encoding: str = "seqcounter",
):
    """Build PySAT formula and solve with proof-producing CaDiCaL."""
    from pysat.card import CardEnc, EncType
    from pysat.formula import CNF
    
    t0 = time.time()
    outdir.mkdir(parents=True, exist_ok=True)
    
    enc_type = getattr(EncType, encoding, EncType.seqcounter)
    
    # Load data
    lut = load_lut()
    actions = make_actions()
    stab = compute_stab_e11(actions)
    orbits = compute_orbits_of_stab(stab)
    
    # Excluded orbits
    excluded = set()
    for rep in exclude_before_reps:
        for a in stab:
            excluded.add(a[rep])
    
    fixed_set = set(fixed_points)
    all_points = list(range(1, 2**N))
    decision_points = sorted(p for p in all_points if p not in fixed_set and p not in excluded)
    dp_set = set(decision_points)
    n_dp = len(decision_points)
    
    # Map point -> variable (1-indexed for SAT)
    point_to_var = {}
    for i, p in enumerate(decision_points):
        point_to_var[p] = i + 1
    
    rank1_set = set(p for p in all_points if matrix_rank_of_mask(p) == 1)
    
    formula = CNF()
    top_var = n_dp  # track highest variable used
    n_wang = 0
    n_trivial = 0
    n_unit = 0
    constraint_stats = {}
    
    # 1. Total support = rank_s - |fixed|
    target = rank_s - len(fixed_set)
    dp_lits = [point_to_var[p] for p in decision_points]
    
    # Encode: sum(dp_lits) = target  <=>  sum <= target AND sum >= target
    atmost = CardEnc.atmost(lits=dp_lits, bound=target, top_id=top_var, encoding=enc_type)
    top_var = max(top_var, atmost.nv)
    for cl in atmost.clauses:
        formula.append(cl)
    
    atleast = CardEnc.atleast(lits=dp_lits, bound=target, top_id=top_var, encoding=enc_type)
    top_var = max(top_var, atleast.nv)
    for cl in atleast.clauses:
        formula.append(cl)
    
    # 2. Wang constraints
    inc_dims_set = set(include_dims)
    thr_dims_set = set(through_fixed_dims) if through_fixed_dims else set()
    
    scan_count = 0
    for key, lb in lut.items():
        scan_count += 1
        if scan_count % 1_000_000 == 0:
            print(f"  scanned {scan_count:,}/{len(lut):,}; wang={n_wang}; elapsed={time.time()-t0:.1f}s",
                  file=sys.stderr, flush=True)
        
        basis = unpack_basis(key)
        dim = len(basis)
        cap = rank_s - lb
        
        # Filter by dimension
        in_direct = dim in inc_dims_set
        in_through = dim in thr_dims_set
        if in_through:
            for fp in fixed_points:
                if not in_rowspace(fp, basis):
                    in_through = False
                    break
        if not in_direct and not in_through:
            continue
        
        pts = subspace_points_from_basis(basis)
        fixed_in = sum(1 for fp in fixed_points if fp in set(pts))
        remaining_cap = cap - fixed_in
        
        dp_in = [point_to_var[p] for p in pts if p in dp_set]
        if not dp_in:
            continue
        
        if remaining_cap < 0:
            # Contradiction: add empty clause
            formula.append([dp_in[0], -dp_in[0]])  # force contradiction
            # Actually, add negation of all dp_in (impossible to satisfy with remaining_cap < 0)
            for v in dp_in:
                formula.append([-v])
            n_wang += 1
            continue
        
        if remaining_cap >= len(dp_in):
            n_trivial += 1
            continue
        
        if remaining_cap == 0:
            # All must be false
            for v in dp_in:
                formula.append([-v])
            n_unit += len(dp_in)
            n_wang += 1
            continue
        
        # Cardinality: at most remaining_cap of dp_in
        card = CardEnc.atmost(lits=dp_in, bound=remaining_cap, top_id=top_var, encoding=enc_type)
        top_var = max(top_var, card.nv)
        for cl in card.clauses:
            formula.append(cl)
        n_wang += 1
        
        dim_key = f"dim{dim}"
        constraint_stats[dim_key] = constraint_stats.get(dim_key, 0) + 1
    
    # 3. Rank-1 projection constraints
    n_r1proj = 0
    if include_rank1_proj:
        for key, lb in lut.items():
            basis = unpack_basis(key)
            cap = rank_s - lb
            pts = subspace_points_from_basis(basis)
            r1_pts = [p for p in pts if p in rank1_set]
            if len(r1_pts) > 9 or len(r1_pts) == 0:
                continue
            r1_fixed = sum(1 for fp in fixed_points if fp in rank1_set and fp in set(r1_pts))
            r1_cap = cap - r1_fixed
            r1_dp = [point_to_var[p] for p in r1_pts if p in dp_set]
            if not r1_dp or r1_cap >= len(r1_dp) or r1_cap < 0:
                continue
            card = CardEnc.atmost(lits=r1_dp, bound=r1_cap, top_id=top_var, encoding=enc_type)
            top_var = max(top_var, card.nv)
            for cl in card.clauses:
                formula.append(cl)
            n_r1proj += 1
    
    # 4. Max rank-1 count
    n_r1cnt = 0
    if max_rank1_count is not None:
        r1_dp_lits = [point_to_var[p] for p in decision_points if p in rank1_set]
        r1_fixed_cnt = sum(1 for fp in fixed_points if fp in rank1_set)
        r1_bound = max_rank1_count - r1_fixed_cnt
        if r1_bound < len(r1_dp_lits):
            card = CardEnc.atmost(lits=r1_dp_lits, bound=r1_bound, top_id=top_var, encoding=enc_type)
            top_var = max(top_var, card.nv)
            for cl in card.clauses:
                formula.append(cl)
            n_r1cnt = 1
    
    build_elapsed = time.time() - t0
    n_vars = top_var
    n_clauses = len(formula.clauses)
    
    print(f"Formula: {n_vars} vars, {n_clauses} clauses", file=sys.stderr)
    print(f"Wang constraints: {n_wang} (trivial skipped: {n_trivial}, unit: {n_unit})", file=sys.stderr)
    print(f"R1 projection: {n_r1proj}, R1 count: {n_r1cnt}", file=sys.stderr)
    print(f"Build time: {build_elapsed:.1f}s", file=sys.stderr)
    
    # Write DIMACS for external verification
    cnf_path = outdir / "formula.cnf"
    formula.to_file(str(cnf_path))
    
    # Solve with PySAT CaDiCaL + DRAT proof
    drat_path = outdir / "formula.drat"
    print(f"Starting CaDiCaL solve (timeout={solver_timeout}s)...", file=sys.stderr)
    
    from pysat.solvers import Cadical195
    
    t_solve = time.time()
    solver = Cadical195(bootstrap_with=formula, with_proof=True)
    
    # Set timeout via conf if possible
    result = solver.solve_limited(expect=0)  # expect UNSAT
    solve_elapsed = time.time() - t_solve
    
    status = "SAT" if result is True else ("UNSAT" if result is False else "UNKNOWN")
    print(f"Result: {status} in {solve_elapsed:.1f}s", file=sys.stderr)
    
    model = None
    if result is True:
        model = solver.get_model()
        # Decode support
        support = [decision_points[i] for i in range(n_dp) if model[i] > 0]
        model_path = outdir / "model.json"
        model_path.write_text(json.dumps({"support": support, "size": len(support)}, indent=2))
    
    if result is False:
        # Save DRAT proof
        proof = solver.get_proof()
        if proof:
            with drat_path.open('w') as f:
                for line in proof:
                    f.write(line + '\n')
            print(f"DRAT proof saved: {len(proof)} lines", file=sys.stderr)
        else:
            print("WARNING: No proof available", file=sys.stderr)
    
    solver.delete()
    
    # External DRAT verification if UNSAT
    drat_verified = False
    trim_log = None
    if result is False and drat_path.exists() and drat_path.stat().st_size > 0:
        trim_log_path = outdir / "formula.drat_trim.log"
        print("Running drat-trim verification...", file=sys.stderr)
        try:
            proc = subprocess.run(
                ["drat-trim", str(cnf_path), str(drat_path)],
                capture_output=True, text=True, timeout=600
            )
            trim_log_path.write_text(proc.stdout + proc.stderr)
            drat_verified = "s VERIFIED" in proc.stdout or "s VERIFIED" in proc.stderr
            print(f"drat-trim: {'VERIFIED' if drat_verified else 'NOT verified'}", file=sys.stderr)
        except subprocess.TimeoutExpired:
            print("drat-trim timed out", file=sys.stderr)
    
    total_elapsed = time.time() - t0
    
    meta = {
        "n_vars": n_vars,
        "n_clauses": n_clauses,
        "n_wang_constraints": n_wang,
        "n_trivial_skipped": n_trivial,
        "n_unit_clauses": n_unit,
        "n_r1_proj": n_r1proj,
        "n_r1_count": n_r1cnt,
        "constraint_stats": constraint_stats,
        "encoding": encoding,
        "build_elapsed_sec": build_elapsed,
        "solve_elapsed_sec": solve_elapsed,
        "total_elapsed_sec": total_elapsed,
        "status": status,
        "drat_verified": drat_verified,
        "fixed_points": fixed_points,
        "rank_s": rank_s,
        "include_dims": include_dims,
        "through_fixed_dims": through_fixed_dims,
        "hashes": {},
    }
    
    for p in [cnf_path, drat_path]:
        if p.exists():
            meta["hashes"][str(p)] = sha256(p)
    
    meta_path = outdir / "meta.json"
    meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True))
    
    print(json.dumps(meta, indent=2, sort_keys=True))
    return meta


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rep", type=int, required=True)
    ap.add_argument("--rank-s", type=int, default=20)
    ap.add_argument("--include-dims", type=str, default="1,2,3")
    ap.add_argument("--through-fixed-dims", type=str, default="4,5,6")
    ap.add_argument("--include-rank1-proj", action="store_true")
    ap.add_argument("--max-rank1", type=int, default=None)
    ap.add_argument("--exclude-before", type=str, default="",
                    help="Stab(E11) orbit reps whose orbits are excluded")
    ap.add_argument("--encoding", type=str, default="seqcounter",
                    choices=["seqcounter", "totalizer", "cardnetwrk", "ladder", "sortnetwrk"])
    ap.add_argument("--timeout", type=int, default=3600)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    
    inc_dims = [int(x) for x in args.include_dims.split(",")]
    thr_dims = [int(x) for x in args.through_fixed_dims.split(",") if x.strip()]
    excl = [int(x) for x in args.exclude_before.split(",") if x.strip()]
    
    build_and_solve(
        fixed_points=[1, args.rep],
        exclude_before_reps=excl,
        rank_s=args.rank_s,
        include_dims=inc_dims,
        through_fixed_dims=thr_dims,
        max_rank1_count=args.max_rank1,
        include_rank1_proj=args.include_rank1_proj,
        outdir=args.out,
        solver_timeout=args.timeout,
        encoding=args.encoding,
    )


if __name__ == "__main__":
    main()
