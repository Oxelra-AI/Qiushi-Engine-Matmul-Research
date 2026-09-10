#!/usr/bin/env python3
"""UNSAT core extraction then DRAT proof for Wang capacity problem.

Strategy:
  1. Encode all constraints with indicator assumptions
  2. Solve with PySAT CaDiCaL to get UNSAT + core
  3. Rebuild the formula with ONLY core constraints (no indicators)
  4. Get DRAT proof from clean CaDiCaL
  5. Verify with drat-trim

This dramatically reduces formula size since most constraints are redundant.
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
from typing import Dict, List, Set, Optional, Tuple

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
    return data['lut']


def compute_stab_e11(actions):
    return [a for a in actions if a[0] == 0]


def build_constraint_list(
    fixed_points, excluded_points, rank_s, include_dims, through_fixed_dims,
    max_rank1_count, include_rank1_proj, rank1_max_int_size=9,
):
    """Build list of (dp_lits, cap) tuples for all constraints."""
    from pysat.card import CardEnc, EncType
    
    lut = load_lut()
    fixed_set = set(fixed_points)
    excl_set = set(excluded_points)
    all_points = list(range(1, 2**N))
    decision_points = sorted(p for p in all_points if p not in fixed_set and p not in excl_set)
    dp_set = set(decision_points)
    
    rank1_set = set(p for p in all_points if matrix_rank_of_mask(p) == 1)
    
    point_to_var = {p: i+1 for i, p in enumerate(decision_points)}
    n_dp = len(decision_points)
    
    constraints = []  # (lits, cap, label)
    
    # Total support = rank_s - |fixed|
    target = rank_s - len(fixed_set)
    all_lits = [point_to_var[p] for p in decision_points]
    constraints.append((all_lits, target, "total_atmost"))
    constraints.append((all_lits, -target, "total_atleast"))  # negative cap = atleast
    
    inc_dims_set = set(include_dims) if include_dims else set()
    thr_dims_set = set(through_fixed_dims) if through_fixed_dims else set()
    
    # Wang constraints
    for key, lb in lut.items():
        basis = unpack_basis(key)
        dim = len(basis)
        cap = rank_s - lb
        
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
        if not dp_in or remaining_cap >= len(dp_in):
            continue
        
        if remaining_cap < 0:
            constraints.append(([], -1, f"wang_impossible_{key}"))
            continue
        
        constraints.append((dp_in, remaining_cap, f"wang_{key}_dim{dim}_cap{remaining_cap}"))
    
    # Rank-1 projection constraints
    if include_rank1_proj:
        for key, lb in lut.items():
            basis = unpack_basis(key)
            cap = rank_s - lb
            pts = subspace_points_from_basis(basis)
            r1_pts = [p for p in pts if p in rank1_set]
            if len(r1_pts) > rank1_max_int_size or len(r1_pts) == 0:
                continue
            r1_fixed = sum(1 for fp in fixed_points if fp in rank1_set and fp in set(r1_pts))
            r1_remaining = cap - r1_fixed
            r1_dp = [point_to_var[p] for p in r1_pts if p in dp_set]
            if not r1_dp or r1_remaining >= len(r1_dp) or r1_remaining < 0:
                continue
            constraints.append((r1_dp, r1_remaining, f"r1proj_{key}"))
    
    # Max rank-1 count
    if max_rank1_count is not None:
        r1_dp_lits = [point_to_var[p] for p in decision_points if p in rank1_set]
        r1_fixed = sum(1 for fp in fixed_points if fp in rank1_set)
        r1_bound = max_rank1_count - r1_fixed
        if r1_bound < len(r1_dp_lits):
            constraints.append((r1_dp_lits, r1_bound, "r1_max"))
    
    return constraints, decision_points, n_dp, point_to_var


def encode_with_indicators(constraints, n_dp):
    """Encode constraints with indicator assumptions for core extraction."""
    from pysat.card import CardEnc, EncType
    from pysat.formula import CNF
    
    formula = CNF()
    top_var = n_dp
    indicators = []
    
    for idx, (lits, cap, label) in enumerate(constraints):
        ind = top_var + 1  # indicator variable
        top_var += 1
        indicators.append(ind)
        
        if cap < 0 and not lits:
            # Impossible constraint: ind -> FALSE
            formula.append([-ind])
            continue
        
        if cap < 0:
            # Atleast constraint: at least abs(cap) of lits
            atleast = CardEnc.atleast(lits=lits, bound=abs(cap), top_id=top_var, 
                                       encoding=EncType.seqcounter)
            top_var = max(top_var, atleast.nv)
            for cl in atleast.clauses:
                formula.append([-ind] + list(cl))
        elif cap == 0:
            # All must be false
            for v in lits:
                formula.append([-ind, -v])
        else:
            # Atmost constraint
            atmost = CardEnc.atmost(lits=lits, bound=cap, top_id=top_var,
                                     encoding=EncType.seqcounter)
            top_var = max(top_var, atmost.nv)
            for cl in atmost.clauses:
                formula.append([-ind] + list(cl))
    
    return formula, indicators, top_var


def encode_core_clean(constraints, core_indices, n_dp):
    """Encode only core constraints without indicators for DRAT."""
    from pysat.card import CardEnc, EncType
    from pysat.formula import CNF
    
    formula = CNF()
    top_var = n_dp
    
    for idx in core_indices:
        lits, cap, label = constraints[idx]
        
        if cap < 0 and not lits:
            formula.append([])  # empty clause
            continue
        
        if cap < 0:
            atleast = CardEnc.atleast(lits=lits, bound=abs(cap), top_id=top_var,
                                       encoding=EncType.seqcounter)
            top_var = max(top_var, atleast.nv)
            for cl in atleast.clauses:
                formula.append(cl)
        elif cap == 0:
            for v in lits:
                formula.append([-v])
        else:
            atmost = CardEnc.atmost(lits=lits, bound=cap, top_id=top_var,
                                     encoding=EncType.seqcounter)
            top_var = max(top_var, atmost.nv)
            for cl in atmost.clauses:
                formula.append(cl)
    
    return formula, top_var


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rep", type=int, required=True)
    ap.add_argument("--rank-s", type=int, default=20)
    ap.add_argument("--include-dims", type=str, default="1")
    ap.add_argument("--through-fixed-dims", type=str, default="4,6")
    ap.add_argument("--max-rank1", type=int, default=18)
    ap.add_argument("--include-rank1-proj", action="store_true", default=True)
    ap.add_argument("--exclude-before", type=str, default="")
    ap.add_argument("--core-timeout", type=int, default=600, help="seconds for core extraction")
    ap.add_argument("--drat-timeout", type=int, default=3600, help="seconds for DRAT proof")
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    
    t0 = time.time()
    args.out.mkdir(parents=True, exist_ok=True)
    
    inc_dims = [int(x) for x in args.include_dims.split(",") if x.strip()]
    thr_dims = [int(x) for x in args.through_fixed_dims.split(",") if x.strip()]
    
    actions = make_actions()
    stab = compute_stab_e11(actions)
    excluded = set()
    if args.exclude_before:
        for rep in [int(x) for x in args.exclude_before.split(",") if x.strip()]:
            for a in stab:
                excluded.add(a[rep])
    
    fixed = [1, args.rep]
    
    print("Building constraint list...", file=sys.stderr)
    constraints, dec_pts, n_dp, pt2var = build_constraint_list(
        fixed, excluded, args.rank_s, inc_dims, thr_dims,
        args.max_rank1, args.include_rank1_proj,
    )
    print(f"Total constraints: {len(constraints)}, decision vars: {n_dp}", file=sys.stderr)
    
    # Phase 1: Core extraction with indicator-based CaDiCaL
    print("Phase 1: Encoding with indicators for core extraction...", file=sys.stderr)
    formula_ind, indicators, top_var = encode_with_indicators(constraints, n_dp)
    print(f"Indicator formula: {top_var} vars, {len(formula_ind.clauses)} clauses", file=sys.stderr)
    
    from pysat.solvers import Cadical195
    
    t_core = time.time()
    solver = Cadical195(bootstrap_with=formula_ind)
    result = solver.solve(assumptions=indicators)
    core_time = time.time() - t_core
    
    if result is True:
        print("SATISFIABLE - no core to extract", file=sys.stderr)
        model = solver.get_model()
        support = [dec_pts[i] for i in range(n_dp) if model[i] > 0]
        solver.delete()
        meta = {"status": "SAT", "support": support, "elapsed_sec": time.time()-t0}
        (args.out / "meta.json").write_text(json.dumps(meta, indent=2))
        print(json.dumps(meta, indent=2))
        return
    
    if result is None:
        print("UNKNOWN during core extraction", file=sys.stderr)
        solver.delete()
        meta = {"status": "UNKNOWN", "elapsed_sec": time.time()-t0}
        (args.out / "meta.json").write_text(json.dumps(meta, indent=2))
        print(json.dumps(meta, indent=2))
        return
    
    # UNSAT - extract core
    core = solver.get_core()
    solver.delete()
    
    if core is None:
        print("UNSAT but no core available", file=sys.stderr)
        return
    
    core_set = set(abs(c) for c in core)
    core_indices = [i for i, ind in enumerate(indicators) if ind in core_set]
    
    print(f"UNSAT core: {len(core_indices)} of {len(constraints)} constraints "
          f"(extraction time: {core_time:.1f}s)", file=sys.stderr)
    
    # Save core info
    core_labels = [constraints[i][2] for i in core_indices]
    core_info_path = args.out / "core_info.json"
    core_info_path.write_text(json.dumps({
        "core_size": len(core_indices),
        "total_constraints": len(constraints),
        "core_labels": core_labels[:500],
        "core_extraction_sec": core_time,
    }, indent=2))
    
    # Phase 2: Build clean formula from core only and get DRAT
    print(f"\nPhase 2: Building clean formula from {len(core_indices)} core constraints...", 
          file=sys.stderr)
    formula_clean, clean_top = encode_core_clean(constraints, core_indices, n_dp)
    print(f"Clean formula: {clean_top} vars, {len(formula_clean.clauses)} clauses", file=sys.stderr)
    
    cnf_path = args.out / "core.cnf"
    formula_clean.to_file(str(cnf_path))
    
    # Solve clean formula with standalone CaDiCaL for DRAT proof
    drat_path = args.out / "core.drat"
    cad_log_path = args.out / "core.cadical.log"
    
    print(f"Running CaDiCaL on clean formula (timeout={args.drat_timeout}s)...", file=sys.stderr)
    t_drat = time.time()
    try:
        proc = subprocess.run(
            ["cadical", "--unsat", "--binary=false", "-n",
             str(cnf_path), str(drat_path)],
            capture_output=True, text=True, timeout=args.drat_timeout
        )
        cad_log_path.write_text(proc.stdout + proc.stderr)
        cad_exit = proc.returncode
    except subprocess.TimeoutExpired:
        cad_exit = -1
        print("CaDiCaL timed out", file=sys.stderr)
    
    drat_time = time.time() - t_drat
    cad_status = "UNSAT" if cad_exit == 20 else ("SAT" if cad_exit == 10 else f"EXIT_{cad_exit}")
    print(f"CaDiCaL: {cad_status} in {drat_time:.1f}s", file=sys.stderr)
    
    # Phase 3: DRAT verification
    drat_verified = False
    trim_log_path = args.out / "core.drat_trim.log"
    if cad_exit == 20 and drat_path.exists():
        print("Running drat-trim verification...", file=sys.stderr)
        try:
            trim = subprocess.run(
                ["drat-trim", str(cnf_path), str(drat_path)],
                capture_output=True, text=True, timeout=600
            )
            trim_log_path.write_text(trim.stdout + trim.stderr)
            drat_verified = "s VERIFIED" in trim.stdout or "s VERIFIED" in trim.stderr
            print(f"drat-trim: {'VERIFIED' if drat_verified else 'NOT verified'}", file=sys.stderr)
        except subprocess.TimeoutExpired:
            print("drat-trim timed out", file=sys.stderr)
    
    total_elapsed = time.time() - t0
    
    meta = {
        "status": cad_status,
        "drat_verified": drat_verified,
        "core_size": len(core_indices),
        "total_constraints": len(constraints),
        "clean_vars": clean_top,
        "clean_clauses": len(formula_clean.clauses),
        "core_extraction_sec": core_time,
        "drat_solve_sec": drat_time,
        "total_elapsed_sec": total_elapsed,
        "fixed_points": fixed,
        "rank_s": args.rank_s,
        "include_dims": inc_dims,
        "through_fixed_dims": thr_dims,
        "hashes": {},
    }
    
    for p in [cnf_path, drat_path, trim_log_path]:
        if p.exists() and p.stat().st_size > 0:
            meta["hashes"][p.name] = sha256(p)
    
    meta_path = args.out / "meta.json"
    meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True))
    print(json.dumps(meta, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
