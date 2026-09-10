#!/usr/bin/env python3
"""Fixed-E11 branch CNF with all high-dimensional rows through the fixed pair.

This strengthens the analysis fixed-E11 rank-20 Wang occupation branches.  For a
second Stab(E11)-orbit representative q, the branch fixes both E11 and q and
omits earlier Stab(E11)-orbit points.  The formula encodes:
  * all Wang rows in selected low dimensions, normally 1,2,3;
  * all Wang rows in selected high dimensions whose subspace contains both fixed
    points E11 and q, normally 4,5,6,7,8;
  * optional seed rows from previous full-LUT scans, including rows missing the
    fixed pair.

Rows are simplified by the fixed selected points before encoding: if a row
already contains k fixed points, its residual capacity is (20-L)-k over the
remaining variables.  This avoids the one-SAT-witness-at-a-time loop and keeps
large high-dimensional row encodings smaller.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import pickle
import shutil
import subprocess
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Set, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import (  # noqa: E402
    in_rowspace,
    matrix_rank_of_mask,
    unpack_basis,
    subspace_points_from_basis,
)
from wang_capacity_cnf_e11_fixed import (  # noqa: E402
    E11,
    collect_violation_keys,
    parse_dims,
    stab_e11_orbits,
)


def load_lut(path: Path):
    with path.open("rb") as f:
        payload = pickle.load(f)
    return payload["lut"], payload.get("meta", {})


class DimacsWriter:
    def __init__(self, final_path: Path):
        self.final_path = final_path
        self.body_path = final_path.with_suffix(final_path.suffix + ".body.tmp")
        self.final_path.parent.mkdir(parents=True, exist_ok=True)
        self.fh = self.body_path.open("w")
        self.nclauses = 0
        self.empty_clause_count = 0

    def add_clause(self, clause: Sequence[int]):
        self.fh.write(" ".join(map(str, clause)) + " 0\n")
        self.nclauses += 1
        if not clause:
            self.empty_clause_count += 1

    def close_with_header(self, nv: int):
        self.fh.close()
        with self.final_path.open("w") as out:
            out.write(f"p cnf {nv} {self.nclauses}\n")
            with self.body_path.open("r") as body:
                shutil.copyfileobj(body, out, length=16 * 1024 * 1024)
        self.body_path.unlink(missing_ok=True)


def encode_atmost(writer: DimacsWriter, lits: List[int], bound: int, top_id: int):
    from pysat.card import CardEnc, EncType

    if bound < 0:
        writer.add_clause([])
        return top_id, 1, 0
    if len(lits) <= bound:
        return top_id, 0, 0
    enc = CardEnc.atmost(lits=lits, bound=bound, top_id=top_id, encoding=EncType.seqcounter)
    for cl in enc.clauses:
        writer.add_clause(cl)
    return enc.nv, len(enc.clauses), max(0, enc.nv - top_id)


def branch_universe(second_rep: int, exclude_orbits_before: bool = True):
    fixed_points = [E11]
    if second_rep != E11:
        fixed_points.append(second_rep)
    excluded_points: Set[int] = set()
    orbit_info = stab_e11_orbits()
    if exclude_orbits_before and second_rep != E11:
        found = False
        for orb in orbit_info:
            if orb["rep"] == second_rep:
                found = True
                break
            excluded_points.update(int(p) for p in orb["members"])
        if not found:
            raise ValueError(f"second_rep {second_rep} is not a Stab(E11) orbit representative")
        for p in fixed_points:
            excluded_points.discard(p)
    points = [p for p in range(1, 512) if p not in excluded_points]
    p_to_var = {p: i + 1 for i, p in enumerate(points)}
    fixed_set = set(fixed_points)
    return fixed_points, excluded_points, points, p_to_var, orbit_info


def choose_keys(lut: Dict[int, int], fixed_points: Sequence[int], include_dims: Set[int],
                through_fixed_dims: Set[int], through_e11_dims: Set[int],
                seed_keys: Set[int], seed_dims: Set[int]):
    keys: Set[int] = set()
    source_counter = Counter()
    fixed = list(fixed_points)
    for key in lut:
        d = key & 0xF
        take = False
        basis = None
        if d in include_dims:
            take = True
            source_counter["include_dim"] += 1
        if d in through_fixed_dims:
            basis = unpack_basis(key)
            if all(in_rowspace(p, basis, n=9) for p in fixed):
                take = True
                source_counter["through_fixed"] += 1
        if d in through_e11_dims:
            if basis is None:
                basis = unpack_basis(key)
            if in_rowspace(E11, basis, n=9):
                take = True
                source_counter["through_e11"] += 1
        if take:
            keys.add(key)
    for key in seed_keys:
        if key in lut and ((key & 0xF) in seed_dims):
            keys.add(key)
            source_counter["seed"] += 1
    return keys, source_counter


def generate(lut: Dict[int, int], lut_meta: dict, rank_s: int, second_rep: int,
             include_dims: Set[int], through_fixed_dims: Set[int], through_e11_dims: Set[int],
             seed_keys: Set[int], seed_dims: Set[int], cnf_path: Path, meta_path: Path,
             direct_point_limit: int, direct_comb_limit: int,
             exclude_orbits_before: bool = True) -> dict:
    from pysat.card import CardEnc, EncType

    t0 = time.time()
    fixed_points, excluded_points, points, p_to_var, orbit_info = branch_universe(second_rep, exclude_orbits_before)
    fixed_set = set(fixed_points)
    writer = DimacsWriter(cnf_path)
    top_id = len(points)

    # Units for the fixed selected points and global projective support size 20.
    for p in fixed_points:
        writer.add_clause([p_to_var[p]])
    enc = CardEnc.equals(lits=[p_to_var[p] for p in points], bound=rank_s, top_id=top_id, encoding=EncType.seqcounter)
    for cl in enc.clauses:
        writer.add_clause(cl)
    top_id = enc.nv

    keys, key_source_counter = choose_keys(lut, fixed_points, include_dims, through_fixed_dims, through_e11_dims, seed_keys, seed_dims)
    missing_seed_keys = sorted(k for k in seed_keys if k not in lut)

    rows_by_dim = Counter()
    rows_by_lb = Counter()
    rows_by_source_dim = Counter()
    row_var_hist = Counter()
    residual_cap_hist = Counter()
    fixed_in_row_hist = Counter()
    direct_rows = 0
    direct_clauses = 0
    card_rows = 0
    card_clauses = 0
    aux_vars = 0
    skipped_vacuous = 0
    empty_capacity_rows = 0
    max_comb_seen = 0

    for key in sorted(keys):
        lb = int(lut[key])
        cap = rank_s - lb
        basis = unpack_basis(key)
        pts_in = subspace_points_from_basis(basis)
        fixed_in = sum(1 for p in fixed_points if p in pts_in)  # small fixed list, exact membership not performance-critical
        cap_rem = cap - fixed_in
        row_lits = [p_to_var[p] for p in pts_in if (p in p_to_var and p not in fixed_set)]
        d = key & 0xF
        rows_by_dim[d] += 1
        rows_by_lb[lb] += 1
        row_var_hist[len(row_lits)] += 1
        residual_cap_hist[cap_rem] += 1
        fixed_in_row_hist[fixed_in] += 1
        if d in through_fixed_dims and fixed_in == len(fixed_points):
            rows_by_source_dim[("through_fixed", d)] += 1
        elif d in through_e11_dims and fixed_in >= 1:
            rows_by_source_dim[("through_e11", d)] += 1
        elif d in include_dims:
            rows_by_source_dim[("include_dim", d)] += 1
        else:
            rows_by_source_dim[("seed", d)] += 1

        if cap_rem < 0:
            writer.add_clause([])
            empty_capacity_rows += 1
            continue
        if len(row_lits) <= cap_rem:
            skipped_vacuous += 1
            continue
        combs = math.comb(len(row_lits), cap_rem + 1) if cap_rem + 1 <= len(row_lits) else 0
        max_comb_seen = max(max_comb_seen, combs)
        if len(row_lits) <= direct_point_limit and combs <= direct_comb_limit:
            for comb in itertools.combinations(row_lits, cap_rem + 1):
                writer.add_clause([-v for v in comb])
            direct_rows += 1
            direct_clauses += combs
        else:
            old = top_id
            top_id, ncl, naux = encode_atmost(writer, row_lits, cap_rem, top_id)
            card_rows += 1
            card_clauses += ncl
            aux_vars += naux
            if top_id < old:
                raise RuntimeError("top_id decreased")

    writer.close_with_header(top_id)

    second_orbit = None
    for i, orb in enumerate(orbit_info):
        if second_rep in orb["members"]:
            second_orbit = {"orbit_index": i, "rep": orb["rep"], "size": orb["size"], "rank_hist": orb["rank_hist"], "fixed_is_rep": second_rep == orb["rep"]}
            break

    payload = {
        "problem": "T-level Wang occupation fixed-E11 branch with all rows through fixed pair",
        "field": "F2",
        "rank_s": rank_s,
        "meaning": "E11 and the Stab(E11) second representative are fixed. All selected high-dimensional Wang rows containing this fixed pair are encoded at once; SAT witnesses still require a full LUT scan.",
        "cnf_path": str(cnf_path),
        "fixed_points": fixed_points,
        "fixed_second_orbit": second_orbit,
        "exclude_orbits_before": exclude_orbits_before,
        "variable_point_count": len(points),
        "variable_rank_hist": dict(sorted(Counter(matrix_rank_of_mask(p) for p in points).items())),
        "excluded_point_count": len(excluded_points),
        "excluded_rank_hist": dict(sorted(Counter(matrix_rank_of_mask(p) for p in excluded_points).items())),
        "include_dims": sorted(include_dims),
        "through_fixed_dims": sorted(through_fixed_dims),
        "through_e11_dims": sorted(through_e11_dims),
        "seed_dims": sorted(seed_dims),
        "seed_key_count_input": len(seed_keys),
        "seed_key_count_used": len([k for k in seed_keys if k in keys]),
        "missing_seed_keys_head": missing_seed_keys[:20],
        "key_source_counter": dict(sorted(key_source_counter.items())),
        "rows_total_encoded_or_seen": len(keys),
        "rows_by_dim": dict(sorted(rows_by_dim.items())),
        "rows_by_lb": dict(sorted(rows_by_lb.items())),
        "rows_by_source_dim": {f"{src},{d}": c for (src, d), c in sorted(rows_by_source_dim.items())},
        "row_var_count_hist": dict(sorted(row_var_hist.items())),
        "fixed_in_row_hist": dict(sorted(fixed_in_row_hist.items())),
        "residual_cap_hist": dict(sorted(residual_cap_hist.items())),
        "skipped_vacuous_rows": skipped_vacuous,
        "empty_capacity_rows": empty_capacity_rows,
        "direct_rows": direct_rows,
        "direct_capacity_clauses": direct_clauses,
        "cardinality_capacity_rows": card_rows,
        "cardinality_capacity_clauses": card_clauses,
        "capacity_aux_vars": aux_vars,
        "global_cardinality_clauses": len(enc.clauses),
        "explicit_fixed_unit_clauses": len(fixed_points),
        "num_vars": top_id,
        "num_clauses": writer.nclauses,
        "empty_clause_count": writer.empty_clause_count,
        "max_direct_comb_seen": max_comb_seen,
        "direct_point_limit": direct_point_limit,
        "direct_comb_limit": direct_comb_limit,
        "lut_meta_brief": {
            "coverage_ok": lut_meta.get("coverage_ok"),
            "conflict_count": lut_meta.get("conflict_count"),
            "subspace_count": lut_meta.get("subspace_count") or lut_meta.get("expected_subspace_count"),
            "action_count": lut_meta.get("action_count"),
        },
        "elapsed_sec": time.time() - t0,
    }
    meta_path.parent.mkdir(parents=True, exist_ok=True)
    meta_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps(payload, indent=2, sort_keys=True))
    return payload


def maybe_run_solver(cnf: Path, outdir: Path, time_limit: int) -> dict:
    outdir.mkdir(parents=True, exist_ok=True)
    stem = cnf.stem
    drat = outdir / f"{stem}.drat"
    cadical_log = outdir / f"{stem}.cadical.log"
    trim_log = outdir / f"{stem}.drat_trim.log"
    status = {"cnf": str(cnf), "drat": str(drat), "cadical_log": str(cadical_log), "drat_trim_log": str(trim_log)}
    cmd = ["cadical", "--unsat", "--binary=false", "-n"]
    if time_limit > 0:
        cmd.extend(["-t", str(time_limit)])
    cmd.extend([str(cnf), str(drat)])
    t0 = time.time()
    with cadical_log.open("w") as log:
        proc = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, text=True)
    status["cadical_exit"] = proc.returncode
    status["cadical_elapsed_sec"] = time.time() - t0
    if proc.returncode == 20:
        t1 = time.time()
        with trim_log.open("w") as log:
            trim = subprocess.run(["drat-trim", str(cnf), str(drat)], stdout=log, stderr=subprocess.STDOUT, text=True)
        status["drat_trim_exit"] = trim.returncode
        status["drat_trim_elapsed_sec"] = time.time() - t1
    else:
        status["drat_trim_exit"] = None
        status["drat_trim_elapsed_sec"] = None
    status_path = outdir / f"{stem}.status.json"
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps(status, indent=2, sort_keys=True))
    return status


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--rank", type=int, default=20)
    ap.add_argument("--second-rep", type=int, required=True)
    ap.add_argument("--include-dims", default="1,2,3")
    ap.add_argument("--through-fixed-dims", default="4-8")
    ap.add_argument("--through-e11-dims", default="", help="Optional higher dimensions for all Wang rows containing E11, not necessarily the second fixed point")
    ap.add_argument("--seed-dims", default="4-7")
    ap.add_argument("--seed-json", type=Path, action="append", default=[])
    ap.add_argument("--cnf", type=Path, required=True)
    ap.add_argument("--meta", type=Path, required=True)
    ap.add_argument("--direct-point-limit", type=int, default=7)
    ap.add_argument("--direct-comb-limit", type=int, default=100000)
    ap.add_argument("--no-exclude-orbits-before", action="store_true")
    ap.add_argument("--solve", action="store_true")
    ap.add_argument("--solver-time", type=int, default=0)
    ap.add_argument("--solver-outdir", type=Path, default=None)
    args = ap.parse_args()

    lut, lut_meta = load_lut(args.lut)
    print(f"loaded LUT {len(lut):,} coverage={lut_meta.get('coverage_ok')} conflicts={lut_meta.get('conflict_count')}")
    seed_keys: Set[int] = set()
    for p in args.seed_json:
        got = collect_violation_keys(p)
        print(f"seed {p}: {len(got)} keys")
        seed_keys.update(got)
    generate(
        lut=lut,
        lut_meta=lut_meta,
        rank_s=args.rank,
        second_rep=args.second_rep,
        include_dims=parse_dims(args.include_dims),
        through_fixed_dims=parse_dims(args.through_fixed_dims),
        through_e11_dims=parse_dims(args.through_e11_dims),
        seed_keys=seed_keys,
        seed_dims=parse_dims(args.seed_dims),
        cnf_path=args.cnf,
        meta_path=args.meta,
        direct_point_limit=args.direct_point_limit,
        direct_comb_limit=args.direct_comb_limit,
        exclude_orbits_before=not args.no_exclude_orbits_before,
    )
    if args.solve:
        maybe_run_solver(args.cnf, args.solver_outdir or args.cnf.parent, args.solver_time)


if __name__ == "__main__":
    main()
