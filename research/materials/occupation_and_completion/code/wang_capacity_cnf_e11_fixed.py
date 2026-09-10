#!/usr/bin/env python3
"""Generate DIMACS formulas for the remaining T-level Wang rank-20 branch.

This instrument encodes the F2 occupation problem after fixing an A-side rank-1
factor to E11.  A hypothetical rank-20 decomposition of T_<3,3,3> has 20
projective A-factors.  Wang's verified lower-bound table gives necessary rows

    |support ∩ Phi| <= 20 - L(Phi)

for every A-side constraint subspace Phi in the expanded LUT.  analysis already
proved the branches with no rank-1 A-factor UNSAT.  The remaining branch fixes
E11 and then breaks the residual Stab(E11) symmetry by fixing a second point
representative from one of the eight Stab(E11) orbits on the other 510 points.

The script can seed a subbranch with all low-dimensional rows, all selected
whole dimensions such as dim 8, and selected higher-dimensional violated rows
learned from earlier solver candidates.  Large capacity rows are encoded with
sequential counters rather than direct forbidden-subset expansion.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import os
import pickle
import shutil
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Set, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import (  # noqa: E402
    make_actions,
    transform_mask,
    matrix_rank_of_mask,
    unpack_basis,
    subspace_points_from_basis,
)

E11 = 1


def load_lut(path: Path) -> Tuple[Dict[int, int], dict]:
    with path.open("rb") as f:
        payload = pickle.load(f)
    return payload["lut"], payload.get("meta", {})


def parse_dims(spec: str) -> Set[int]:
    out: Set[int] = set()
    for part in spec.split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            a, b = map(int, part.split("-", 1))
            out.update(range(a, b + 1))
        else:
            out.add(int(part))
    return out


def stab_e11_orbits() -> List[dict]:
    actions = make_actions()
    stab = [img for img in actions if transform_mask(E11, img) == E11]
    unseen = set(range(1, 512))
    unseen.remove(E11)
    orbits = []
    while unseen:
        rep = min(unseen)
        members = {transform_mask(rep, img) for img in stab}
        assert rep in members
        ranks = Counter(matrix_rank_of_mask(p) for p in members)
        orbits.append({
            "rep": rep,
            "size": len(members),
            "rank_hist": dict(sorted(ranks.items())),
            "members": sorted(members),
        })
        unseen -= members
    orbits.sort(key=lambda o: o["rep"])
    return orbits


def collect_violation_keys(path: Path) -> Set[int]:
    data = json.loads(path.read_text())
    keys: Set[int] = set()

    def visit(obj):
        if isinstance(obj, dict):
            if "key" in obj and "dim" in obj and "lb" in obj:
                try:
                    keys.add(int(obj["key"]))
                except Exception:
                    pass
            for v in obj.values():
                visit(v)
        elif isinstance(obj, list):
            for v in obj:
                visit(v)

    visit(data)
    return keys


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


def generate(lut: Dict[int, int], meta: dict, rank_s: int, fixed_second: int,
             include_dims: Set[int], seed_keys: Set[int], seed_dims: Set[int],
             cnf_path: Path, meta_path: Path, direct_point_limit: int,
             direct_comb_limit: int, exclude_orbits_before: bool) -> dict:
    from pysat.card import CardEnc, EncType

    t0 = time.time()
    orbit_info = stab_e11_orbits()
    fixed_points = [E11]
    if fixed_second != E11:
        fixed_points.append(fixed_second)

    excluded_points: Set[int] = set()
    if exclude_orbits_before and fixed_second != E11:
        seen_before = True
        for orb in orbit_info:
            if orb["rep"] == fixed_second:
                seen_before = False
                break
            excluded_points.update(int(p) for p in orb["members"])
        if seen_before:
            raise ValueError(f"fixed_second {fixed_second} is not a Stab(E11) orbit representative")
        for p in fixed_points:
            excluded_points.discard(p)

    # Omit excluded earlier-orbit points from the variable universe rather than
    # adding many unit clauses.  This is equivalent to the invariant-parent
    # branch and makes later Stab(E11) subbranches much smaller.
    points = [p for p in range(1, 512) if p not in excluded_points]
    for p in fixed_points:
        if p not in points:
            raise ValueError(f"fixed point {p} was excluded from branch")
    p_to_var = {p: i + 1 for i, p in enumerate(points)}
    var_to_point = {i + 1: p for i, p in enumerate(points)}
    top_id = len(points)
    writer = DimacsWriter(cnf_path)

    for p in fixed_points:
        writer.add_clause([p_to_var[p]])

    allowed_lits = [p_to_var[p] for p in points]
    enc = CardEnc.equals(lits=allowed_lits, bound=rank_s, top_id=top_id, encoding=EncType.seqcounter)
    for cl in enc.clauses:
        writer.add_clause(cl)
    global_cardinality_clauses = len(enc.clauses)
    top_id = enc.nv

    all_keys: Set[int] = set()
    for key in lut:
        if (key & 0xF) in include_dims:
            all_keys.add(key)
    for key in seed_keys:
        if key in lut and ((key & 0xF) in seed_dims):
            all_keys.add(key)

    stats = Counter()
    rows_by_dim = Counter()
    rows_by_lb = Counter()
    row_var_hist = Counter()
    cap_hist = Counter()
    direct_clause_count = 0
    card_clause_count = 0
    card_constraint_count = 0
    aux_var_count = 0
    skipped_vacuous = 0
    missing_seed_keys = sorted(k for k in seed_keys if k not in lut)

    for key in sorted(all_keys):
        lb = int(lut[key])
        cap = rank_s - lb
        basis = unpack_basis(key)
        row_lits = [p_to_var[p] for p in subspace_points_from_basis(basis) if p in p_to_var]
        d = key & 0xF
        rows_by_dim[d] += 1
        rows_by_lb[lb] += 1
        row_var_hist[len(row_lits)] += 1
        cap_hist[cap] += 1
        if cap < 0:
            writer.add_clause([])
            stats["empty_capacity_rows"] += 1
            continue
        if len(row_lits) <= cap:
            skipped_vacuous += 1
            continue
        combs = math.comb(len(row_lits), cap + 1) if cap + 1 <= len(row_lits) else 0
        if len(row_lits) <= direct_point_limit and combs <= direct_comb_limit:
            for comb in itertools.combinations(row_lits, cap + 1):
                writer.add_clause([-v for v in comb])
            direct_clause_count += combs
            stats["direct_rows"] += 1
        else:
            old_top = top_id
            top_id, ncl, naux = encode_atmost(writer, row_lits, cap, top_id)
            card_clause_count += ncl
            aux_var_count += naux
            card_constraint_count += 1
            stats["card_rows"] += 1
            if top_id < old_top:
                raise RuntimeError("top_id moved backward")

    writer.close_with_header(top_id)
    fixed_second_orbit = None
    for i, orb in enumerate(orbit_info):
        if fixed_second in orb["members"]:
            fixed_second_orbit = {
                "orbit_index": i,
                "rep": orb["rep"],
                "size": orb["size"],
                "rank_hist": orb["rank_hist"],
                "fixed_is_rep": fixed_second == orb["rep"],
            }
            break

    payload = {
        "problem": "T-level Wang occupation branch with E11 fixed",
        "field": "F2",
        "rank_s": rank_s,
        "meaning": "E11 fixed plus a second Stab(E11)-orbit representative; UNSAT over all second orbits excludes the remaining rank-20 A-support branch.",
        "cnf_path": str(cnf_path),
        "fixed_points": fixed_points,
        "fixed_second_orbit": fixed_second_orbit,
        "exclude_orbits_before": exclude_orbits_before,
        "variable_point_count": len(points),
        "variable_rank_hist": dict(sorted(Counter(matrix_rank_of_mask(p) for p in points).items())),
        "excluded_point_count": len(excluded_points),
        "excluded_rank_hist": dict(sorted(Counter(matrix_rank_of_mask(p) for p in excluded_points).items())),
        "include_dims": sorted(include_dims),
        "seed_dims": sorted(seed_dims),
        "seed_key_count_input": len(seed_keys),
        "seed_key_count_used": len([k for k in seed_keys if k in all_keys]),
        "missing_seed_keys_head": missing_seed_keys[:20],
        "rows_total_encoded_or_seen": len(all_keys),
        "rows_by_dim": dict(sorted(rows_by_dim.items())),
        "rows_by_lb": dict(sorted(rows_by_lb.items())),
        "row_var_count_hist": dict(sorted(row_var_hist.items())),
        "cap_hist": dict(sorted(cap_hist.items())),
        "skipped_vacuous_rows": skipped_vacuous,
        "direct_rows": int(stats["direct_rows"]),
        "direct_capacity_clauses": direct_clause_count,
        "cardinality_capacity_rows": card_constraint_count,
        "cardinality_capacity_clauses": card_clause_count,
        "capacity_aux_vars": aux_var_count,
        "global_cardinality_clauses": global_cardinality_clauses,
        "explicit_fixed_unit_clauses": len(fixed_points),
        "note_on_exclusions": "Earlier Stab(E11)-orbit points are omitted from the variable universe, not encoded as explicit unit clauses.",
        "num_vars": top_id,
        "num_clauses": writer.nclauses,
        "empty_clause_count": writer.empty_clause_count,
        "lut_meta_brief": {
            "coverage_ok": meta.get("coverage_ok"),
            "conflict_count": meta.get("conflict_count"),
            "subspace_count": meta.get("subspace_count") or meta.get("expected_subspace_count"),
            "action_count": meta.get("action_count"),
        },
        "direct_point_limit": direct_point_limit,
        "direct_comb_limit": direct_comb_limit,
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
    status_path = outdir / f"{stem}.status.json"
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps(status, indent=2, sort_keys=True))
    return status


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--rank", type=int, default=20)
    ap.add_argument("--list-orbits", action="store_true")
    ap.add_argument("--second-rep", type=int, default=None, help="Stab(E11)-orbit representative to fix in addition to E11")
    ap.add_argument("--include-dims", default="1,2,3,8")
    ap.add_argument("--seed-dims", default="4-7")
    ap.add_argument("--seed-json", type=Path, action="append", default=[])
    ap.add_argument("--cnf", type=Path, default=None)
    ap.add_argument("--meta", type=Path, default=None)
    ap.add_argument("--direct-point-limit", type=int, default=7)
    ap.add_argument("--direct-comb-limit", type=int, default=100000)
    ap.add_argument("--exclude-orbits-before", action="store_true")
    ap.add_argument("--solve", action="store_true")
    ap.add_argument("--solver-time", type=int, default=0)
    ap.add_argument("--solver-outdir", type=Path, default=None)
    args = ap.parse_args()

    if args.list_orbits:
        print(json.dumps({"stab_E11_orbits": stab_e11_orbits()}, indent=2, sort_keys=True))
        return
    if args.second_rep is None:
        raise SystemExit("--second-rep is required unless --list-orbits is used")
    if args.cnf is None or args.meta is None:
        raise SystemExit("--cnf and --meta are required")

    lut, meta = load_lut(args.lut)
    print(f"loaded LUT {len(lut):,} coverage={meta.get('coverage_ok')} conflicts={meta.get('conflict_count')}")
    seed_keys: Set[int] = set()
    for p in args.seed_json:
        got = collect_violation_keys(p)
        print(f"seed {p}: {len(got)} keys")
        seed_keys.update(got)
    payload = generate(
        lut=lut,
        meta=meta,
        rank_s=args.rank,
        fixed_second=args.second_rep,
        include_dims=parse_dims(args.include_dims),
        seed_keys=seed_keys,
        seed_dims=parse_dims(args.seed_dims),
        cnf_path=args.cnf,
        meta_path=args.meta,
        direct_point_limit=args.direct_point_limit,
        direct_comb_limit=args.direct_comb_limit,
        exclude_orbits_before=args.exclude_orbits_before,
    )
    if args.solve:
        outdir = args.solver_outdir or args.cnf.parent
        status = maybe_run_solver(args.cnf, outdir, args.solver_time)
        payload["solver_status_path"] = str(outdir / f"{args.cnf.stem}.status.json")


if __name__ == "__main__":
    main()
