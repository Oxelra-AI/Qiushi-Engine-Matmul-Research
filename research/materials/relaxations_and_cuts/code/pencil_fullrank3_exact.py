#!/usr/bin/env python3
r"""analysis: summary for a representative low-rank pencil line.

The line [1,2,3] is a representative where the explicit block-diagonal pencil
envelope is stricter than the three individual contraction rank inequalities on
very small budgets.  This script collects the fast block-envelope boundary and
CP-SAT factorization outcomes for that representative.  It is a bookkeeping
summary of computations already run, not an independent proof-producing
certificate.

It is not used as a support cut for the E11 distinct branch; all-rank-3 lines
are weak contraction lines compared with the Wang rows already in use.  The
purpose is to preserve a correct mathematical distinction: the pencil condition
can be stronger than individual rank bounds for degenerate low-rank lines, while
it did not support the analysis all-rank-9 negative claims.
"""
from __future__ import annotations

import json
from itertools import product
from pathlib import Path
from typing import Iterable, List, Tuple

import numpy as np

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/pencil_repair"


def rank_diag(bits: Tuple[int,int,int]) -> int:
    return sum(bits)


def minimal_triples(triples: Iterable[Tuple[int,int,int]]) -> List[Tuple[int,int,int]]:
    ts = sorted(set(triples)); out=[]
    for t in ts:
        if not any(all(u[i] <= t[i] for i in range(3)) and any(u[i] < t[i] for i in range(3)) for u in ts if u != t):
            out.append(t)
    return out


def main() -> None:
    # For line [1,2,3], after grouping, M1=diag(1,1,1) on the three active scalar
    # coordinates for the first A coordinate, M2 likewise on a disjoint/second scalar
    # coordinate.  Equivalently the 3 blocks are 1x1 pairs (1,0)/(0,1) in the active
    # scalar component plus zero rows/columns; the rank contribution of each block
    # under a scalar z is exactly one of (rank(1+z), rank(z), rank(z)) etc.  The
    # analysis CP-SAT file stores the solver check.  Here we preserve the minimal
    # boundary already computed by the block-envelope engine for [1,2,3].
    # Direct scalar budget boundary from the fast boundary output:
    boundary_path = OUTDIR / "pencil_boundary_fast.json"
    boundary = json.loads(boundary_path.read_text())
    line_rec = boundary["failure_head"][0]
    assert line_rec["line"] == [1,2,3]
    cpsat_path = OUTDIR / "pencil_factor_cpsat_line_1_2_3.json"
    cpsat = json.loads(cpsat_path.read_text()) if cpsat_path.exists() else {}
    out = {
        "schema": "fullrank3_exact_summary_v1",
        "line": [1,2,3],
        "individual_minimal": line_rec["individual_minimal"],
        "block_pencil_minimal": line_rec["env_minimal"],
        "missing_individual_minimal_budgets": line_rec["missing_head"],
        "cpsat_factorization_results_for_missing_budgets": cpsat.get("results", []),
        "interpretation": "For this all-rank-3 dual line the pencil rank condition is strictly stronger than the three individual contraction ranks on the listed tiny budgets. This does not rescue analysis all-rank-9 exclusions and is not a global distinct-branch proof.",
    }
    out_path = OUTDIR / "pencil_lowrank_line_1_2_3_summary.json"
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(out_path), "missing": out["missing_individual_minimal_budgets"], "cpsat_statuses": [r.get('status') for r in out['cpsat_factorization_results_for_missing_budgets']]}, indent=2))

if __name__ == "__main__":
    main()
