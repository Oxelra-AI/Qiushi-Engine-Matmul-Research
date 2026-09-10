#!/usr/bin/env python3
"""analysis: realize invariant pair-count witnesses by actual point subsets.

Input is the analysis invariant block-count CP-SAT output.  For a selected witness
(n_a, m_j), this script asks for an actual 19-point subset whose point-orbit
counts are n_a and whose unordered pair orbit counts are m_j.  Optionally it also
adds the complete E11 Wang occupation rows, yielding a focused support search
inside one invariant-count branch.

A realized support is rescanned against the complete Wang table.  Solver UNSAT or
UNKNOWN here is computational evidence only unless separately encoded/replayed.
"""
from __future__ import annotations

import argparse, json, sys, time
from collections import Counter
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import build_core_constraints, complete_core_wang_scan  # noqa: E402
from cert_trace_separator import full_violation_scan  # noqa: E402
from rlt_pair_lift import LUT_PATH, build_stabilizer, compute_pair_orbits, compute_point_orbits  # noqa: E402

DEFAULT_INPUT = ROOT / "workspace/data/invariant_pair_block/pair_block_triangles.json"
OUT = ROOT / "workspace/data/realized_pair_counts"


def points_from_bitset_intersect(bs: int, allowed: set[int]):
    pts=[]
    while bs:
        bit=bs & -bs
        p=bit.bit_length()
        if p in allowed:
            pts.append(p)
        bs ^= bit
    return pts


def main():
    from ortools.sat.python import cp_model
    ap=argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    ap.add_argument("--label", default="min_omitted")
    ap.add_argument("--with-wang", action="store_true")
    ap.add_argument("--out-dir", type=Path, default=OUT)
    ap.add_argument("--solver-time", type=float, default=180.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=660766)
    args=ap.parse_args()
    t0=time.time(); args.out_dir.mkdir(parents=True, exist_ok=True)
    data=json.loads(args.input.read_text())
    matches=[r for r in data["results"] if r["label"] == args.label]
    if not matches:
        raise SystemExit(f"label {args.label!r} not found")
    wit=matches[0]
    n=[int(v) for v in wit["n_by_point_orbit"]]
    m=[int(v) for v in wit["m_by_pair_orbit"]]

    perms=build_stabilizer(); pt_orb, point_orbits=compute_point_orbits(perms); pair_orb, pair_sizes, pair_ep, M=compute_pair_orbits(perms, pt_orb)
    allowed=[]
    for a,na in enumerate(n):
        if na:
            allowed.extend(point_orbits[a])
    allowed=sorted(int(p) for p in allowed)
    allowed_set=set(allowed)

    model=cp_model.CpModel()
    x={p:model.NewBoolVar(f"x_{p}") for p in allowed}
    by_orbit={a:[p for p in allowed if pt_orb[p]==a] for a in range(len(point_orbits))}
    for a,pts in by_orbit.items():
        model.Add(sum(x[p] for p in pts) == n[a])
    # Pair variables only for allowed pairs.
    z={}
    pair_count_expr=[[] for _ in range(M)]
    for i,p in enumerate(allowed):
        for q in allowed[i+1:]:
            var=model.NewBoolVar(f"z_{p}_{q}")
            z[(p,q)]=var
            model.Add(var <= x[p]); model.Add(var <= x[q]); model.Add(var >= x[p] + x[q] - 1)
            j=pair_orb[(p,q)]
            pair_count_expr[j].append(var)
    for j in range(M):
        if pair_count_expr[j] or m[j] != 0:
            model.Add(sum(pair_count_expr[j]) == m[j])

    lut_meta=None; complete_meta=None; records=None; wang_rows=0; trivial=0; empty=0; row_by_L=Counter(); row_by_dim=Counter()
    if args.with_wang:
        lut,lut_meta=load_lut(LUT_PATH)
        records,complete_meta=build_core_constraints(CoreQuotient(1), lut)
        for rec in records:
            L=int(rec["L"]); cap=19-L
            pts=points_from_bitset_intersect(int(rec["point_bitset"]), allowed_set)
            if not pts:
                empty += 1; continue
            if len(pts) <= cap:
                trivial += 1; continue
            model.Add(sum(x[p] for p in pts) <= cap)
            wang_rows += 1; row_by_L[L]+=1; row_by_dim[int(rec["dim8"])] += 1
    model.Minimize(sum(((p*101+args.seed)%1009)*x[p] for p in allowed))
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(args.solver_time); solver.parameters.num_search_workers=int(args.workers); solver.parameters.random_seed=int(args.seed)
    ts=time.time(); status=solver.Solve(model); solve_sec=time.time()-ts
    status_name=solver.StatusName(status)
    result={
        "schema":"realize_pair_count_witness_v1",
        "input":str(args.input),"label":args.label,"with_wang":args.with_wang,
        "n_by_point_orbit":n,"omitted_n_0_3":sum(n[:4]),"m_total":sum(m),"nonzero_m_orbits":sum(1 for v in m if v),
        "point_orbit_reps":[int(o[0]) for o in point_orbits],"point_orbit_sizes":[len(o) for o in point_orbits],
        "allowed_size":len(allowed),"allowed_points":allowed,
        "pair_variables":len(z),
        "wang_constraint_summary":{"rows_added":wang_rows,"trivial":trivial,"empty":empty,"by_L":{str(k):int(v) for k,v in sorted(row_by_L.items())},"by_dim8":{str(k):int(v) for k,v in sorted(row_by_dim.items())}},
        "parameters":{"solver_time":args.solver_time,"workers":args.workers,"seed":args.seed},
        "status":status_name,"solve_sec":round(solve_sec,3),
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        S=[p for p in allowed if solver.Value(x[p])]
        # Independent count check.
        n_check=[sum(1 for p in S if pt_orb[p]==a) for a in range(len(point_orbits))]
        m_check=[0]*M
        for i,p in enumerate(S):
            for q in S[i+1:]:
                m_check[pair_orb[(p,q)]] += 1
        result["solution"]={
            "A_cols":S,
            "n_check":n_check,
            "m_check_matches":m_check==m,
            "objective_value":float(solver.ObjectiveValue()),
        }
        if records is None:
            lut,lut_meta=load_lut(LUT_PATH); records,complete_meta=build_core_constraints(CoreQuotient(1), lut)
        scan=complete_core_wang_scan(f"realized_{args.label}", S, 19, records, max_head=20)
        full=full_violation_scan(S, records, 19)
        result["solution"].update({
            "complete_wang_scan":scan,
            "complete_violation_count_with_points":full["complete_violation_count"],
            "first_violations_with_points":full.get("violations",[])[:10],
        })
    result["elapsed_sec"]=round(time.time()-t0,3)
    name=f"realize_{args.label}_{'with_wang' if args.with_wang else 'counts_only'}.json"
    path=args.out_dir/name
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"out":str(path),"label":args.label,"with_wang":args.with_wang,"allowed_size":len(allowed),"pair_variables":len(z),"status":status_name,"solve_sec":result["solve_sec"],"solution":result.get("solution",{}).get("A_cols"),"violations":result.get("solution",{}).get("complete_wang_scan",{}).get("complete_violation_count"),"elapsed_sec":result["elapsed_sec"]},indent=2,sort_keys=True))

if __name__=="__main__":
    main()
