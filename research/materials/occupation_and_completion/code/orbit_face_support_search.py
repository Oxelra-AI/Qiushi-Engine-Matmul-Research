#!/usr/bin/env python3
"""analysis: integer support search restricted by E11 stabilizer point-orbit mask.

This tests heuristic orbit faces suggested by invariant relaxations.  It is not a
global exhaustive argument unless all orbit-count branches are covered elsewhere.
Any feasible support is rescanned against the complete Wang table and passed
through the fixed-A necessary filters.
"""
from __future__ import annotations

import argparse, json, sys, time
from collections import Counter
from pathlib import Path

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from complete_core_and_transversal import ROOT as ROOT2, build_core_constraints, complete_core_wang_scan, saturation_domains, transversal_failures  # noqa: E402
from candidate_source_qcut_scan import eval_candidate_sources  # noqa: E402
from quotient_rank_cuts import build_contractions, point_mask_for_q  # noqa: E402
from cert_trace_separator import full_violation_scan  # noqa: E402
from trace_dependency_family import eval_support_local_dependency, trace_mask_correct  # noqa: E402
from dual_basis_instrument import gf2_mat_inv  # noqa: E402
from fixed_A_saturation import contraction_matrix, mat_rank_f2  # noqa: E402
from rlt_pair_lift import build_stabilizer, compute_point_orbits  # noqa: E402

LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"
OUT = ROOT / "workspace/data/orbit_face_support_search"


def points_from_bitset_intersect(bs: int, allowed: set[int]):
    pts=[]
    while bs:
        bit=bs & -bs
        p=bit.bit_length()
        if p in allowed:
            pts.append(p)
        bs ^= bit
    return pts


def build_phi(T_core):
    phi={}
    for q in range(1,1<<8):
        M=contraction_matrix(T_core,q)
        if mat_rank_f2(M)==9:
            inv=gf2_mat_inv(M)
            if inv is None:
                raise RuntimeError(q)
            phi[int(q)]=trace_mask_correct(inv)
    return phi


def main():
    from ortools.sat.python import cp_model
    ap=argparse.ArgumentParser()
    ap.add_argument("--orbits", nargs="+", type=int, default=[4,5])
    ap.add_argument("--solver-time", type=float, default=300.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--seed", type=int, default=660466)
    args=ap.parse_args()
    t0=time.time(); OUT.mkdir(parents=True, exist_ok=True)
    perms=build_stabilizer(); pt_orb, point_orbits=compute_point_orbits(perms)
    allowed=[]
    for a in args.orbits:
        allowed.extend(point_orbits[a])
    allowed=sorted(set(int(p) for p in allowed))
    Aset=set(allowed)
    lut,lut_meta=load_lut(LUT_PATH)
    records,complete_meta=build_core_constraints(CoreQuotient(1), lut)
    model=cp_model.CpModel()
    x={p:model.NewBoolVar(f"x_{p}") for p in allowed}
    model.Add(sum(x.values())==19)
    row_count=0; row_by_L=Counter(); row_by_dim=Counter(); trivial=0; empty=0
    for rec in records:
        L=int(rec["L"]); cap=19-L
        pts=points_from_bitset_intersect(int(rec["point_bitset"]), Aset)
        if not pts:
            empty += 1
            continue
        if len(pts) <= cap:
            trivial += 1
            continue
        model.Add(sum(x[p] for p in pts) <= cap)
        row_count += 1; row_by_L[L]+=1; row_by_dim[int(rec["dim8"])] += 1
    model.Minimize(sum(((p*97+args.seed)%1009)*x[p] for p in allowed))
    solver=cp_model.CpSolver(); solver.parameters.max_time_in_seconds=float(args.solver_time); solver.parameters.num_search_workers=int(args.workers); solver.parameters.random_seed=int(args.seed)
    ts=time.time(); status=solver.Solve(model); solve_sec=time.time()-ts
    status_name=solver.StatusName(status)
    result={
        "schema":"orbit_face_support_search_v1",
        "orbits":args.orbits,
        "point_orbit_reps":[int(o[0]) for o in point_orbits],
        "point_orbit_sizes":[len(o) for o in point_orbits],
        "allowed_size":len(allowed),
        "allowed_points":allowed,
        "constraint_summary":{"wang_rows_added":row_count,"wang_rows_by_L":{str(k):int(v) for k,v in sorted(row_by_L.items())},"wang_rows_by_dim":{str(k):int(v) for k,v in sorted(row_by_dim.items())},"trivial_pop_le_cap":trivial,"empty_intersection":empty},
        "parameters":{"solver_time":args.solver_time,"workers":args.workers,"seed":args.seed},
        "status":status_name,
        "solve_sec":round(solve_sec,3),
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        S=[p for p in allowed if solver.Value(x[p])]
        scan=complete_core_wang_scan("orbit_face_solution", S, 19, records, max_head=40)
        fullscan=full_violation_scan(S, records, 19)
        T_core=np.load(ROOT/"workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8)%2
        contractions=build_contractions(T_core); masks={q:point_mask_for_q(q) for q in contractions}
        sat=saturation_domains(T_core,S)
        trans=transversal_failures(sat["sat_records"], sat["B_domains"], sat["C_domains"], 9, 9, max_report=20)
        qscan=eval_candidate_sources("orbit_face_solution", S, contractions, masks, max_source_size=2, max_store=20)
        phi=build_phi(T_core)
        trace_dep=eval_support_local_dependency(S, sorted(phi), phi, {p:None for p in range(1,256)})
        result["solution"]={
            "A_cols":S,
            "point_orbit_counts":{str(a):sum(1 for p in S if pt_orb[p]==a) for a in range(len(point_orbits))},
            "objective_value":float(solver.ObjectiveValue()),
            "complete_wang_scan":scan,
            "complete_violation_count_with_points":fullscan["complete_violation_count"],
            "first_violations_with_points":fullscan.get("violations",[])[:10],
            "zero_domain_terms":len(sat["summary"]["zero_domain_terms"]),
            "linear_pass":sat["summary"]["linear_membership"]["necessary_linear_test_passed"],
            "affine_dim":sat["summary"]["linear_membership"].get("affine_solution_dimension_if_consistent"),
            "saturated_contractions":sat["summary"].get("saturated_contraction_count"),
            "transversal_failures":trans["failure_count_reported"],
            "quotient_rank_violations_size2":qscan["violated_guarded_instances"],
            "trace_local_dependency":trace_dep,
        }
    result["elapsed_sec"]=round(time.time()-t0,3)
    name="orbits_"+"_".join(str(a) for a in args.orbits)+"_support_search.json"
    path=OUT/name
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"out":str(path),"orbits":args.orbits,"allowed_size":len(allowed),"rows_added":row_count,"status":status_name,"solve_sec":result["solve_sec"],"solution":result.get("solution",{}).get("A_cols"),"complete_violations":result.get("solution",{}).get("complete_wang_scan",{}).get("complete_violation_count"),"elapsed_sec":result["elapsed_sec"]},indent=2,sort_keys=True))

if __name__=="__main__":
    main()
