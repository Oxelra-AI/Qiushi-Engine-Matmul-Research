#!/usr/bin/env python3
"""Validate analysis invariant triangle-row construction on random supports."""
from __future__ import annotations
import json, random, sys, time
from fractions import Fraction
from pathlib import Path

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from rlt_pair_lift import build_stabilizer, compute_pair_orbits, compute_point_orbits  # noqa: E402
from rlt_triangle_integrality import build_triangle_constraints  # noqa: E402

OUT = ROOT / "workspace/data/triangle_validation"
OUT.mkdir(parents=True, exist_ok=True)


def support_marginals(S, pt_orb, point_orbits, pair_orb, pair_sizes, K, M):
    S = sorted(S)
    n = [0]*K
    for p in S:
        n[pt_orb[p]] += 1
    m = [0]*M
    for i,p in enumerate(S):
        for q in S[i+1:]:
            m[pair_orb[(min(p,q), max(p,q))]] += 1
    z = [Fraction(n[a], len(point_orbits[a])) for a in range(K)]
    z += [Fraction(m[j], pair_sizes[j]) for j in range(M)]
    return z, n, m


def max_triangle_violation(A_tri, z):
    worst = Fraction(0,1)
    bad = 0
    first = None
    for r in range(A_tri.shape[0]):
        start, end = A_tri.indptr[r], A_tri.indptr[r+1]
        val = Fraction(0,1)
        for idx, coeff in zip(A_tri.indices[start:end], A_tri.data[start:end]):
            c = int(round(float(coeff)))
            val += c * z[int(idx)]
        if val > 0:
            bad += 1
            if val > worst:
                worst = val
            if first is None:
                first = {"row": r, "violation": str(val)}
    return {"bad_rows": bad, "max_violation": str(worst), "first_bad": first}


def main():
    t0=time.time()
    perms=build_stabilizer()
    pt_orb, point_orbits=compute_point_orbits(perms)
    pair_orb, pair_sizes, pair_ep, M=compute_pair_orbits(perms, pt_orb)
    K=len(point_orbits)
    A_tri, b_tri, meta=build_triangle_constraints(pt_orb, pair_orb, K, M)
    rng=random.Random(660266)
    tests=[]
    # Include some structured supports plus random supports.
    supports=[]
    supports.append(list(range(1,20)))
    supports.append([1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219])
    for _ in range(50):
        supports.append(rng.sample(range(1,256), 19))
    total_bad=0
    max_seen=Fraction(0,1)
    for idx,S in enumerate(supports):
        z,n,m=support_marginals(S, pt_orb, point_orbits, pair_orb, pair_sizes, K, M)
        res=max_triangle_violation(A_tri, z)
        if res["bad_rows"]:
            total_bad += res["bad_rows"]
            max_seen=max(max_seen, Fraction(res["max_violation"]))
        tests.append({"test_index": idx, "point_counts": n, "pair_count_total": sum(m), **res})
    payload={
        "schema":"triangle_validation_v1",
        "triangle_meta":meta,
        "point_orbit_reps":[int(o[0]) for o in point_orbits],
        "point_orbit_sizes":[len(o) for o in point_orbits],
        "support_tests":len(supports),
        "total_bad_rows":total_bad,
        "max_violation_seen":str(max_seen),
        "first_tests":tests[:5],
        "all_tests_passed": total_bad == 0,
        "elapsed_sec":round(time.time()-t0,3),
    }
    path=OUT/"triangle_row_validation.json"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True)+"\n")
    print(json.dumps({k:payload[k] for k in ["triangle_meta","support_tests","total_bad_rows","max_violation_seen","all_tests_passed","elapsed_sec"]}, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
