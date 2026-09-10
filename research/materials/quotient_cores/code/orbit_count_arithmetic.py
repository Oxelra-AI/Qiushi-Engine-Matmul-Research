#!/usr/bin/env python3
"""analysis: exact arithmetic for E11 stabilizer point-orbit counts.

This script does not solve Wang constraints.  It enumerates the integer point-count
simplex n_a=|S∩O_a| with sum n_a=19 and compares it to the rounded analysis LP
point.  The purpose is to make clear what the invariant-count strengthening can
and cannot infer from one zero-objective LP vertex.
"""
from __future__ import annotations

import json
from fractions import Fraction
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
OUT = ROOT / "workspace/data/orbit_count_arithmetic"
OUT.mkdir(parents=True, exist_ok=True)

SIZES = [6, 9, 36, 72, 36, 96]
REPS = [1, 5, 8, 10, 42, 80]
X = [Fraction(0,1), Fraction(0,1), Fraction(0,1), Fraction(0,1),
            Fraction('0.0636225266'), Fraction('0.1740582192')]
# The displayed analysis values are rounded, so use only as proximity evidence.
N_APPROX = [X[i] * SIZES[i] for i in range(6)]

vectors = []
for vals in product(*(range(min(s, 19) + 1) for s in SIZES)):
    if sum(vals) == 19:
        vectors.append(vals)

hist_omitted = {}
mins = [999]*6
maxs = [-1]*6
closest = []
for v in vectors:
    omitted = sum(v[:4])
    hist_omitted[str(omitted)] = hist_omitted.get(str(omitted), 0) + 1
    for a,n in enumerate(v):
        mins[a] = min(mins[a], n); maxs[a] = max(maxs[a], n)
    # L1 distance to rounded analysis masses.
    dist = sum(abs(Fraction(v[i], 1) - N_APPROX[i]) for i in range(6))
    closest.append((dist, v))
closest.sort(key=lambda t: (t[0], t[1]))

# Count pure orbit4+5 branches and possible n4,n5 under exact cardinality.
pure_45 = [v for v in vectors if sum(v[:4]) == 0]

payload = {
    "schema": "orbit_count_arithmetic_v1",
    "point_orbit_reps": REPS,
    "point_orbit_sizes": SIZES,
    "total_count_vectors": len(vectors),
    "omitted_n_0_3_histogram_all_cardinality_only": dict(sorted(hist_omitted.items(), key=lambda kv: int(kv[0]))),
    "per_orbit_min_count_cardinality_only": mins,
    "per_orbit_max_count_cardinality_only": maxs,
    "pure_orbits_4_5_count_vectors": len(pure_45),
    "pure_orbits_4_5_vectors": [list(v) for v in pure_45[:20]],
    "displayed_x_values_are_rounded": [str(x) for x in X],
    "displayed_n_masses_from_rounded_x": [str(n) for n in N_APPROX],
    "nearest_integer_count_vectors_to_displayed_vertex": [
        {"l1_distance_to_rounded_displayed_masses": str(d), "counts": list(v), "omitted_n_0_3": sum(v[:4])}
        for d, v in closest[:20]
    ],
    "interpretation_note": (
        "This only enumerates the exact invariant point-count simplex.  It shows that the analysis zero-objective vertex "
        "has non-integral masses near n4≈2.2904 and n5≈16.7096, closest to branches [0,0,0,0,2,17] and [0,0,0,0,3,16]. "
        "Whether any branch satisfies shared-pair Wang constraints is tested separately."
    ),
}
path = OUT / "orbit_count_arithmetic.json"
path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
print(json.dumps({k: payload[k] for k in ["total_count_vectors", "omitted_n_0_3_histogram_all_cardinality_only", "pure_orbits_4_5_count_vectors", "nearest_integer_count_vectors_to_displayed_vertex"]}, indent=2, sort_keys=True))
