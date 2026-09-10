#!/usr/bin/env python3
r"""analysis: legitimate E11 group-average relaxation for distinct core supports.

The six E11 point orbits cannot replace the 255 point variables.  However, if a
complete-Wang-admissible support exists, its average over the verified
E11 table-preserving group is constant on point orbits.  Therefore the six
orbit means z_i satisfy all averaged row inequalities

    sum_i |U∩O_i| z_i <= 19-L(U),

plus sum_i |O_i| z_i=19 and 0<=z_i<=1.  If profile counts n_i=|P∩O_i| are used,
z_i=n_i/|O_i| gives an integer first-moment relaxation over orbit profiles.
This is a necessary relaxation only; feasibility does not imply a support.
"""
from __future__ import annotations

import itertools
import json
import math
import pickle
import sys
import time
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

import numpy as np
from scipy.optimize import linprog

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient  # noqa: E402
from complete_core_and_transversal import ROOT, build_core_constraints  # noqa: E402
from quotient_rank_cuts import build_contractions  # noqa: E402
from orbit_structure import bit8_to_mat3x3, gl3f2_elements, mat3x3_to_8bit, apply_conj  # noqa: E402
from distinct_trace_cut_cpsat import generate_stabilizer_permutations  # noqa: E402
from support_symmetry_discipline import compute_point_orbits, orbit_profile, load_new_supports  # noqa: E402
from trace_dependency_family import load_candidate_supports, dot8  # noqa: E402
from cert_trace_separator import points_for_rec  # noqa: E402
from neighborhood_repair import DEFAULT_SUPPORT  # noqa: E402

OUTDIR = ROOT / "workspace/data/transported_overlap"


def load_lut(path: Path):
    with path.open("rb") as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload["lut"].items()}, payload.get("meta", {})


def point_orbit_index(orbits: Sequence[Sequence[int]]) -> dict[int, int]:
    idx = {}
    for i, orb in enumerate(orbits):
        for p in orb:
            idx[int(p)] = i
    return idx


def row_orbit_counts(points: Sequence[int], idx: dict[int, int], m: int) -> Tuple[int, ...]:
    c = [0] * m
    for p in points:
        c[idx[int(p)]] += 1
    return tuple(c)


def support_profile(A: Sequence[int], idx: dict[int, int], m: int) -> Tuple[int, ...]:
    c = [0] * m
    for p in A:
        c[idx[int(p)]] += 1
    return tuple(c)


def compositions_with_caps(total: int, caps: Sequence[int]):
    m = len(caps)
    cur = [0] * m
    def rec(i, rem):
        if i == m - 1:
            if 0 <= rem <= caps[i]:
                cur[i] = rem
                yield tuple(cur)
            return
        for v in range(min(caps[i], rem) + 1):
            cur[i] = v
            yield from rec(i + 1, rem - v)
    yield from rec(0, total)


def rational_lhs(profile: Sequence[int], counts: Sequence[int], sizes: Sequence[int]) -> Fraction:
    acc = Fraction(0, 1)
    for n, a, sz in zip(profile, counts, sizes):
        if n and a:
            acc += Fraction(int(n) * int(a), int(sz))
    return acc


def load_stored_profiles(orbits):
    idx = point_orbit_index(orbits)
    raw = load_candidate_supports() + load_new_supports() + [{"name": "current_best_base", "source": "analysis/54", "A_cols": list(DEFAULT_SUPPORT), "complete_wang_violations": 9}]
    seen = set()
    out = []
    for r in raw:
        A = tuple(sorted(int(x) for x in r.get("A_cols", [])))
        if len(A) != 19 or len(set(A)) != 19 or A in seen:
            continue
        seen.add(A)
        out.append({
            "name": r.get("name"),
            "source": r.get("source"),
            "complete_wang_violations": r.get("complete_wang_violations"),
            "A_cols": list(A),
            "profile": list(support_profile(A, idx, len(orbits))),
        })
    return out


def main() -> None:
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    perms = generate_stabilizer_permutations(include_transpose=True)
    orbits = compute_point_orbits(perms)
    sizes = [len(o) for o in orbits]
    idx = point_orbit_index(orbits)
    base_prof = support_profile(DEFAULT_SUPPORT, idx, len(orbits))

    lut, _ = load_lut(ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl")
    core = CoreQuotient(1)
    records, meta = build_core_constraints(core, lut)
    # Compress rows by orbit-count vector and cap, keeping the tightest cap for each vector.
    tight = {}
    witness = {}
    raw_rows = 0
    for rec in records:
        L = int(rec["L"])
        cap = 19 - L
        if cap >= 19:
            continue
        counts = row_orbit_counts(points_for_rec(rec), idx, len(orbits))
        old = tight.get(counts)
        if old is None or cap < old:
            tight[counts] = cap
            witness[counts] = {"key8": int(rec["key8"]), "dim8": int(rec["dim8"]), "L": L, "cap": cap, "counts": list(counts)}
        raw_rows += 1
    compressed_rows = [(counts, cap, witness[counts]) for counts, cap in tight.items()]

    # Linear programming over z_i = averaged point value on orbit O_i.
    A_ub = []
    b_ub = []
    for counts, cap, _w in compressed_rows:
        A_ub.append([float(c) for c in counts])
        b_ub.append(float(cap))
    # transported overlap averaged cut: sum_i base_profile_i z_i <= 15
    A_ub.append([float(c) for c in base_prof])
    b_ub.append(15.0)
    A_eq = [[float(sz) for sz in sizes]]
    b_eq = [19.0]
    bounds = [(0.0, 1.0) for _ in sizes]
    lp = linprog(c=[0.0] * len(sizes), A_ub=np.array(A_ub), b_ub=np.array(b_ub), A_eq=np.array(A_eq), b_eq=np.array(b_eq), bounds=bounds, method="highs")

    # Optional averaged contraction-rank constraints.
    T_core = np.load(ROOT / "workspace/data/restricted_cores/mask_001_E11_core.npy").astype(np.uint8) % 2
    contractions = build_contractions(T_core)
    contraction_rows = []
    for q, c in contractions.items():
        rk = int(c["rank"])
        if rk <= 0:
            continue
        cnt = [0] * len(orbits)
        for p in range(1, 256):
            if dot8(q, p):
                cnt[idx[p]] += 1
        contraction_rows.append((tuple(cnt), rk, int(q)))
    A_ub2 = list(A_ub)
    b_ub2 = list(b_ub)
    # lower bound cnt.z >= rk as -cnt.z <= -rk
    for cnt, rk, _q in contraction_rows:
        A_ub2.append([-float(c) for c in cnt])
        b_ub2.append(-float(rk))
    lp_con = linprog(c=[0.0] * len(sizes), A_ub=np.array(A_ub2), b_ub=np.array(b_ub2), A_eq=np.array(A_eq), b_eq=np.array(b_eq), bounds=bounds, method="highs")

    # Enumerate integer orbit profiles n_i.  A real support with profile n maps to z_i=n_i/|O_i|.
    profile_records = []
    feasible_counts = 0
    feasible_with_contraction = 0
    min_max_slack = None
    tight_profile_examples = []
    infeas_reason_counter = Counter()
    for prof in compositions_with_caps(19, sizes):
        ok = True
        max_violation = Fraction(0, 1)
        tight_count = 0
        for counts, cap, _w in compressed_rows:
            lhs = rational_lhs(prof, counts, sizes)
            if lhs > cap:
                ok = False
                infeas_reason_counter["wang_avg"] += 1
                break
            if lhs == cap:
                tight_count += 1
        if ok:
            lhs_overlap = rational_lhs(prof, base_prof, sizes)
            if lhs_overlap > 15:
                ok = False
                infeas_reason_counter["overlap_avg"] += 1
        if ok:
            feasible_counts += 1
            con_ok = True
            for cnt, rk, _q in contraction_rows:
                lhs = rational_lhs(prof, cnt, sizes)
                if lhs < rk:
                    con_ok = False
                    infeas_reason_counter["contraction_avg"] += 1
                    break
            if con_ok:
                feasible_with_contraction += 1
            score = tight_count
            if len(tight_profile_examples) < 30 or con_ok:
                tight_profile_examples.append({
                    "profile": list(prof),
                    "z": [str(Fraction(n, sz)) for n, sz in zip(prof, sizes)],
                    "overlap_avg_lhs": str(lhs_overlap),
                    "tight_avg_wang_rows": tight_count,
                    "passes_avg_contraction": con_ok,
                })
                # keep bounded and prefer examples passing contractions
                tight_profile_examples = sorted(tight_profile_examples, key=lambda r: (not r["passes_avg_contraction"], -r["tight_avg_wang_rows"], r["profile"]))[:30]

    stored = load_stored_profiles(orbits)
    profile_hist = Counter(tuple(r["profile"]) for r in stored)
    result = {
        "schema": "orbit_average_relaxation_v1",
        "field": "F2",
        "core": "E11 quotient core",
        "meaning": "Legal first-moment group-average relaxation over point orbits. Feasible profiles are necessary possibilities only; they do not represent actual support orbits and do not preserve point-level incidences.",
        "group_order": len(perms),
        "point_orbit_sizes": sizes,
        "point_orbits": orbits,
        "base_support": list(DEFAULT_SUPPORT),
        "base_orbit_profile": list(base_prof),
        "complete_core_table_meta": meta,
        "raw_nonvacuous_rows": raw_rows,
        "compressed_average_row_count": len(compressed_rows),
        "lp_wang_overlap": {
            "success": bool(lp.success),
            "status": int(lp.status),
            "message": lp.message,
            "z": None if lp.x is None else [float(v) for v in lp.x],
            "sum_size_z": None if lp.x is None else float(np.dot(np.array(sizes), lp.x)),
        },
        "lp_wang_overlap_contraction": {
            "success": bool(lp_con.success),
            "status": int(lp_con.status),
            "message": lp_con.message,
            "z": None if lp_con.x is None else [float(v) for v in lp_con.x],
            "sum_size_z": None if lp_con.x is None else float(np.dot(np.array(sizes), lp_con.x)),
            "contraction_rows": len(contraction_rows),
        },
        "integer_orbit_profile_relaxation": {
            "total_profiles_with_caps": sum(1 for _ in compositions_with_caps(19, sizes)),
            "feasible_wang_overlap_profiles": feasible_counts,
            "feasible_wang_overlap_contraction_profiles": feasible_with_contraction,
            "infeas_reason_counter_first_hit": {str(k): int(v) for k, v in sorted(infeas_reason_counter.items())},
            "example_profiles": tight_profile_examples,
        },
        "stored_support_profiles": stored,
        "stored_profile_histogram": {str(list(k)): int(v) for k, v in sorted(profile_hist.items())},
        "elapsed_sec": round(time.time() - t0, 3),
    }
    out = OUTDIR / "orbit_average_relaxation.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "point_orbit_sizes": sizes,
        "base_profile": list(base_prof),
        "compressed_rows": len(compressed_rows),
        "lp_success": bool(lp.success),
        "lp_con_success": bool(lp_con.success),
        "profile_relaxation": result["integer_orbit_profile_relaxation"],
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True)[:6000])


if __name__ == "__main__":
    main()
