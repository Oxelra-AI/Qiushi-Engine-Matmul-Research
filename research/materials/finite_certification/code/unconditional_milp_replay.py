#!/usr/bin/env python3
r"""analysis: Unconditional MILP replay of the stored E11 core exclusion model.

The stored analysis quotient-separator model reached CP-SAT INFEASIBLE using
252 guarded quotient-rank cuts that require saturation Boolean variables.
Here we convert each stored cut to its unconditional form:

    N_out + sum_{q in S}(w_q - r_q) >= R

equivalently:

    sum_{p: t(p)=1, q1(p)=q2(p)=0} x_p
      + sum_{p: q1(p)=1} x_p
      + sum_{p: q2(p)=1} x_p
    >= R + r_q1 + r_q2

This is purely linear in x_p with no saturation guards.  The model becomes:
- 255 integer variables x_p in [0, cap_p]
- sum(x) = 19
- at least one x_p >= 2  (repeated direction)
- Wang rows (upper occupancy bounds)
- contraction lower bounds (w_q >= r_q)
- unconditional quotient-rank cuts (purely linear)

We solve with scipy/HiGHS.  If INFEASIBLE, the exclusion is a pure ILP
certificate, independent of the saturation-literal mechanism.  We also test
a second model WITHOUT the repeat-direction constraint to check if the
unconditional cuts exclude distinct supports too.
"""
from __future__ import annotations
import argparse, json, pickle, sys, time
from collections import Counter
from pathlib import Path
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient
from fixed_A_saturation import mat_rank_f2
from complete_core_and_transversal import ROOT, build_core_constraints
from quotient_rank_cuts import build_contractions, point_mask_for_q
from wang_capacity_lazy import subspace_points_from_basis, unpack_basis

OUTDIR = ROOT / "workspace/data/unconditional_qcuts"


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}


def build_milp_model(
    s: int,
    points: list,
    point_cap: dict,
    records: list,
    record_by_key: dict,
    lut: dict,
    core: object,
    contractions: dict,
    masks: dict,
    wang_keys: set,
    qcuts: list,
    force_repeat: bool = True,
) -> dict:
    """Build a pure ILP model (no saturation Booleans)."""
    t0 = time.time()
    p_index = {p: p - 1 for p in points}
    repeat_pts = [p for p, c in point_cap.items() if c >= 2]

    # Variables: 255 x_p + (optionally repeat indicators)
    nx = 255
    nr = len(repeat_pts) if force_repeat else 0
    nvars = nx + nr
    r_index = {p: nx + i for i, p in enumerate(repeat_pts)} if force_repeat else {}

    rows = []
    lbs = []
    ubs = []

    def add(coeff, lb=-np.inf, ub=np.inf):
        rows.append(coeff)
        lbs.append(lb)
        ubs.append(ub)

    # 1. Total rank
    add({p_index[p]: 1 for p in points}, s, s)

    # 2. Repeat encoding (if required)
    if force_repeat and repeat_pts:
        add({r_index[p]: 1 for p in repeat_pts}, 1, np.inf)
        for p in repeat_pts:
            add({p_index[p]: 1, r_index[p]: -1}, -np.inf, 1)   # x - r <= 1
            add({p_index[p]: 1, r_index[p]: -2}, 0, np.inf)     # x - 2r >= 0

    # 3. Wang rows
    wang_count = 0
    for key8 in sorted(wang_keys):
        rec = record_by_key[key8]
        cap = s - int(rec['L'])
        pts = subspace_points_from_basis(unpack_basis(key8))
        add({p_index[p]: 1 for p in pts}, -np.inf, cap)
        wang_count += 1

    # 4. Contraction lower bounds
    clb = 0
    for q, c in contractions.items():
        rk = int(c['rank'])
        if rk > 0:
            add({p_index[p]: 1 for p in points if ((q & p).bit_count() & 1)}, rk, np.inf)
            clb += 1

    # 5. UNCONDITIONAL quotient-rank cuts
    qcut_count = 0
    for c in qcuts:
        q1, q2 = int(c['sources'][0]), int(c['sources'][1])
        target = int(c['target'])
        req = int(c['requirement'])
        rq1 = int(contractions[q1]['rank'])
        rq2 = int(contractions[q2]['rank'])

        # Build coefficient vector
        source_union = masks[q1] | masks[q2]
        outside_mask = masks[target] & (~source_union) & ((1 << 255) - 1)

        coeff = {}
        # Outside (target-active, not in source union): coeff = 1
        for p in points:
            if (outside_mask >> (p - 1)) & 1:
                coeff[p_index[p]] = coeff.get(p_index[p], 0) + 1
        # Source q1 active: coeff += 1
        for p in points:
            if ((q1 & p).bit_count() & 1):
                coeff[p_index[p]] = coeff.get(p_index[p], 0) + 1
        # Source q2 active: coeff += 1
        for p in points:
            if ((q2 & p).bit_count() & 1):
                coeff[p_index[p]] = coeff.get(p_index[p], 0) + 1

        rhs = req + rq1 + rq2
        add(coeff, rhs, np.inf)
        qcut_count += 1

    build_sec = time.time() - t0

    # Assemble sparse matrix
    A = lil_matrix((len(rows), nvars), dtype=float)
    for i, coeff in enumerate(rows):
        for j, v in coeff.items():
            A[i, j] = v

    lbounds = np.zeros(nvars)
    ubounds = np.zeros(nvars)
    integrality = np.ones(nvars, dtype=int)
    for p in points:
        lbounds[p_index[p]] = 0
        ubounds[p_index[p]] = point_cap[p]
    if force_repeat:
        for p in repeat_pts:
            lbounds[r_index[p]] = 0
            ubounds[r_index[p]] = 1

    return {
        "A": A.tocsr(),
        "lbs": np.array(lbs, dtype=float),
        "ubs": np.array(ubs, dtype=float),
        "bounds": Bounds(lbounds, ubounds),
        "integrality": integrality,
        "nvars": nvars,
        "nx": nx,
        "nr": nr,
        "wang_count": wang_count,
        "clb": clb,
        "qcut_count": qcut_count,
        "nrows": len(rows),
        "build_sec": build_sec,
        "p_index": p_index,
        "points": points,
    }


def solve_milp(model_data: dict, time_limit: float = 300.0) -> dict:
    """Solve the built model with scipy/HiGHS."""
    c = np.zeros(model_data["nvars"])
    constraints = LinearConstraint(model_data["A"], model_data["lbs"], model_data["ubs"])
    ts = time.time()
    res = milp(
        c=c,
        integrality=model_data["integrality"],
        bounds=model_data["bounds"],
        constraints=constraints,
        options={'time_limit': time_limit, 'mip_rel_gap': 0.0, 'presolve': True},
    )
    solve_sec = time.time() - ts
    result = {
        "status": int(res.status),
        "message": str(res.message),
        "success": bool(res.success),
        "fun": None if res.fun is None else float(res.fun),
        "solve_sec": round(solve_sec, 3),
    }
    if res.x is not None:
        vals = np.rint(res.x[:model_data["nx"]]).astype(int)
        counts = {int(p): int(vals[p - 1]) for p in model_data["points"] if vals[p - 1]}
        result["counts"] = counts
        result["distinct_points"] = len(counts)
        result["max_mult"] = max(counts.values()) if counts else 0
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--source', type=Path,
                    default=ROOT / 'workspace/data/quotient_rank_cuts/core_e11_multiset_quotient_sep_24r_fullstored.json')
    ap.add_argument('--time-limit', type=float, default=300.0)
    ap.add_argument('--out', type=Path, default=OUTDIR / 'unconditional_milp_replay.json')
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)

    t0 = time.time()
    s = 19
    core = CoreQuotient(1)
    src = json.loads(args.source.read_text())
    T = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2
    lut = load_lut(ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    records, meta = build_core_constraints(core, lut)
    record_by_key = {int(r['key8']): r for r in records}
    contractions = build_contractions(T)
    masks = {q: point_mask_for_q(q) for q in contractions}
    points = list(range(1, 256))

    point_cap = {}
    for p in points:
        key8 = core.key8_from_rows([p])
        key9 = core.key9_from_key8(key8)
        point_cap[p] = max(0, min(s, s - int(lut[key9])))

    # Extract learned constraints from source file
    wang_keys = set()
    qcuts = []
    for r in records:
        if int(r['dim8']) in (1, 2):
            wang_keys.add(int(r['key8']))
    for rnd in src.get('rounds', []):
        for w in rnd.get('learned_wang_rows', []):
            wang_keys.add(int(w['key8']))
        for c in rnd.get('learned_quotient_cuts', []):
            qcuts.append(c)

    print(f"Loaded: {len(wang_keys)} unique Wang rows, {len(qcuts)} quotient cuts")
    print(f"Source final status: {src.get('final_status')}")

    # Model 1: WITH repeated-direction constraint (multiset)
    print("\n=== Model 1: Unconditional MILP WITH repeat constraint ===")
    m1 = build_milp_model(s, points, point_cap, records, record_by_key, lut, core,
                          contractions, masks, wang_keys, qcuts, force_repeat=True)
    print(f"  vars={m1['nvars']} rows={m1['nrows']} wang={m1['wang_count']} "
          f"clb={m1['clb']} qcuts={m1['qcut_count']} build_sec={m1['build_sec']:.3f}")
    r1 = solve_milp(m1, args.time_limit)
    print(f"  status={r1['status']} message={r1['message']} solve_sec={r1['solve_sec']}")
    if 'counts' in r1:
        print(f"  FEASIBLE solution: {r1['distinct_points']} distinct points, max_mult={r1['max_mult']}")

    # Model 2: WITHOUT repeated-direction constraint (also covers distinct supports)
    print("\n=== Model 2: Unconditional MILP WITHOUT repeat constraint ===")
    m2 = build_milp_model(s, points, point_cap, records, record_by_key, lut, core,
                          contractions, masks, wang_keys, qcuts, force_repeat=False)
    print(f"  vars={m2['nvars']} rows={m2['nrows']} wang={m2['wang_count']} "
          f"clb={m2['clb']} qcuts={m2['qcut_count']} build_sec={m2['build_sec']:.3f}")
    r2 = solve_milp(m2, args.time_limit)
    print(f"  status={r2['status']} message={r2['message']} solve_sec={r2['solve_sec']}")
    if 'counts' in r2:
        print(f"  FEASIBLE solution: {r2['distinct_points']} distinct points, max_mult={r2['max_mult']}")

    # Save
    result = {
        "schema": "unconditional_milp_replay_v1",
        "field": "F2",
        "core": "E11",
        "rank_s": s,
        "source": str(args.source),
        "source_final_status": src.get("final_status"),
        "point_cap_distribution": {str(k): int(v) for k, v in sorted(Counter(point_cap.values()).items())},
        "shared_constraint_summary": {
            "unique_wang_rows": len(wang_keys),
            "contraction_lower_bounds": m1["clb"],
            "unconditional_quotient_cuts": m1["qcut_count"],
        },
        "model1_with_repeat": {
            "description": "ILP with x_p sum=19, repeat forced, Wang+contraction+unconditional qcuts",
            "variables": m1["nvars"],
            "constraint_rows": m1["nrows"],
            "build_sec": round(m1["build_sec"], 3),
            "solver": "scipy.optimize.milp/HiGHS",
            "result": r1,
        },
        "model2_no_repeat": {
            "description": "ILP with x_p sum=19, no repeat forced, Wang+contraction+unconditional qcuts",
            "variables": m2["nvars"],
            "constraint_rows": m2["nrows"],
            "build_sec": round(m2["build_sec"], 3),
            "solver": "scipy.optimize.milp/HiGHS",
            "result": r2,
        },
        "mathematical_content": (
            "Each stored guarded quotient-rank cut (sat(q1) AND sat(q2) => N_out >= R) "
            "is replaced by the unconditional linear inequality "
            "N_out + (w_q1-r_q1) + (w_q2-r_q2) >= R, i.e. "
            "sum_{p coeff} x_p >= R + r_q1 + r_q2 where "
            "coeff(p) = 1_{outside(p)} + 1_{q1(p)} + 1_{q2(p)}. "
            "No saturation Boolean variables; pure ILP."
        ),
        "total_elapsed_sec": round(time.time() - t0, 3),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"\nSaved {args.out}")


if __name__ == "__main__":
    main()
