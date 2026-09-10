#!/usr/bin/env python3
r"""analysis: local flag/color-count polytopes for E11 Wang incidence.

For a dual subspace D <= (F2^8)^* of dimension d=2 or d=3, the primal row is
U=D^perp.  A 19-point support induces color counts n_v for v in F2^d by the
evaluation map p -> (q_i(p)).  Wang rows for nonzero E<=D give linked integer
constraints on these counts.  This script asks which dim-6 (d=2) and dim-5
(d=3) rows are locally new relative to their proper subflags.

For d=2: maximize n_00 subject only to the three contraction rows (dual points).
The line row U=D^perp with L(D^perp) adds information iff max n_00 > 19-L.

For d=3: maximize n_000 subject to all dual point rows and all dual-line rows
inside D.  The plane row U=D^perp adds information iff max n_000 > 19-L.

This is not a global proof: it is a labelled local-incidence catalogue showing
which Wang rows are primitive after lower-dimensional flag information is kept.
"""
from __future__ import annotations

import json
import sys
import time
from collections import Counter, defaultdict
from functools import lru_cache
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_all_mip import enumerate_subspace_keys  # noqa: E402
from core_capacity_from_wang_lut import CoreQuotient, load_lut  # noqa: E402
from wang_capacity_lazy import pack_basis, rref_basis, unpack_basis  # noqa: E402

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/core_incidence"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"


def dot(a: int, b: int) -> int:
    return (int(a) & int(b)).bit_count() & 1


def xor_combo(basis: Sequence[int], mask: int) -> int:
    x = 0
    for i, b in enumerate(basis):
        if (mask >> i) & 1:
            x ^= int(b)
    return x


@lru_cache(maxsize=None)
def dual_perp_key8_cached(qs_key: Tuple[int, ...]) -> int:
    qs = list(qs_key)
    rows: List[int] = []
    target_dim = 8 - len(qs)
    for p in range(1, 256):
        if all(dot(p, q) == 0 for q in qs):
            new_rows = list(rref_basis(rows + [p], n=8))
            if len(new_rows) > len(rows):
                rows = new_rows
                if len(rows) == target_dim:
                    break
    if len(rows) != target_dim:
        raise RuntimeError(f"perp basis rank failed for qs={qs}: got {rows}")
    return pack_basis(rref_basis(rows, n=8))


def dual_perp_key8(qs: Sequence[int]) -> int:
    return dual_perp_key8_cached(tuple(unpack_basis(pack_basis(rref_basis(qs, n=8)))))


def local_profile_for_dual_key(keyD: int, L_by_primal_key: Dict[int, int]) -> dict:
    basis = list(unpack_basis(keyD))
    d = len(basis)
    point_L = []
    for m in range(1, 1 << d):
        q = xor_combo(basis, m)
        k = dual_perp_key8([q])
        point_L.append(int(L_by_primal_key[k]))
    line_L = []
    if d >= 2:
        # For each nonzero local color r, E_r is the hyperplane of dual masks m with m.r=0.
        # In d=2 this hyperplane is a point; in d=3 it is a dual line.
        for r in range(1, 1 << d):
            qs = [xor_combo(basis, m) for m in range(1, 1 << d) if dot(m, r) == 0]
            k = dual_perp_key8(qs)
            line_L.append(int(L_by_primal_key[k]))
    kD = dual_perp_key8(basis)
    LD = int(L_by_primal_key[kD])
    return {
        "dual_key": int(keyD),
        "dual_basis": basis,
        "d": d,
        "primal_key": int(kD),
        "point_L": tuple(point_L),
        "line_L_by_annihilator_color": tuple(line_L),
        "L_Dperp": LD,
    }


def feasible_with_n0(d: int, n0: int, point_L: Tuple[int, ...], line_L: Tuple[int, ...]) -> Tuple[bool, Tuple[int, ...] | None]:
    m = (1 << d) - 1
    R = 19 - n0
    if R < 0:
        return False, None
    upper = [R] * (m + 1)
    lower = [0] * (m + 1)
    # Proper hyperplane rows E<=D represented by annihilator color r impose n0+n_r <= 19-L(Eperp).
    for r in range(1, m + 1):
        cap = 19 - int(line_L[r - 1])
        upper[r] = min(upper[r], cap - n0)
    if any(upper[r] < 0 for r in range(1, m + 1)):
        return False, None

    vals = [0] * (m + 1)
    vals[0] = n0
    # Order variables by smallest upper first to prune.
    order = sorted(range(1, m + 1), key=lambda r: upper[r])

    def check_partial_assuming_remaining(idx: int, rem: int) -> bool:
        # Necessary upper-sum check.
        if rem < 0:
            return False
        if sum(upper[r] for r in order[idx:]) < rem:
            return False
        return True

    def point_constraints_possible(idx: int, rem: int) -> bool:
        # Upper-bound lookahead for each point inequality.
        assigned = {r for r in order[:idx]}
        remaining = order[idx:]
        for qmask in range(1, m + 1):
            current = sum(vals[v] for v in assigned if dot(qmask, v))
            max_extra = sum(upper[v] for v in remaining if dot(qmask, v))
            if current + max_extra < int(point_L[qmask - 1]):
                return False
        return True

    def rec(idx: int, rem: int) -> bool:
        if not check_partial_assuming_remaining(idx, rem):
            return False
        if not point_constraints_possible(idx, rem):
            return False
        if idx == len(order):
            if rem != 0:
                return False
            for qmask in range(1, m + 1):
                if sum(vals[v] for v in range(1, m + 1) if dot(qmask, v)) < int(point_L[qmask - 1]):
                    return False
            return True
        r = order[idx]
        lo = 0
        hi = min(upper[r], rem)
        # Higher values in constrained cells are often helpful for lower bounds; try descending.
        for z in range(hi, lo - 1, -1):
            vals[r] = z
            if rec(idx + 1, rem - z):
                return True
        vals[r] = 0
        return False

    ok = rec(0, R)
    if ok:
        return True, tuple(vals)
    return False, None


@lru_cache(maxsize=None)
def max_n0_for_profile(d: int, point_L: Tuple[int, ...], line_L: Tuple[int, ...]) -> Tuple[int, Tuple[int, ...] | None]:
    for n0 in range(19, -1, -1):
        ok, witness = feasible_with_n0(d, n0, point_L, line_L)
        if ok:
            return n0, witness
    return -1, None


def profile_summary(records: List[dict], d: int) -> dict:
    profile_records = defaultdict(list)
    for r in records:
        key = (r["point_L"], r["line_L_by_annihilator_color"], r["L_Dperp"])
        profile_records[key].append(r)

    profile_out = []
    by_L = Counter()
    row_status = Counter()
    by_L_status = Counter()
    witness_examples = []
    for key, recs in profile_records.items():
        point_L, line_L, LD = key
        max_n0, witness = max_n0_for_profile(d, tuple(point_L), tuple(line_L))
        cap = 19 - int(LD)
        adds = max_n0 > cap
        tight = max_n0 == cap
        status = "proper_flag_implies_row" if max_n0 <= cap else "row_adds_integer_information"
        by_L[int(LD)] += len(recs)
        row_status[status] += len(recs)
        by_L_status[(int(LD), status)] += len(recs)
        profile_out.append({
            "profile_count": len(recs),
            "d": d,
            "point_L": list(point_L),
            "line_L_by_annihilator_color": list(line_L),
            "L_Dperp": int(LD),
            "row_cap_n0": cap,
            "max_n0_from_proper_subflags": int(max_n0),
            "row_adds_information": bool(adds),
            "row_tight_under_proper_flags": bool(tight),
            "status": status,
            "example_dual_key": int(recs[0]["dual_key"]),
            "example_dual_basis": list(recs[0]["dual_basis"]),
            "example_primal_key": int(recs[0]["primal_key"]),
            "witness_counts_n0_then_nonzero_colors": None if witness is None else list(witness),
        })
        if adds and len(witness_examples) < 40:
            witness_examples.append(profile_out[-1])
    profile_out.sort(key=lambda z: (z["L_Dperp"], z["status"], -z["profile_count"], z["point_L"], z["line_L_by_annihilator_color"]))
    return {
        "d": d,
        "row_count": sum(len(v) for v in profile_records.values()),
        "unique_exact_profiles": len(profile_records),
        "rows_by_L": {str(k): int(v) for k, v in sorted(by_L.items())},
        "rows_by_status": {str(k): int(v) for k, v in sorted(row_status.items())},
        "rows_by_L_and_status": [
            {"L_Dperp": int(L), "status": st, "count": int(cnt)}
            for (L, st), cnt in sorted(by_L_status.items())
        ],
        "profiles": profile_out,
        "row_adds_information_profile_examples_head": witness_examples,
    }


def main() -> None:
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    lut, meta = load_lut(LUT_PATH)
    core = CoreQuotient(1)
    # Build L_by_primal_key for E11 core rows.
    print("Enumerating complete E11 core keys for L lookup...")
    keys8 = enumerate_subspace_keys(8)
    L_by_primal_key = {int(k): int(lut[core.key9_from_key8(int(k))]) for k in keys8}
    print(f"Core keys: {len(L_by_primal_key):,}")

    dual_keys_by_d = {2: [], 3: []}
    for k in keys8:
        d = int(k & 0xF)
        if d in dual_keys_by_d:
            dual_keys_by_d[d].append(int(k))
    outputs = {}
    for d in (2, 3):
        print(f"Building local profiles for dual dimension {d}: {len(dual_keys_by_d[d]):,} keys")
        recs = []
        for i, keyD in enumerate(dual_keys_by_d[d], start=1):
            recs.append(local_profile_for_dual_key(keyD, L_by_primal_key))
            if i % 20000 == 0:
                print(f"  d={d} processed {i:,}/{len(dual_keys_by_d[d]):,}")
        outputs[f"dual_dim_{d}"] = profile_summary(recs, d)
        print(f"  d={d}: profiles={outputs[f'dual_dim_{d}']['unique_exact_profiles']} status={outputs[f'dual_dim_{d}']['rows_by_status']}")

    result = {
        "schema": "flag_local_polytope_v1",
        "field": "F2",
        "core": "E11 quotient core",
        "meaning": "Local color-count implication of a Wang row by its proper dual subflag; not a global support exclusion.",
        "full_lut_coverage_ok": meta.get("coverage_ok"),
        "outputs": outputs,
        "elapsed_sec": time.time() - t0,
    }
    out = OUTDIR / "flag_local_polytope.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "elapsed_sec": round(time.time() - t0, 3),
        "dual_dim_2": {k: outputs["dual_dim_2"][k] for k in ["row_count", "unique_exact_profiles", "rows_by_L", "rows_by_status"]},
        "dual_dim_3": {k: outputs["dual_dim_3"][k] for k in ["row_count", "unique_exact_profiles", "rows_by_L", "rows_by_status"]},
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
