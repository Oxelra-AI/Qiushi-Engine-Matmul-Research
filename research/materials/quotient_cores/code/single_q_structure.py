#!/usr/bin/env python3
r"""analysis: structure of corrected one-contraction trace obstruction.

For saturated invertible q (rank L(q)=9, w(q)=9), the corrected single-q trace
condition is automatic if the ten outside support points span ker(q).  If they
span a proper W<ker(q), then all ten outside points lie in W.  This script tests
whether Wang occupation rows already forbid that for the E11 core by checking
stored lower bounds L(W) for proper subspaces W of each rank-9 kernel.
"""
from __future__ import annotations

import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Sequence

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient  # noqa: E402
from fixed_A_saturation import build_matmul_tensor_f2, contraction_matrix, mat_rank_f2  # noqa: E402
from complete_core_and_transversal import build_core_constraints  # noqa: E402
from wang_capacity_lazy import rref_basis, subspace_points_from_basis, unpack_basis  # noqa: E402

ROOT = Path("research/research_record")
OUTDIR = ROOT / "workspace/data/corrected_trace"
LUT_PATH = ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl"


def parity_dot(a: int, b: int) -> int:
    return (int(a) & int(b)).bit_count() & 1


def load_lut() -> Dict[int, int]:
    with LUT_PATH.open("rb") as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload["lut"].items()}


def main() -> None:
    OUTDIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    T_core = build_matmul_tensor_f2()[1:, :, :].astype(np.uint8) % 2
    rank9 = []
    for q in range(1, 256):
        rk = mat_rank_f2(contraction_matrix(T_core, q))
        if rk == 9:
            rank9.append(q)
    lut = load_lut()
    core = CoreQuotient(1)
    records, meta = build_core_constraints(core, lut)

    # Index records contained in each hyperplane ker(q).
    per_q = []
    global_bad = []
    dim_L_hist = defaultdict(Counter)
    proper_min_by_dim = defaultdict(lambda: 999)
    for q in rank9:
        q_hist = defaultdict(Counter)
        q_min = {}
        allowed_proper_with_L_le9 = []
        for rec in records:
            d = int(rec["dim8"])
            if d >= 7:
                continue
            pts = subspace_points_from_basis(unpack_basis(int(rec["key8"])))
            if all(parity_dot(q, p) == 0 for p in pts):
                L = int(rec["L"])
                q_hist[d][L] += 1
                dim_L_hist[d][L] += 1
                proper_min_by_dim[d] = min(proper_min_by_dim[d], L)
                q_min[d] = min(q_min.get(d, 999), L)
                if L <= 9:
                    allowed_proper_with_L_le9.append({
                        "dim8": d,
                        "L": L,
                        "key8": int(rec["key8"]),
                        "point_count": int(rec["point_count"]),
                    })
        if allowed_proper_with_L_le9:
            global_bad.append({"q": q, "count": len(allowed_proper_with_L_le9), "examples": allowed_proper_with_L_le9[:8]})
        per_q.append({
            "q": q,
            "proper_subspace_min_L_by_dim": {str(k): v for k, v in sorted(q_min.items())},
            "proper_subspaces_with_L_le9_count": len(allowed_proper_with_L_le9),
            "dim_L_hist": {str(d): {str(L): c for L, c in sorted(cnt.items())} for d, cnt in sorted(q_hist.items())},
        })

    result = {
        "schema": "single_q_trace_structure_v1",
        "field": "F2",
        "rank9_contractions": rank9,
        "rank9_count": len(rank9),
        "complete_core_table_meta": meta,
        "proper_subspace_global_min_L_by_dim": {str(k): v for k, v in sorted(proper_min_by_dim.items())},
        "proper_subspaces_inside_rank9_kernels_with_L_le9_count": sum(x["count"] for x in global_bad),
        "q_with_any_proper_L_le9": global_bad,
        "per_q_sample": per_q[:10],
        "consequence": "If every proper subspace W<ker(q) has L(W)>=10, then any length-19 Wang-admissible support with w(q)=9 must have its ten outside points span ker(q); the corrected one-q trace support condition is therefore automatic.",
        "elapsed_sec": round(time.time() - t0, 3),
    }
    out = OUTDIR / "single_q_trace_structure.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "elapsed_sec": result["elapsed_sec"],
        "rank9_count": len(rank9),
        "proper_subspaces_inside_rank9_kernels_with_L_le9_count": result["proper_subspaces_inside_rank9_kernels_with_L_le9_count"],
        "global_min_L_by_dim": result["proper_subspace_global_min_L_by_dim"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
