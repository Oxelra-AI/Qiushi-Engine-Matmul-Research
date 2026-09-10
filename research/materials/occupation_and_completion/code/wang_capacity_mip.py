#!/usr/bin/env python3
"""Build LP/MIP files for Wang occupation capacity using generated cuts.

The variables x_p (p=1..511) count A-factor multiplicities.  Constraints are
linear packing inequalities sum_{p in Phi\0} x_p <= s - L(Phi).  This script
materializes useful finite cut sets (all dimensions up to a chosen dimension,
or cuts already learned by lazy solvers) into an LP file for external solvers.

It can also solve with scipy.milp when available.  This is useful as an
independent linear/integer optimizer surface from OR-Tools CP-SAT.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Set, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import unpack_basis, subspace_points_from_basis  # noqa: E402


def load_lut(path: Path):
    with path.open("rb") as f:
        payload = pickle.load(f)
    return payload["lut"], payload.get("meta", {})


def collect_keys(lut: Dict[int, int], init_max_dim: int, result_jsons: List[Path]) -> List[int]:
    keys: Set[int] = set()
    for key in lut:
        d = key & 0xF
        if 1 <= d <= init_max_dim:
            keys.add(key)
    for fp in result_jsons:
        d = json.loads(fp.read_text())
        for name in ["cut_records_head", "cut_records_tail"]:
            for c in d.get(name, []):
                keys.add(int(c["key"]))
        # Full iteration records keep violations_head, but not every cut; use
        # them as extra seeds when present.
        for it in d.get("iterations", []):
            for v in it.get("violations_head", []):
                keys.add(int(v.get("key", v.get("key9", 0))))
        # Some scripts stored no full cut list intentionally; this function is
        # conservative and only imports exact keys present in JSON.
    return sorted(keys)


def write_lp(lut: Dict[int, int], keys: List[int], s: int, out: Path) -> dict:
    t0 = time.time()
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w") as f:
        f.write("\\ Wang occupation capacity MIP\n")
        f.write("Minimize\n obj: 0\n")
        f.write("Subject To\n")
        f.write(" total: " + " + ".join(f"x{p}" for p in range(1, 512)) + f" = {s}\n")
        for i, key in enumerate(keys):
            lb = lut[key]
            cap = s - lb
            pts = subspace_points_from_basis(unpack_basis(key))
            # Skip full-space trivial LB0; retain everything else, including
            # negative cap cuts if any (they make infeasibility immediate).
            expr = " + ".join(f"x{p}" for p in pts) if pts else "0"
            f.write(f" c{i}: {expr} <= {cap}\n")
        f.write("Bounds\n")
        for p in range(1, 512):
            f.write(f" 0 <= x{p} <= {s}\n")
        f.write("Generals\n")
        for p in range(1, 512):
            f.write(f" x{p}\n")
        f.write("End\n")
    meta = {
        "lp_path": str(out),
        "rank_s": s,
        "constraint_count": len(keys) + 1,
        "subspace_cut_count": len(keys),
        "cuts_by_dim": dict(Counter(k & 0xF for k in keys)),
        "cuts_by_lb": dict(Counter(lut[k] for k in keys)),
        "elapsed_sec": time.time() - t0,
    }
    out.with_suffix(out.suffix + ".meta.json").write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n")
    return meta


def solve_scipy(lut: Dict[int, int], keys: List[int], s: int, time_limit: float) -> dict:
    import numpy as np
    from scipy.optimize import LinearConstraint, Bounds, milp
    from scipy.sparse import lil_matrix

    t0 = time.time()
    m = len(keys) + 1
    n = 511
    A = lil_matrix((m, n), dtype=float)
    lb = np.full(m, -np.inf)
    ub = np.empty(m)
    A[0, :] = 1.0
    lb[0] = s
    ub[0] = s
    for i, key in enumerate(keys, start=1):
        for p in subspace_points_from_basis(unpack_basis(key)):
            A[i, p-1] = 1.0
        ub[i] = s - lut[key]
    c = np.zeros(n)
    constraints = LinearConstraint(A.tocsr(), lb, ub)
    integrality = np.ones(n)
    bounds = Bounds(np.zeros(n), np.full(n, s))
    options = {"time_limit": time_limit, "mip_rel_gap": 0.0, "disp": True}
    res = milp(c, integrality=integrality, bounds=bounds, constraints=constraints, options=options)
    return {
        "success": bool(res.success),
        "status": int(res.status),
        "message": str(res.message),
        "fun": None if res.fun is None else float(res.fun),
        "elapsed_sec": time.time() - t0,
        "nonzero_solution": {str(i+1): int(round(v)) for i, v in enumerate(res.x)} if getattr(res, "x", None) is not None else None,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--rank", type=int, default=20)
    ap.add_argument("--init-max-dim", type=int, default=3)
    ap.add_argument("--result-json", action="append", type=Path, default=[])
    ap.add_argument("--out", type=Path, default=Path("data/wang_capacity_mip/t_level_s20_dim3.lp"))
    ap.add_argument("--solve-scipy", action="store_true")
    ap.add_argument("--time-limit", type=float, default=300.0)
    args = ap.parse_args()
    lut, meta = load_lut(args.lut)
    keys = collect_keys(lut, args.init_max_dim, args.result_json)
    print(f"Collected {len(keys):,} subspace cuts: by dim {dict(Counter(k&0xF for k in keys))}")
    lpmeta = write_lp(lut, keys, args.rank, args.out)
    print(json.dumps(lpmeta, indent=2, sort_keys=True))
    if args.solve_scipy:
        res = solve_scipy(lut, keys, args.rank, args.time_limit)
        respath = args.out.with_suffix(args.out.suffix + ".scipy_result.json")
        respath.write_text(json.dumps(res, indent=2, sort_keys=True) + "\n")
        print(json.dumps(res, indent=2, sort_keys=True)[:4000])
        print(f"Saved {respath}")


if __name__ == "__main__":
    main()
