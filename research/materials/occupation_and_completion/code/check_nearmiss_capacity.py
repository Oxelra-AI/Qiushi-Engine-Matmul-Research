#!/usr/bin/env python3
"""Check rank-21 core near-miss A-supports against complete Wang capacity.

research_record found rank-21 core decompositions where deleting an equal-W pair leaves
19 two-factor columns whose span misses exactly one output mode.  This script
asks a separate A-side question: do the 19 remaining A-factors satisfy the
complete Wang-derived core occupation constraints?  If a near-miss support
passes, it is a promising fixed-A surface for B/C-only search.  If it fails, the
violating subspaces show why Wang's A-side restrictions push away from that
local rank-19 surface.
"""
from __future__ import annotations

import argparse
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from core_capacity_from_wang_lut import CoreQuotient, PIVOTS  # noqa: E402
from wang_capacity_lazy import unpack_basis, subspace_points_from_basis, pack_basis  # noqa: E402
from wang_capacity_orbit_closed import extension_keys  # noqa: E402

DEFAULTS = {
    "E11": {
        "pivot": "E11",
        "pool": "data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy",
        "structure": "data/e11_rank21_pool_structure_full_examples_v2.json",
    },
    "E13_E22_E31": {
        "pivot": "E13_E22_E31",
        "pool": "data/e13e22e31_flip_workspace/data/schemes_modp/e13e22e31core/mod2-rank21a.npy",
        "structure": "data/e13e22e31_rank21_pool_structure_v2.json",
    },
}


def load_lut(path: Path):
    with path.open("rb") as f:
        payload = pickle.load(f)
    return payload["lut"], payload.get("meta", {})


def enumerate_subspace_keys(n: int = 8) -> List[int]:
    levels = {0: {pack_basis(tuple())}}
    all_keys = set(levels[0])
    for d in range(n):
        nxt = set()
        for key in levels[d]:
            for ekey in extension_keys(unpack_basis(key), n=n):
                if (ekey & 0xF) == d + 1:
                    nxt.add(ekey)
        levels[d + 1] = nxt
        all_keys.update(nxt)
    return sorted(all_keys)


def bitset_for_points(points: Iterable[int]) -> int:
    b = 0
    for p in points:
        b |= 1 << int(p)
    return b


def build_core_constraints(core: CoreQuotient, lut: Dict[int, int], s: int) -> Tuple[List[Tuple[int, int, int, int]], dict]:
    t0 = time.time()
    keys8 = enumerate_subspace_keys(8)
    cons = []
    by_dim = Counter()
    by_L = Counter()
    for key8 in keys8:
        key9 = core.key9_from_key8(key8)
        L = lut[key9]
        cap = s - L
        pts = subspace_points_from_basis(unpack_basis(key8))
        pbits = bitset_for_points(pts)
        cons.append((key8, L, cap, pbits))
        by_dim[key8 & 0xF] += 1
        by_L[L] += 1
    meta = {
        "constraint_count": len(cons),
        "constraints_by_dim8": dict(by_dim),
        "constraints_by_original_L": dict(by_L),
        "rank_s": s,
        "elapsed_sec": time.time() - t0,
    }
    return cons, meta


def multiset_bit_data(points: List[int]) -> Tuple[int, Dict[int, int], List[Tuple[int, int]]]:
    c = Counter(points)
    bitset = bitset_for_points(c.keys())
    dup = [(p, cnt - 1) for p, cnt in c.items() if cnt > 1]
    return bitset, dict(c), dup


def occ_from_bitset(pbits: int, support_bits: int, dup_extra: List[Tuple[int, int]]) -> int:
    occ = (pbits & support_bits).bit_count()
    for p, extra in dup_extra:
        if (pbits >> p) & 1:
            occ += extra
    return occ


def check_support(points: List[int], constraints, max_report=20):
    support_bits, mult, dup_extra = multiset_bit_data(points)
    violations = []
    for key8, L, cap, pbits in constraints:
        occ = occ_from_bitset(pbits, support_bits, dup_extra)
        if occ > cap:
            violations.append({"key8": key8, "dim8": key8 & 0xF, "L": L, "cap": cap, "occupancy": occ, "excess": occ - cap, "basis8": list(unpack_basis(key8))})
    violations.sort(key=lambda v: (v["excess"], v["L"], v["occupancy"], -v["dim8"]), reverse=True)
    return {
        "support_size": len(mult),
        "total_multiplicity": sum(mult.values()),
        "max_multiplicity": max(mult.values()) if mult else 0,
        "multiplicity_profile": dict(Counter(mult.values())),
        "A_multiset": {str(k): v for k, v in sorted(mult.items())},
        "violation_count": len(violations),
        "violations_by_dim8": dict(Counter(v["dim8"] for v in violations)),
        "violations_by_L": dict(Counter(v["L"] for v in violations)),
        "max_excess": max((v["excess"] for v in violations), default=0),
        "violations_head": violations[:max_report],
    }


def load_examples(structure_path: Path, max_examples: int = 0):
    data = json.loads(structure_path.read_text())
    examples = data.get("deficiency_one_examples", [])
    if max_examples:
        examples = examples[:max_examples]
    return data, examples


def run(label: str, cfg: dict, lut: Dict[int, int], outdir: Path, max_examples: int = 0) -> dict:
    pivot_name = cfg["pivot"]
    pivot = PIVOTS[pivot_name]
    core = CoreQuotient(pivot)
    pool = np.load(cfg["pool"])
    structure, examples = load_examples(Path(cfg["structure"]), max_examples=max_examples)
    rank = int(structure.get("rank", 21))
    cons, cons_meta = build_core_constraints(core, lut, s=19)
    print(f"{label}: loaded pool {pool.shape}, examples={len(examples)}, constraints={cons_meta['constraint_count']:,}")

    records = []
    pass_records = []
    by_viol = Counter()
    by_max_excess = Counter()
    by_mode = Counter()
    by_w = Counter()
    t0 = time.time()
    for idx, ex in enumerate(examples):
        si = int(ex["scheme_index"])
        deleted = set(int(x) for x in ex["deleted"])
        row = [int(x) for x in pool[si].tolist()]
        terms = [tuple(row[3*i:3*i+3]) for i in range(rank)]
        remain_u = [terms[i][0] for i in range(rank) if i not in deleted]
        chk = check_support(remain_u, cons, max_report=10)
        rec = {
            "example_index": idx,
            "scheme_index": si,
            "deleted": sorted(deleted),
            "mode": ex.get("mode"),
            "mode_bits": ex.get("mode_bits"),
            "deleted_w": ex.get("deleted_w"),
            "support_check": {k: v for k, v in chk.items() if k not in ("A_multiset", "violations_head")},
            "A_multiset": chk["A_multiset"],
            "violations_head": chk["violations_head"],
        }
        records.append(rec)
        by_viol[chk["violation_count"]] += 1
        by_max_excess[chk["max_excess"]] += 1
        by_mode[ex.get("mode")] += 1
        if ex.get("deleted_w"):
            by_w[tuple(ex.get("deleted_w"))] += 1
        if chk["violation_count"] == 0:
            pass_records.append(rec)
        if (idx + 1) % 100 == 0:
            print(f"  {label}: checked {idx+1}/{len(examples)}; passes={len(pass_records)}; elapsed={time.time()-t0:.1f}s")
    # Summarize top violation types from all heads.
    head_dim = Counter()
    head_L = Counter()
    top_basis = Counter()
    for rec in records:
        for v in rec["violations_head"][:3]:
            head_dim[v["dim8"]] += 1
            head_L[v["L"]] += 1
            top_basis[tuple(v["basis8"])] += 1
    result = {
        "label": label,
        "pivot_name": pivot_name,
        "pivot_mask": pivot,
        "rank21_pool": cfg["pool"],
        "structure_file": cfg["structure"],
        "near_miss_examples_checked": len(examples),
        "constraint_meta": cons_meta,
        "pass_count": len(pass_records),
        "fail_count": len(records) - len(pass_records),
        "violation_count_distribution": {str(k): v for k, v in sorted(by_viol.items())},
        "max_excess_distribution": {str(k): v for k, v in sorted(by_max_excess.items())},
        "top_head_violation_dims": dict(head_dim.most_common()),
        "top_head_violation_L": dict(head_L.most_common()),
        "top_head_violation_bases": [{"basis8": list(k), "count": v} for k, v in top_basis.most_common(20)],
        "passes": pass_records[:50],
        "records_head": records[:20],
        "records_tail": records[-20:],
        "elapsed_sec": time.time() - t0,
        "meaning": "A pass is an A-side Wang-capacity-admissible 19-term support from an equal-W rank-21 near miss. It is not a decomposition; it is a surface for fixed-A B/C search. A fail only rules out that exact A multiset as a rank-19 core decomposition.",
    }
    outdir.mkdir(parents=True, exist_ok=True)
    outpath = outdir / f"near_miss_capacity_{label}.json"
    outpath.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"{label}: pass_count={len(pass_records)} fail_count={len(records)-len(pass_records)} elapsed={result['elapsed_sec']:.1f}s saved {outpath}")
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--outdir", type=Path, default=Path("data/nearmiss_capacity"))
    ap.add_argument("--which", choices=["E11", "E13_E22_E31", "all"], default="all")
    ap.add_argument("--max-examples", type=int, default=0)
    args = ap.parse_args()
    lut, meta = load_lut(args.lut)
    print(f"Loaded LUT {len(lut):,}; coverage_ok={meta.get('coverage_ok')} conflicts={meta.get('conflict_count')}")
    todo = DEFAULTS.items() if args.which == "all" else [(args.which, DEFAULTS[args.which])]
    summary = {}
    for label, cfg in todo:
        summary[label] = run(label, cfg, lut, args.outdir, max_examples=args.max_examples)
    (args.outdir / "near_miss_capacity_summary.json").write_text(json.dumps({k: {kk: vv for kk, vv in v.items() if kk not in ("records_head", "records_tail", "passes")} for k, v in summary.items()}, indent=2, sort_keys=True) + "\n")
    print(f"Saved summary to {args.outdir / 'near_miss_capacity_summary.json'}")


if __name__ == "__main__":
    main()
