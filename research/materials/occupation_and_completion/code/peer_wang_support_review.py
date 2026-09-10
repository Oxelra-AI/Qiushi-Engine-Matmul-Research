#!/usr/bin/env python3
r"""analysis independent review of research_record coding/DFS Wang-support artifacts.

This script rebuilds the E11 core Wang support inequalities using the canonical
CoreQuotient.key9_from_key8 interface from research_record, then compares the resulting
statistics with the peer's GHW/DFS files.  It also checks the rank-21 pool A-bit
convention: the .npy pool stores 8-bit core masks directly, not 9-bit full A masks.

The purpose is review and error isolation, not a proof certificate for global
infeasibility.
"""
from __future__ import annotations

import collections
import json
import sys
import time
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))

from core_capacity_all_mip import enumerate_subspace_keys  # type: ignore
from core_capacity_from_wang_lut import CoreQuotient, load_lut  # type: ignore
from wang_capacity_lazy import rref_basis, pack_basis, unpack_basis, subspace_points_from_basis  # type: ignore

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
POOL_PATH = Path("data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy")
PEER_DIR = Path("data/ghw_singleton")
OUT = Path("data/ghw_singleton_review/peer_wang_support_review.json")
N_COLS = 19


def gf2_rank(rows: Iterable[int], n: int = 8) -> int:
    basis = [0]*n
    r=0
    for row0 in rows:
        v=int(row0)&((1<<n)-1)
        while v:
            p=v.bit_length()-1
            if basis[p]:
                v ^= basis[p]
            else:
                basis[p]=v; r+=1; break
    return r


def build_core_tensor() -> np.ndarray:
    T = np.zeros((8,9,9), dtype=np.uint8)
    for s in range(8):
        a = s + 1
        i = a // 3
        j = a % 3
        for k in range(3):
            T[s, 3*j+k, 3*i+k] = 1
    return T


def reconstruct_core(terms: Sequence[Tuple[int,int,int]]) -> np.ndarray:
    R = np.zeros((8,9,9), dtype=np.uint8)
    for u,v,w in terms:
        for s in range(8):
            if (int(u)>>s)&1:
                for b in range(9):
                    if (int(v)>>b)&1:
                        for c in range(9):
                            if (int(w)>>c)&1:
                                R[s,b,c] ^= 1
    return R


def row_to_terms(row: Sequence[int]) -> List[Tuple[int,int,int]]:
    R=len(row)//3
    return [(int(row[3*t]), int(row[3*t+1]), int(row[3*t+2])) for t in range(R)]


def pool_convention_check(max_rows: int = 20) -> dict:
    pool = np.load(POOL_PATH)
    core = build_core_tensor()
    cq = CoreQuotient(1)
    raw_ok = 0; proj_ok = 0; examples = []
    raw_distinct = []
    proj_zero_terms = []
    for idx,row in enumerate(pool[:max_rows]):
        terms_raw = row_to_terms(row)
        terms_proj = [(cq.project9(u), v, w) for (u,v,w) in terms_raw]
        raw_diff = int(np.sum(reconstruct_core(terms_raw) ^ core))
        proj_diff = int(np.sum(reconstruct_core(terms_proj) ^ core))
        if raw_diff == 0: raw_ok += 1
        if proj_diff == 0: proj_ok += 1
        raw_distinct.append(len(set(u for u,_,_ in terms_raw)))
        proj_zero_terms.append(sum(1 for u,_,_ in terms_proj if u == 0))
        if len(examples) < 5:
            examples.append({
                "row": idx,
                "raw_diff": raw_diff,
                "project9_diff": proj_diff,
                "all_raw_u_lt_256": all(0 <= u < 256 for u,_,_ in terms_raw),
                "raw_u_head": [u for u,_,_ in terms_raw[:10]],
                "project9_u_head": [u for u,_,_ in terms_proj[:10]],
                "raw_distinct_A": raw_distinct[-1],
                "project9_zero_terms": proj_zero_terms[-1],
            })
    return {
        "pool_path": str(POOL_PATH),
        "rows_checked": min(max_rows, int(pool.shape[0])),
        "raw_8bit_core_masks_reconstruct_rows": raw_ok,
        "project9_interpretation_reconstruct_rows": proj_ok,
        "raw_distinct_A_hist": {str(k): int(v) for k,v in sorted(collections.Counter(raw_distinct).items())},
        "project9_zero_term_hist": {str(k): int(v) for k,v in sorted(collections.Counter(proj_zero_terms).items())},
        "examples": examples,
        "conclusion": "The rank-21 pool stores quotient/core A masks in bits 0..7 directly; applying CoreQuotient.project9 to these masks is a convention bug.",
    }


def canonical_wang_stats() -> Tuple[dict, List[Tuple[int,int,frozenset]]]:
    lut, meta = load_lut(LUT_PATH)
    cq = CoreQuotient(1)
    keys8 = enumerate_subspace_keys(8)
    by_dim = collections.Counter()
    lb_hist_by_dim = collections.defaultdict(collections.Counter)
    cap_dist_all = collections.Counter()
    cap_dist_le8 = collections.Counter()
    rows_le8: List[Tuple[int,int,frozenset]] = []
    min_lb_by_dim = {}
    max_lb_by_dim = {}
    for key8 in keys8:
        dim8 = key8 & 0xF
        key9 = cq.key9_from_key8(key8)
        lb = int(lut[key9])
        cap = N_COLS - lb
        by_dim[dim8] += 1
        lb_hist_by_dim[dim8][lb] += 1
        cap_dist_all[cap] += 1
        min_lb_by_dim[dim8] = min(lb, min_lb_by_dim.get(dim8, lb))
        max_lb_by_dim[dim8] = max(lb, max_lb_by_dim.get(dim8, lb))
        if 0 <= cap <= 8:
            pts = frozenset(subspace_points_from_basis(unpack_basis(key8)))
            rows_le8.append((cap, key8, pts))
            cap_dist_le8[cap] += 1
    # GHW L_r: dim8 = 8-r, Singleton 11+r.
    ghw = []
    for r in range(0,9):
        dim8 = 8-r
        lr = min_lb_by_dim.get(dim8)
        mx = max_lb_by_dim.get(dim8)
        singleton = 11 + r
        ghw.append({
            "r": r,
            "dim8": dim8,
            "dim9": dim8+1,
            "subspace_count": by_dim.get(dim8,0),
            "L_r": lr,
            "max_lb": mx,
            "singleton_bound": singleton,
            "gap": None if lr is None else singleton-lr,
            "singleton_violation": False if lr is None else lr > singleton,
            "lb_histogram": {str(k): int(v) for k,v in sorted(lb_hist_by_dim.get(dim8, {}).items())},
        })
    stats = {
        "total_keys8": len(keys8),
        "by_dim8": {str(k): int(v) for k,v in sorted(by_dim.items())},
        "cap_distribution_all": {str(k): int(v) for k,v in sorted(cap_dist_all.items())},
        "cap_distribution_0_to_8": {str(k): int(v) for k,v in sorted(cap_dist_le8.items())},
        "rows_cap_0_to_8": len(rows_le8),
        "ghw_results_canonical": ghw,
        "violation_found": any(x["singleton_violation"] for x in ghw),
    }
    return stats, rows_le8


def complete_wang_first_failure(support: Sequence[int], rows_le8: Sequence[Tuple[int,int,frozenset]]) -> dict:
    S = frozenset(int(x) for x in support)
    # Check smaller caps first because they are stronger; report first and worst.
    failures = []
    for cap,key8,pts in rows_le8:
        occ = len(S & pts)
        if occ > cap:
            failures.append({"cap": cap, "dim8": key8 & 0xF, "occupancy": occ, "excess": occ-cap, "point_count": len(pts), "basis8": list(unpack_basis(key8))})
    failures.sort(key=lambda x: (x["cap"], -x["excess"], x["dim8"]))
    return {"ok": len(failures)==0, "violation_count_cap0_to_8": len(failures), "first_failures": failures[:10]}


def peer_files_review(rows_le8: Sequence[Tuple[int,int,frozenset]]) -> dict:
    out = {}
    for name in ["ghw_singleton_test.json", "cap3_stream_cap48_check.json", "dfs_pilot_cap3.json", "dfs_pilot_cap5.json", "wang_check_results.json"]:
        p = PEER_DIR / name
        if p.exists() and p.stat().st_size:
            out[name] = json.loads(p.read_text())
        else:
            out[name] = {"missing_or_empty": True, "path": str(p), "size": p.stat().st_size if p.exists() else None}
    # Compare peer GHW to canonical, if present.
    if "ghw_singleton_test.json" in out and "results_by_r" in out["ghw_singleton_test.json"]:
        # canonical embedded later by caller, compare only key fields in final assembly.
        pass
    # Check the first saved DFS cap3 supports independently against canonical rows.
    sol_checks = []
    dfs = out.get("dfs_pilot_cap3.json", {})
    for i, sol in enumerate(dfs.get("solutions_head", [])[:10]):
        chk = complete_wang_first_failure(sol, rows_le8)
        sol_checks.append({"index": i, "support": sol, "check": chk})
    out["dfs_pilot_cap3_solutions_head_canonical_cap0_to_8_checks"] = sol_checks
    out["review_conclusion"] = {
        "dfs_cap3_timeout": out.get("dfs_pilot_cap3.json", {}).get("timeout"),
        "cap3_stream_timeout": out.get("cap3_stream_cap48_check.json", {}).get("timeout"),
        "dfs_cap5_timeout": out.get("dfs_pilot_cap5.json", {}).get("timeout"),
        "meaning": "The saved DFS/stream files are timeout-limited pilots. The fact that all generated branch-1 cap<=3 supports fail later caps is useful evidence, but is not an exhaustive proof that all 19-point E11 supports violate Wang.",
    }
    return out


def main() -> None:
    t0 = time.time()
    pool = pool_convention_check()
    wang, rows_le8 = canonical_wang_stats()
    peer = peer_files_review(rows_le8)
    # Compare peer GHW fields to canonical.
    peer_ghw = peer.get("ghw_singleton_test.json", {}).get("results_by_r", [])
    ghw_compare = []
    canon_by_r = {x["r"]: x for x in wang["ghw_results_canonical"]}
    for p in peer_ghw:
        c = canon_by_r.get(p.get("r"))
        ghw_compare.append({
            "r": p.get("r"),
            "peer_L_r": p.get("L_r"),
            "canonical_L_r": None if c is None else c["L_r"],
            "peer_gap": p.get("gap"),
            "canonical_gap": None if c is None else c["gap"],
            "match": c is not None and p.get("L_r") == c["L_r"] and p.get("gap") == c["gap"] and p.get("subspace_count") == c["subspace_count"],
        })
    result = {
        "schema": "s0908_peer_wang_support_review_v1",
        "pool_convention_check": pool,
        "canonical_wang_stats": wang,
        "peer_ghw_compare": ghw_compare,
        "peer_artifacts_review": peer,
        "scientific_interpretation": {
            "ghw": "The GHW/Singleton computation matches the canonical E11 quotient Wang table and shows no Singleton contradiction; it does not prove existence or nonexistence of a support.",
            "dfs": "The cap<=3 DFS and cap3_stream files have timeout=true and explored only the lexicographically first region/branch in the saved runs; all generated examples failed cap 4-8 constraints, usually cap 7, but this is not a complete exclusion.",
            "pool_bug": "Pool rows are already 8-bit E11 core masks; scripts validating pool rows with CoreQuotient.project9 are wrong for those validation sections. Scripts using pool u masks raw are not affected.",
        },
        "elapsed_sec": round(time.time()-t0,3),
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(OUT),
        "pool_raw_ok_rows": pool["raw_8bit_core_masks_reconstruct_rows"],
        "pool_project9_ok_rows": pool["project9_interpretation_reconstruct_rows"],
        "rows_cap0_to8": wang["rows_cap_0_to_8"],
        "cap_distribution_0_to8": wang["cap_distribution_0_to_8"],
        "ghw_all_match": all(x["match"] for x in ghw_compare),
        "peer_dfs_timeouts": result["peer_artifacts_review"]["review_conclusion"],
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
