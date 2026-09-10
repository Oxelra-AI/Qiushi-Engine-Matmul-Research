#!/usr/bin/env python3
"""Rank-n Wang/independent-verification-record pipeline with controls and rank-sum biased seeds.

This script is for calibration, not proof by sampling.  It runs the same
A-side Wang hill-climb plus B/C filters at n=23, where exact rank-23 schemes
are known, and at n=22 under optional low-A-rank bias.  A zero random SAT rate
at n=23 shows that random A-support volume is not evidence about n=22.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import List, Optional, Sequence, Tuple

import numpy as np

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))

from pipeline_n22 import load_wang512_numpy, compute_occupation, mat33_rank, brent_completion  # type: ignore

WORKSPACE = SCRIPT.parent
BINARIES = {
    22: WORKSPACE / "data" / "pivot_fixed_n22_binary" / "full_wang512_cap21_len22_all_dim9_allbinding.bin",
    23: WORKSPACE / "data" / "wang_native" / "full_tensor" / "full_wang512_cap22_len23_all_dim9_allbinding.bin",
}


def bit_membership(masks: np.ndarray, rows: np.ndarray, d: int) -> np.ndarray:
    w, b = d >> 6, d & 63
    return ((masks[rows, w] >> np.uint64(b)) & np.uint64(1)).astype(np.float32)


def rank_bounded_swap_search(masks: np.ndarray, caps: np.ndarray, seed: Sequence[int],
                             max_iters: int = 50, max_rank_sum: Optional[int] = None,
                             distinct: bool = True) -> Tuple[List[int], int, int, List[dict]]:
    """Single-swap hill-climb; optionally forbids moves above max_rank_sum."""
    ms = list(map(int, seed))
    ranks = [mat33_rank(a) for a in range(512)]
    hist: List[dict] = []
    for it in range(max_iters):
        occ = compute_occupation(masks, ms)
        diff = occ - caps.astype(np.int32)
        violated = np.where(diff > 0)[0]
        tight = np.where(diff == 0)[0]
        n_viol = int(len(violated))
        flat = int(sum(ranks[a] for a in ms))
        rec = {"iter": it, "violations": n_viol, "tight": int(len(tight)), "rank_sum": flat, "multiset": [int(x) for x in ms]}
        if n_viol == 0:
            rec["status"] = "ADMISSIBLE"
            hist.append(rec)
            return ms, 0, it, hist
        excess = diff[violated]
        fix_rows = violated[excess == 1]
        if len(fix_rows) == 0:
            rec["status"] = "NO_EXCESS1"
            hist.append(rec)
            return ms, n_viol, it, hist
        fix_masks = masks[fix_rows]
        tight_masks = masks[tight]
        n_fix = len(fix_rows)
        n_tight = len(tight)
        fix_has = np.zeros((512, n_fix), dtype=np.float32)
        tight_has = np.zeros((512, n_tight), dtype=np.float32)
        for d in range(1, 512):
            w, b = d >> 6, d & 63
            fix_has[d] = ((fix_masks[:, w] >> np.uint64(b)) & np.uint64(1)).astype(np.float32)
            tight_has[d] = ((tight_masks[:, w] >> np.uint64(b)) & np.uint64(1)).astype(np.float32)
        tight_sum = tight_has.sum(axis=1)
        used = set(ms)
        best_score = -10**9
        best_i = -1
        best_d = -1
        best_after = n_viol
        top = []
        for i, ai in enumerate(ms):
            ai_fix = fix_has[ai]
            ai_tight = tight_has[ai]
            fixed = float(ai_fix.sum()) - (fix_has @ ai_fix)
            created = tight_sum - (tight_has @ ai_tight)
            scores = fixed - created
            scores[0] = -10**6
            scores[ai] = -10**6
            if distinct:
                for u in used:
                    if u != ai:
                        scores[u] = -10**6
            if max_rank_sum is not None:
                for d in range(1, 512):
                    if flat - ranks[ai] + ranks[d] > max_rank_sum:
                        scores[d] = -10**6
            d0 = int(np.argmax(scores))
            sc = int(scores[d0])
            after = int(n_viol - sc)
            top.append({"remove_pos": int(i), "remove": int(ai), "add": int(d0), "score": sc, "violations_after": after,
                        "rank_sum_after": int(flat - ranks[ai] + ranks[d0])})
            if sc > best_score:
                best_score = sc
                best_i = i
                best_d = d0
                best_after = after
        top.sort(key=lambda x: (-x["score"], x["rank_sum_after"]))
        rec["best_swap"] = top[0]
        rec["top_swaps"] = top[:8]
        hist.append(rec)
        if best_score <= 0:
            hist[-1]["status"] = "STUCK"
            return ms, n_viol, it, hist
        ms[best_i] = best_d
    occ = compute_occupation(masks, ms)
    n_viol = int(np.sum(occ > caps.astype(np.int32)))
    return ms, n_viol, max_iters, hist


def enhanced_filter(multiset: Sequence[int], out_path: Path) -> Tuple[bool, dict]:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    cmd = [sys.executable, str(SCRIPT / "enhanced_trace_filter.py"),
           "--multiset", ",".join(map(str, multiset)), "--out", str(out_path)]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=60,
                          env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
    if proc.returncode != 0:
        return False, {"error": proc.stderr[-1000:], "returncode": proc.returncode}
    data = json.loads(out_path.read_text())
    return bool(data.get("enhanced_consistent", False)), data


def random_seed_by_rank_sum(rng: np.random.Generator, r: int, min_sum: Optional[int], max_sum: Optional[int]) -> List[int]:
    ranks = {1: [], 2: [], 3: []}
    for a in range(1, 512):
        ranks[mat33_rank(a)].append(a)
    if min_sum is None and max_sum is None:
        return rng.choice(np.arange(1, 512), size=r, replace=False).astype(int).tolist()
    triples = []
    for n1 in range(r + 1):
        for n2 in range(r - n1 + 1):
            n3 = r - n1 - n2
            if n1 <= len(ranks[1]) and n2 <= len(ranks[2]) and n3 <= len(ranks[3]):
                s = n1 + 2 * n2 + 3 * n3
                if (min_sum is None or s >= min_sum) and (max_sum is None or s <= max_sum):
                    triples.append((n1, n2, n3, s))
    if not triples:
        raise ValueError("no feasible rank-count triples")
    n1, n2, n3, _s = triples[int(rng.integers(len(triples)))]
    seed = []
    if n1:
        seed += rng.choice(ranks[1], size=n1, replace=False).astype(int).tolist()
    if n2:
        seed += rng.choice(ranks[2], size=n2, replace=False).astype(int).tolist()
    if n3:
        seed += rng.choice(ranks[3], size=n3, replace=False).astype(int).tolist()
    rng.shuffle(seed)
    return seed


def load_rank23_control() -> List[int]:
    p = WORKSPACE / "data" / "full_fixed_a_controls" / "pivot17_rank23" / "pivot17_rank23_result.json"
    data = json.loads(p.read_text())
    return [int(x) for x in data["A_multiset"]]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rank", type=int, choices=[22, 23], required=True)
    ap.add_argument("--binary", type=Path, default=None)
    ap.add_argument("--n-random", type=int, default=10)
    ap.add_argument("--seed", type=int, default=123)
    ap.add_argument("--min-rank-sum", type=int, default=None)
    ap.add_argument("--max-rank-sum", type=int, default=None)
    ap.add_argument("--max-swap-iters", type=int, default=50)
    ap.add_argument("--brent-timeout", type=int, default=60)
    ap.add_argument("--max-brent-candidates", type=int, default=20)
    ap.add_argument("--include-rank23-control", action="store_true")
    ap.add_argument("--outdir", type=Path, required=True)
    args = ap.parse_args()

    binary = args.binary or BINARIES[args.rank]
    args.outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    print(f"Loading {binary}", flush=True)
    masks, caps, dims, nrows = load_wang512_numpy(binary)
    print(f"Loaded {nrows} rows in {time.time()-t0:.2f}s", flush=True)
    rng = np.random.default_rng(args.seed)
    seeds: List[Tuple[str, List[int]]] = []
    if args.include_rank23_control:
        ctrl = load_rank23_control()
        if len(ctrl) == args.rank:
            seeds.append(("known_rank23_control", ctrl))
    for i in range(args.n_random):
        seeds.append((f"random_{args.seed}_{i}", random_seed_by_rank_sum(rng, args.rank, args.min_rank_sum, args.max_rank_sum)))

    results = []
    brent_used = 0
    for idx, (name, seed) in enumerate(seeds):
        print(f"\n[{idx+1}/{len(seeds)}] {name} seed_rank_sum={sum(mat33_rank(a) for a in seed)}", flush=True)
        s0 = time.time()
        ms, vio, iters, hist = rank_bounded_swap_search(masks, caps, seed, args.max_swap_iters, args.max_rank_sum)
        rec = {
            "name": name,
            "seed": [int(x) for x in seed],
            "seed_rank_sum": int(sum(mat33_rank(a) for a in seed)),
            "final_multiset": [int(x) for x in ms],
            "final_rank_sum": int(sum(mat33_rank(a) for a in ms)),
            "violations": int(vio),
            "swap_iters": int(iters),
            "search_sec": time.time() - s0,
            "history_head": hist[:5],
            "history_tail": hist[-3:],
        }
        print(f"  search vio={vio} iters={iters} rank_sum={rec['final_rank_sum']} sec={rec['search_sec']:.2f}", flush=True)
        if vio == 0:
            ok, edata = enhanced_filter(ms, args.outdir / "enhanced" / f"{name}.json")
            rec["enhanced_consistent"] = ok
            rec["tight_count"] = edata.get("tight_count")
            rec["tight_rank_hist"] = edata.get("tight_rank_hist")
            rec["enhanced_rank_aug"] = edata.get("enhanced_rank_aug")
            print(f"  enhanced={'OK' if ok else 'REJECT'} tight={rec.get('tight_count')} hist={rec.get('tight_rank_hist')}", flush=True)
            if ok and brent_used < args.max_brent_candidates:
                brent_used += 1
                sat, bdata = brent_completion(ms, args.outdir / "brent" / name, name, args.brent_timeout)
                rec["brent_sat"] = sat
                rec["brent_returncode"] = bdata.get("returncode", -1)
                rec["brent_vars"] = bdata.get("vars", 0)
                rec["brent_clauses"] = bdata.get("clauses", 0)
                rec["brent_sec"] = bdata.get("elapsed_sec", None)
                rec["verification_diff"] = bdata.get("verification_diff", None)
                print(f"  brent sat={sat} rc={rec['brent_returncode']} sec={rec['brent_sec']}", flush=True)
        results.append(rec)
        (args.outdir / "pipeline_rank_control_summary.json").write_text(json.dumps({
            "schema": "pipeline_rank_control_v1",
            "rank": args.rank,
            "binary": str(binary),
            "seed": args.seed,
            "rank_sum_window": [args.min_rank_sum, args.max_rank_sum],
            "brent_timeout": args.brent_timeout,
            "elapsed_sec": time.time() - t0,
            "results": results,
        }, indent=2, sort_keys=True) + "\n")

    summary = {
        "schema": "pipeline_rank_control_v1",
        "rank": args.rank,
        "binary": str(binary),
        "seed": args.seed,
        "rank_sum_window": [args.min_rank_sum, args.max_rank_sum],
        "n_random": args.n_random,
        "include_rank23_control": args.include_rank23_control,
        "brent_timeout": args.brent_timeout,
        "elapsed_sec": time.time() - t0,
        "counts": {
            "total": len(results),
            "admissible": sum(1 for r in results if r["violations"] == 0),
            "enhanced_pass": sum(1 for r in results if r.get("enhanced_consistent") is True),
            "brent_sat": sum(1 for r in results if r.get("brent_sat") is True),
            "brent_unsat": sum(1 for r in results if r.get("brent_sat") is False),
            "brent_unknown": sum(1 for r in results if "brent_sat" in r and r.get("brent_sat") is None),
        },
        "results": results,
    }
    out = args.outdir / "pipeline_rank_control_summary.json"
    out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(out), "counts": summary["counts"], "elapsed_sec": summary["elapsed_sec"]}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
