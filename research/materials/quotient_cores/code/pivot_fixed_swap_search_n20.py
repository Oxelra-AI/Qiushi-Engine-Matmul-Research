#!/usr/bin/env python3
"""Direct pivot-fixed n=20 full-Wang local search.

The lower-bound occupation question after the A-flattening reduction is whether
there is a 20-point full A-support containing a fixed rank-2 or rank-3 pivot
and satisfying every length-20 Wang occupation row.  CP-SAT CEGAR candidates
were still thousands of rows away from full feasibility.  This script attacks
the complete row system directly with a structure-preserving single-swap local
search:

  * support is a distinct 20-set and contains the pivot;
  * only non-pivot terms are swapped;
  * score primarily minimizes total positive excess sum(max(0,occ-cap)), not
    just the number of violated rows, so rows with excess > 1 guide the search.

It is not a proof engine, but it can decide whether feasible supports are easy
to find and gives sharper violation floors / row structure for later branch
proofs.
"""
from __future__ import annotations

import argparse
import json
import os
import struct
import sys
import time
from collections import Counter
from pathlib import Path
from typing import List, Sequence, Tuple

import numpy as np

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from pipeline_n22 import load_wang512_numpy, compute_occupation, mat33_rank  # type: ignore

DEFAULT_BINARY = SCRIPT.parent / "data" / "wang_native" / "full_tensor" / "full_wang512_cap19_len20_all_dim9_allbinding.bin"


def parse_multiset(s: str) -> List[int]:
    if Path(s).exists():
        data = json.loads(Path(s).read_text())
        for key in ("candidate_multiset", "multiset", "final_multiset", "selected_full_A_multiset", "A_multiset"):
            if key in data:
                return [int(x) for x in data[key]]
        raise KeyError(f"no multiset key in {s}")
    return [int(x) for x in s.replace("[", "").replace("]", "").split(",") if x.strip()]


def bit_has(masks: np.ndarray, rows: np.ndarray, d: int) -> np.ndarray:
    w, b = d >> 6, d & 63
    return ((masks[rows, w] >> np.uint64(b)) & np.uint64(1)).astype(np.float32)


def evaluate_swaps_excess(masks: np.ndarray, caps: np.ndarray, support: List[int], pivot: int,
                          violated: np.ndarray, bad: np.ndarray, diff: np.ndarray,
                          max_rank_sum: int | None = None,
                          min_rank_sum: int | None = None) -> Tuple[int, int, dict]:
    """Return best remove-position/add-direction by total-excess improvement."""
    ranks = [mat33_rank(a) for a in range(512)]
    cur_rank_sum = sum(ranks[a] for a in support)
    used = set(support)
    caps_i32 = caps.astype(np.int32)
    # rows where decrement can reduce total excess: diff>0
    dec_rows = violated
    # rows where increment increases total excess: diff>=0 (violated or tight)
    inc_rows = bad
    dec_masks = masks[dec_rows]
    inc_masks = masks[inc_rows]
    n_dec, n_inc = len(dec_rows), len(inc_rows)
    dec_has = np.zeros((512, n_dec), dtype=np.float32)
    inc_has = np.zeros((512, n_inc), dtype=np.float32)
    for d in range(1, 512):
        w, b = d >> 6, d & 63
        dec_has[d] = ((dec_masks[:, w] >> np.uint64(b)) & np.uint64(1)).astype(np.float32)
        inc_has[d] = ((inc_masks[:, w] >> np.uint64(b)) & np.uint64(1)).astype(np.float32)
    inc_sum = inc_has.sum(axis=1)
    best = {"score_total_excess": -10**9, "total_excess_after_est": None}
    top = []
    # only remove non-pivot entries
    for i, ai in enumerate(support):
        if ai == pivot:
            continue
        ai_dec = dec_has[ai]
        ai_inc = inc_has[ai]
        reduced = float(ai_dec.sum()) - (dec_has @ ai_dec)  # violated rows with ai in, d out
        added = inc_sum - (inc_has @ ai_inc)                # bad rows with d in, ai out
        scores = reduced - added
        scores[0] = -10**6
        scores[pivot] = -10**6
        for u in used:
            if u != ai:
                scores[u] = -10**6
        if max_rank_sum is not None or min_rank_sum is not None:
            for d in range(1, 512):
                rs_after = cur_rank_sum - ranks[ai] + ranks[d]
                if (max_rank_sum is not None and rs_after > max_rank_sum) or (min_rank_sum is not None and rs_after < min_rank_sum):
                    scores[d] = -10**6
        d0 = int(np.argmax(scores))
        sc = int(scores[d0])
        rec = {"remove_pos": int(i), "remove": int(ai), "add": d0, "score_total_excess": sc,
               "rank_sum_after": int(cur_rank_sum - ranks[ai] + ranks[d0])}
        top.append(rec)
        if sc > best["score_total_excess"]:
            best = rec
    top.sort(key=lambda x: (-x["score_total_excess"], x["rank_sum_after"]))
    return int(best["remove_pos"]), int(best["add"]), {"best": best, "top": top[:12], "n_dec_rows": int(n_dec), "n_inc_rows": int(n_inc)}


def summarize(masks: np.ndarray, caps: np.ndarray, dims: np.ndarray, support: Sequence[int]) -> dict:
    occ = compute_occupation(masks, list(support))
    diff = occ - caps.astype(np.int32)
    violated = np.where(diff > 0)[0]
    tight = np.where(diff == 0)[0]
    excess = diff[violated]
    return {
        "violations": int(len(violated)),
        "total_excess": int(excess.sum()) if len(excess) else 0,
        "max_excess": int(excess.max()) if len(excess) else 0,
        "tight_rows": int(len(tight)),
        "rank_sum_A": int(sum(mat33_rank(int(a)) for a in support)),
        "violation_dim_hist": dict(sorted((int(k), int(v)) for k, v in Counter(dims[violated].astype(int)).items())),
        "violation_excess_hist": dict(sorted((int(k), int(v)) for k, v in Counter(excess.astype(int)).items())),
    }


def search(binary: Path, pivot: int, seed: List[int], out: Path, max_iters: int, max_rank_sum: int | None, min_rank_sum: int | None) -> dict:
    if pivot not in seed:
        raise ValueError("seed must contain pivot")
    if len(seed) != 20:
        raise ValueError("pivot-fixed n=20 search needs a 20-term support")
    if len(set(seed)) != len(seed):
        raise ValueError("seed must be distinct; dim-1 rows enforce this at n=20")
    t0 = time.time()
    print(f"Loading {binary}", flush=True)
    masks, caps, dims, nrows = load_wang512_numpy(binary)
    print(f"Loaded {nrows} rows in {time.time()-t0:.2f}s", flush=True)
    support = [int(x) for x in seed]
    history = []
    for it in range(max_iters):
        occ = compute_occupation(masks, support)
        diff = occ - caps.astype(np.int32)
        violated = np.where(diff > 0)[0]
        tight = np.where(diff == 0)[0]
        bad = np.where(diff >= 0)[0]
        summ = summarize(masks, caps, dims, support)
        summ["iteration"] = it
        summ["support"] = [int(x) for x in support]
        print(f"iter {it}: viol={summ['violations']} total_excess={summ['total_excess']} max={summ['max_excess']} tight={summ['tight_rows']} rank_sum={summ['rank_sum_A']}", flush=True)
        if summ["violations"] == 0:
            summ["status"] = "ADMISSIBLE"
            history.append(summ)
            break
        ti = time.time()
        rem, add, ev = evaluate_swaps_excess(masks, caps, support, pivot, violated, bad, diff, max_rank_sum, min_rank_sum)
        ev["eval_sec"] = time.time() - ti
        summ["swap_eval"] = ev
        history.append(summ)
        sc = int(ev["best"]["score_total_excess"])
        print(f"  best: remove {support[rem]} add {add} score={sc} eval={ev['eval_sec']:.2f}s", flush=True)
        if sc <= 0:
            history[-1]["status"] = "STUCK"
            break
        support[rem] = add
    final = summarize(masks, caps, dims, support)
    result = {
        "schema": "pivot_fixed_swap_search_n20_v1",
        "pivot": int(pivot),
        "binary": str(binary),
        "seed": [int(x) for x in seed],
        "final_support": [int(x) for x in support],
        "max_rank_sum": max_rank_sum,
        "min_rank_sum": min_rank_sum,
        "iterations_recorded": len(history),
        "total_elapsed_sec": time.time() - t0,
        "final": final,
        "history": history,
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"out": str(out), "final": final, "elapsed_sec": result["total_elapsed_sec"]}, indent=2, sort_keys=True), flush=True)
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", type=Path, default=DEFAULT_BINARY)
    ap.add_argument("--pivot", type=int, required=True)
    ap.add_argument("--seed", required=True, help="comma list or json file with a multiset")
    ap.add_argument("--max-iters", type=int, default=40)
    ap.add_argument("--max-rank-sum", type=int, default=None)
    ap.add_argument("--min-rank-sum", type=int, default=None)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    seed = parse_multiset(args.seed)
    search(args.binary, args.pivot, seed, args.out, args.max_iters, args.max_rank_sum, args.min_rank_sum)


if __name__ == "__main__":
    main()
