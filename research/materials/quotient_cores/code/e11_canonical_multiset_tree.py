#!/usr/bin/env python3
"""Canonical E11 rank-19 A-multiset search tree with exact Wang separation.

This is a proof-oriented support-search layer for the finite-field E11 route.
It is deliberately separated from generic CP-SAT time extensions.

Objects:
  * Points are nonzero quotient A-factors in F2^8, encoded as masks 1..255.
  * A rank-19 A-multiset has multiplicities bounded by the exact singleton
    Wang capacities: 249 points have cap 1, six points have cap 2.
  * The verified 576-element E11 quotient action acts on whole multisets.

Canonical augmentation:
  canon(S) is the lexicographically smallest sorted multiset in the orbit of S.
  parent(C) for a canonical nonempty multiset C is the lexicographically smallest
  canon(C with one occurrence removed).  A child C' is generated from C only if
      canon(C') = C' and parent(C') = C.
This is the standard invariant-parent construction; it enumerates one canonical
representative per multiset orbit when run to a fixed size without node limits.

Separation:
  Every prefix stores its exact occupancy vector on all 417,199 cached E11 Wang
  subspaces.  If any occupancy exceeds the cached capacity, the entire branch is
  pruned permanently, because later additions only increase occupancies.  The
  emitted JSONL record gives the exact prefix, violated subspace index/key, and
  subspace orbit id.  The 1,496-orbit object is used as provenance for constraint
  images, not as a replacement for checking moved inequalities.

A complete run to depth 19 whose frontier is exhausted would be a replayable
occupation-infeasibility certificate.  Partial/node-limited runs are only search
state and pruning diagnostics.
"""
from __future__ import annotations

import argparse
import json
import pickle
import subprocess
import sys
import time
from collections import Counter, defaultdict
from functools import lru_cache
from pathlib import Path
from typing import Iterable

import numpy as np

SCRIPTS_A02 = Path("scripts")
if str(SCRIPTS_A02) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_A02))

from e11_capacity_incremental_sat import (  # noqa: E402
    build_or_load_constraint_cache,
    mask_to_points,
)


def load_perms(perms_path: Path) -> list[tuple[int, ...]]:
    arr = np.load(perms_path)["perms"]
    perms = [tuple(int(x) for x in row.tolist()) for row in arr]
    if len(perms) != 576:
        raise ValueError(f"expected 576 permutations, got {len(perms)}")
    if any(p[0] != 0 or set(p[1:]) != set(range(1, 256)) for p in perms):
        raise ValueError("bad quotient permutation array")
    return perms


def point_caps_from_cache(cache: dict) -> np.ndarray:
    caps = np.zeros(256, dtype=np.int16)
    for m, cap, dim in zip(cache["masks"], cache["caps"], cache["dims"]):
        if int(dim) == 1 and int(m).bit_count() == 1:
            p = int(m).bit_length()
            caps[p] = int(cap)
    if int(np.count_nonzero(caps[1:])) != 255:
        raise ValueError("bad singleton capacity coverage")
    return caps


def build_or_load_membership(cache: dict, path: Path, force: bool = False) -> np.ndarray:
    N = len(cache["masks"])
    if path.exists() and not force:
        M = np.load(path, mmap_mode=None)
        if M.shape != (256, N):
            raise ValueError(f"bad membership shape {M.shape}, expected {(256, N)}")
        return M.astype(np.uint8, copy=False)
    path.parent.mkdir(parents=True, exist_ok=True)
    M = np.zeros((256, N), dtype=np.uint8)
    t0 = time.time()
    for i, m0 in enumerate(cache["masks"]):
        m = int(m0)
        while m:
            lb = m & -m
            p = lb.bit_length()
            M[p, i] = 1
            m ^= lb
        if (i + 1) % 100000 == 0:
            print(f"  membership {i+1:,}/{N:,}")
    np.save(path, M)
    print(f"built membership in {time.time()-t0:.2f}s at {path}")
    return M


def load_subspace_orbit_ids(path: Path, n: int) -> np.ndarray:
    if not path.exists():
        return np.full(n, -1, dtype=np.int32)
    data = np.load(path)
    oid = data["orbit_id"].astype(np.int32, copy=False)
    if oid.shape != (n,):
        raise ValueError(f"bad orbit_id shape {oid.shape}, expected {(n,)}")
    return oid


def counts_to_tuple(counts: np.ndarray) -> tuple[int, ...]:
    out: list[int] = []
    for p in range(1, 256):
        out.extend([p] * int(counts[p]))
    return tuple(out)


def tuple_to_counts(ms: Iterable[int]) -> np.ndarray:
    c = np.zeros(256, dtype=np.int16)
    for p in ms:
        c[int(p)] += 1
    return c


def solution_dict(ms: tuple[int, ...]) -> dict[int, int]:
    d: dict[int, int] = {}
    for p in ms:
        d[p] = d.get(p, 0) + 1
    return d


def make_canonical_functions(perms: list[tuple[int, ...]]):
    @lru_cache(maxsize=None)
    def canonical(ms: tuple[int, ...]) -> tuple[int, ...]:
        base = tuple(sorted(int(x) for x in ms))
        best = base
        for perm in perms:
            img = tuple(sorted(perm[x] for x in base))
            if img < best:
                best = img
        return best

    @lru_cache(maxsize=None)
    def canonical_parent(canon_ms: tuple[int, ...]) -> tuple[int, ...]:
        if not canon_ms:
            raise ValueError("empty multiset has no parent")
        best = None
        # Delete one representative of each equal-valued occurrence.
        last = None
        for i, x in enumerate(canon_ms):
            if x == last:
                continue
            last = x
            parent = canon_ms[:i] + canon_ms[i+1:]
            cp = canonical(parent)
            if best is None or cp < best:
                best = cp
        assert best is not None
        return best

    return canonical, canonical_parent


def first_violation(occ: np.ndarray, caps: np.ndarray) -> int | None:
    bad = np.flatnonzero(occ > caps)
    if len(bad) == 0:
        return None
    # Prefer largest excess, then strongest L/cap handled by caller if desired.
    return int(bad[0])


def violation_record(prefix: tuple[int, ...], occ: np.ndarray, cache: dict, orbit_id: np.ndarray, index: int, reason: str) -> dict:
    i = int(index)
    return {
        "reason": reason,
        "prefix": list(prefix),
        "prefix_size": len(prefix),
        "subspace_index": i,
        "subspace_orbit_id": int(orbit_id[i]) if i < len(orbit_id) else -1,
        "key8": int(cache["keys8"][i]),
        "dim8": int(cache["dims"][i]),
        "L": int(cache["Ls"][i]),
        "cap": int(cache["caps"][i]),
        "occupancy": int(occ[i]),
        "excess": int(occ[i]) - int(cache["caps"][i]),
        "point_count": int(cache["masks"][i]).bit_count(),
        "points_head": mask_to_points(int(cache["masks"][i]))[:80],
    }


def brute_force_orbit_count_size2(point_caps: np.ndarray, canonical) -> dict:
    reps = set()
    total = 0
    for a in range(1, 256):
        for b in range(a, 256):
            if a == b and point_caps[a] < 2:
                continue
            total += 1
            reps.add(canonical((a, b)))
    return {"size": 2, "raw_valid_multisets": total, "orbit_representatives": len(reps)}


def generated_count_no_prune_size2(point_caps: np.ndarray, canonical, canonical_parent) -> dict:
    root: tuple[int, ...] = tuple()
    level1 = []
    for p in range(1, 256):
        child = (p,)
        if canonical(child) == child and canonical_parent(child) == root:
            level1.append(child)
    level2 = []
    for node in level1:
        counts = tuple_to_counts(node)
        for p in range(1, 256):
            if counts[p] >= point_caps[p]:
                continue
            child = tuple(sorted(node + (p,)))
            if canonical(child) != child:
                continue
            if canonical_parent(child) != node:
                continue
            level2.append(child)
    return {"level1": len(level1), "level2": len(level2), "level2_unique": len(set(level2))}


def run_fixed_u_xor(ms: tuple[int, ...], outdir: Path, name: str, timeout: int, threads: int) -> dict:
    cmd = [
        sys.executable, "-B", "scripts/e11_fixed_u_xor_sat.py",
        "--u-list", ",".join(str(x) for x in ms),
        "--outdir", str(outdir),
        "--name", name,
        "--timeout", str(timeout),
        "--threads", str(threads),
    ]
    t0 = time.time()
    proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=timeout + 30)
    json_path = outdir / f"{name}.json"
    data = json.loads(json_path.read_text()) if json_path.exists() else {}
    return {
        "command": " ".join(cmd),
        "returncode": proc.returncode,
        "elapsed_sec": time.time() - t0,
        "json_path": str(json_path),
        "status": data.get("solver_status", "NO_JSON"),
        "decoded_verified": data.get("decoded_solution", {}).get("verified"),
        "stdout_tail": proc.stdout[-2000:],
        "stderr_tail": proc.stderr[-1000:],
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lut", type=Path, default=Path("data/wang_f2_lb20/wang_subspace_lut.pkl"))
    ap.add_argument("--cache", type=Path, default=Path("data/e11_capacity_sat/e11_capacity_cache.pkl"))
    ap.add_argument("--perms", type=Path, default=Path("data/e11_quotient_action/e11_quotient_action_verification.perms.npz"))
    ap.add_argument("--subspace-orbits", type=Path, default=Path("data/e11_subspace_orbits/e11_subspace_orbits.npz"))
    ap.add_argument("--membership", type=Path, default=Path("data/e11_occupation_sat/e11_membership.npy"))
    ap.add_argument("--rank", type=int, default=19)
    ap.add_argument("--max-depth", type=int, default=6)
    ap.add_argument("--node-limit", type=int, default=50000, help="Maximum canonical non-root nodes to pop; 0 means no limit.")
    ap.add_argument("--record-limit", type=int, default=0, help="Maximum eliminated-prefix records to write; 0 writes all. Proof-use runs require 0 or a verified partitioned equivalent.")
    ap.add_argument("--self-test-size2", action="store_true")
    ap.add_argument("--leaf-xor", action="store_true", help="At depth=rank, immediately run native-XOR fixed-A SAT on occupation-feasible leaves.")
    ap.add_argument("--xor-timeout", type=int, default=120)
    ap.add_argument("--xor-threads", type=int, default=4)
    ap.add_argument("--outdir", type=Path, default=Path("data/e11_canonical_tree"))
    ap.add_argument("--name", default="pilot")
    args = ap.parse_args()

    t_all = time.time()
    cache = build_or_load_constraint_cache(args.lut, args.cache, args.rank, False)
    perms = load_perms(args.perms)
    canonical, canonical_parent = make_canonical_functions(perms)
    point_caps = point_caps_from_cache(cache)
    M = build_or_load_membership(cache, args.membership, False)
    caps = np.asarray(cache["caps"], dtype=np.int16)
    orbit_id = load_subspace_orbit_ids(args.subspace_orbits, len(caps))

    args.outdir.mkdir(parents=True, exist_ok=True)
    elim_path = args.outdir / f"{args.name}_eliminated_prefixes.jsonl"
    frontier_path = args.outdir / f"{args.name}_frontier.jsonl"
    leaf_path = args.outdir / f"{args.name}_occupation_feasible_leaves.jsonl"
    elim_f = elim_path.open("w")
    frontier_f = frontier_path.open("w")
    leaf_f = leaf_path.open("w")

    self_tests = []
    if args.self_test_size2:
        brute2 = brute_force_orbit_count_size2(point_caps, canonical)
        gen2 = generated_count_no_prune_size2(point_caps, canonical, canonical_parent)
        ok = brute2["orbit_representatives"] == gen2["level2_unique"] == gen2["level2"]
        self_tests.append({"name": "canonical_augmentation_size2", "brute": brute2, "generated": gen2, "ok": bool(ok)})
        if not ok:
            raise SystemExit(f"canonical augmentation size-2 self-test failed: {self_tests[-1]}")

    zero_occ = np.zeros(len(caps), dtype=np.int16)
    root: tuple[int, ...] = tuple()
    stack = [(root, np.zeros(256, dtype=np.int16), zero_occ)]
    stats = {
        "popped_by_depth": Counter(),
        "children_attempted_by_depth": Counter(),
        "skipped_point_cap_by_depth": Counter(),
        "skipped_noncanonical_by_depth": Counter(),
        "skipped_wrong_parent_by_depth": Counter(),
        "pruned_by_capacity_by_depth": Counter(),
        "pushed_by_depth": Counter(),
        "leaves_by_depth": Counter(),
    }
    violation_orbits = Counter()
    violation_dims = Counter()
    violation_caps = Counter()
    node_popped = 0
    accepted_nonroot_popped = 0
    pruned_count = 0
    leaf_count = 0
    fixed_tests = []
    witness = None
    exhausted = True
    max_frontier_size = 0

    while stack:
        max_frontier_size = max(max_frontier_size, len(stack))
        ms, counts, occ = stack.pop()
        depth = len(ms)
        stats["popped_by_depth"][depth] += 1
        node_popped += 1
        if depth > 0:
            accepted_nonroot_popped += 1
            if args.node_limit and accepted_nonroot_popped > args.node_limit:
                # Save this node and the remaining frontier for replay/resume and stop.
                frontier_f.write(json.dumps({"prefix": list(ms), "prefix_size": depth, "reason": "node_limit_stop_current"}, sort_keys=True) + "\n")
                for fms, _, _ in stack:
                    frontier_f.write(json.dumps({"prefix": list(fms), "prefix_size": len(fms), "reason": "node_limit_frontier"}, sort_keys=True) + "\n")
                exhausted = False
                break
        if depth == args.max_depth:
            leaf_count += 1
            stats["leaves_by_depth"][depth] += 1
            leaf_rec = {"multiset": list(ms), "size": depth, "canonical": True, "occupation_feasible_within_prefix": True}
            if args.leaf_xor and depth == args.rank:
                fixed = run_fixed_u_xor(ms, args.outdir / "fixed_u_xor", f"{args.name}_leaf{leaf_count:06d}", args.xor_timeout, args.xor_threads)
                leaf_rec["fixed_u_xor"] = fixed
                fixed_tests.append(fixed)
                if fixed.get("status") == "SAT" and fixed.get("decoded_verified") is True:
                    witness = fixed.get("json_path")
                    leaf_f.write(json.dumps(leaf_rec, sort_keys=True) + "\n")
                    exhausted = False
                    break
            leaf_f.write(json.dumps(leaf_rec, sort_keys=True) + "\n")
            continue

        # Generate children.  This broad loop is expensive but transparent and safe.
        for p in range(1, 256):
            stats["children_attempted_by_depth"][depth] += 1
            if counts[p] >= point_caps[p]:
                stats["skipped_point_cap_by_depth"][depth] += 1
                continue
            child = tuple(sorted(ms + (p,)))
            cchild = canonical(child)
            if cchild != child:
                stats["skipped_noncanonical_by_depth"][depth] += 1
                continue
            if canonical_parent(child) != ms:
                stats["skipped_wrong_parent_by_depth"][depth] += 1
                continue
            occ2 = occ + M[p].astype(np.int16)
            bad = first_violation(occ2, caps)
            if bad is not None:
                pruned_count += 1
                stats["pruned_by_capacity_by_depth"][len(child)] += 1
                violation_orbits[int(orbit_id[bad])] += 1
                violation_dims[int(cache["dims"][bad])] += 1
                violation_caps[int(cache["caps"][bad])] += 1
                if args.record_limit == 0 or pruned_count <= args.record_limit:
                    elim_f.write(json.dumps(violation_record(child, occ2, cache, orbit_id, bad, "prefix_occupation_exceeds_capacity"), sort_keys=True) + "\n")
                continue
            c2 = counts.copy(); c2[p] += 1
            stack.append((child, c2, occ2))
            stats["pushed_by_depth"][len(child)] += 1

    elim_f.close(); frontier_f.close(); leaf_f.close()
    for path in (elim_path, frontier_path, leaf_path):
        if path.exists() and path.stat().st_size == 0:
            # Keep empty files as evidence that no records of that kind were produced.
            pass

    def counter_to_dict(c: Counter) -> dict[str, int]:
        return {str(k): int(v) for k, v in sorted(c.items(), key=lambda kv: kv[0])}

    result = {
        "purpose": "canonical E11 A-multiset support tree with exact all-subspace Wang separation",
        "field": "F2",
        "rank_s": args.rank,
        "max_depth": args.max_depth,
        "node_limit": args.node_limit,
        "record_limit": args.record_limit,
        "exhausted_declared_tree": bool(exhausted and not witness and not stack),
        "stopped_by_node_limit_or_witness": not bool(exhausted and not witness and not stack),
        "witness": witness,
        "accepted_nonroot_nodes_popped": int(min(accepted_nonroot_popped, args.node_limit) if args.node_limit else accepted_nonroot_popped),
        "raw_popped_including_root": int(node_popped),
        "max_frontier_size": int(max_frontier_size),
        "pruned_prefix_count": int(pruned_count),
        "occupation_feasible_leaf_count_at_max_depth": int(leaf_count),
        "stats": {k: counter_to_dict(v) for k, v in stats.items()},
        "violation_orbit_id_counts_head": dict(list(counter_to_dict(violation_orbits).items())[:50]),
        "violation_dim_counts": counter_to_dict(violation_dims),
        "violation_cap_counts": counter_to_dict(violation_caps),
        "self_tests": self_tests,
        "files": {
            "eliminated_prefixes_jsonl": str(elim_path),
            "frontier_jsonl": str(frontier_path),
            "occupation_feasible_leaves_jsonl": str(leaf_path),
            "cache": str(args.cache),
            "perms": str(args.perms),
            "subspace_orbits": str(args.subspace_orbits),
            "membership": str(args.membership),
        },
        "meaning": "Proof interpretation is two-stage. If max_depth=19, node_limit=0, record_limit=0 (or a verified partitioned equivalent), exhausted_declared_tree is true, and occupation_feasible_leaf_count_at_max_depth=0, the tree is a replayable Wang-occupation infeasibility certificate. If depth-19 leaves survive, Wang occupation alone has not excluded them and each surviving canonical support still needs fixed-A CPD exclusion or a witness test. Node-limited or shallower runs are calibrated search-state evidence only.",
        "elapsed_sec": time.time() - t_all,
    }
    out = args.outdir / f"{args.name}_summary.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "max_depth": args.max_depth,
        "node_limit": args.node_limit,
        "exhausted_declared_tree": result["exhausted_declared_tree"],
        "accepted_nonroot_nodes_popped": result["accepted_nonroot_nodes_popped"],
        "pruned_prefix_count": pruned_count,
        "occupation_feasible_leaf_count_at_max_depth": leaf_count,
        "witness": witness,
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True))
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
