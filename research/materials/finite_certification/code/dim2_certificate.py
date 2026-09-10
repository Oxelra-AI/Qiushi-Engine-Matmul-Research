#!/usr/bin/env python3
"""Generate proof-grade certificates for the eight dim-2 occupation raises.

For orbits 484-488, 490, 491: all line caps are 0 or 1, so distinct-support
DFS (via wang_domain_dfs_safe) is valid and its complete enumeration is
a certificate.

For orbit 489: one line has cap=2, so distinct-support DFS is insufficient.
We build an integer-multiplicity PB model and solve with CP-SAT, recording
the complete constraint system and infeasibility result.

Each certificate consists of:
  - The RREF basis of the node W
  - The list of quotient constraint rows (mask, cap) from strict super-subspaces
  - The target support size L
  - For DFS nodes: the complete DFS summary with zero solutions
  - For non-DFS (orbit 489): the integer model and solver status
"""
from __future__ import annotations
import argparse, json, os, pickle, subprocess, struct, sys, time
from pathlib import Path
from collections import Counter

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from node_local_occupation_closure import (
    rref_basis, pack_basis, free_bits_from_rref, lift_q,
    strict_nonzero_proper_subspaces, mask_from_qbasis, node_constraints,
    solve_local_cp
)

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
CACHE_PATH = Path("data/wang_f2_lb20/wang_orbit_closed_cache.pkl")
DFS_BIN = Path("scripts/wang_domain_dfs_safe")
OUTDIR = Path("data/dim2_certificates")


def popcount_int(x: int) -> int:
    return bin(x).count("1")


def write_wang512_binary(rows_caps, outpath: Path, npts: int = 127):
    """Write a WANG512 binary for quotient occupations on 2^k - 1 points.

    DFS binary format per row: cap(1B) + dim(1B) + reserved(2B) + 8×uint64(64B) = 68 bytes.
    Points are 1-indexed: point p corresponds to bit (p-1) in the mask words.
    For k=7 quotient, points are 1..127 and only words 0,1 are nonzero.
    """
    MAGIC = b"WANG512\x01"
    nrows = len(rows_caps)
    with outpath.open("wb") as f:
        f.write(MAGIC)
        f.write(struct.pack("<I", nrows))
        for mask, cap in rows_caps:
            words = [0] * 8
            for p in range(1, npts + 1):
                if (mask >> (p - 1)) & 1:
                    w = (p - 1) // 64
                    b = (p - 1) % 64
                    words[w] |= 1 << b
            # Estimate dimension from popcount of mask
            dim = popcount_int(mask).bit_length()  # rough estimate
            f.write(struct.pack("<BBH", int(cap), dim, 0))
            for w in words:
                f.write(struct.pack("<Q", w))
    return outpath


def run_dfs(binary_path: Path, target: int, npts: int, timeout: int = 600) -> dict:
    """Run wang_domain_dfs_safe on a quotient binary.

    Exclude points npts+1..511 to restrict the DFS to the quotient domain.
    """
    # Build exclusion list: points outside the quotient domain
    exclude_pts = ",".join(str(p) for p in range(npts + 1, 512))
    cmd = [
        str(DFS_BIN),
        "--constraints", str(binary_path),
        "--target", str(target),
        "--timeout", str(timeout),
        "--exclude", exclude_pts,
    ]
    t0 = time.time()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 30)
        elapsed = time.time() - t0
        return {
            "command": cmd,
            "returncode": proc.returncode,
            "stdout": proc.stdout[-2000:] if proc.stdout else "",
            "stderr": proc.stderr[-2000:] if proc.stderr else "",
            "elapsed_sec": elapsed,
        }
    except subprocess.TimeoutExpired:
        return {
            "command": cmd,
            "returncode": None,
            "stdout": "",
            "stderr": "timeout",
            "elapsed_sec": time.time() - t0,
        }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--indices", default="484,485,486,487,488,489,490,491")
    ap.add_argument("--dfs-timeout", type=int, default=600)
    ap.add_argument("--cpsat-timeout", type=float, default=900.0)
    args = ap.parse_args()

    indices = [int(x) for x in args.indices.split(",")]

    with LUT_PATH.open("rb") as f:
        data = pickle.load(f)
    lut = data["lut"] if isinstance(data, dict) and "lut" in data else data
    with CACHE_PATH.open("rb") as f:
        cache = pickle.load(f)
    orbits = cache["orbits"]
    OUTDIR.mkdir(parents=True, exist_ok=True)

    results = []
    for idx in indices:
        orb = next(o for o in orbits if o["cert_index"] == idx)
        W_basis = orb["basis"]
        W = rref_basis(W_basis, 9)
        d = len(W)
        k = 9 - d
        L = orb["raw_lb"]  # 18
        free = free_bits_from_rref(W, 9)
        npts = (1 << k) - 1

        print(f"\n=== Orbit {idx}: W={W}, d={d}, k={k}, L={L}, npts={npts} ===")

        # Build constraint rows
        rows, meta = node_constraints(W, lut, L)
        # Check line caps
        max_cap = 0
        cap2_directions = []
        for q in range(1, 1 << k):
            v = lift_q(q, free)
            U = rref_basis((*W, v), 9)
            key = pack_basis(U)
            lb_U = lut.get(key)
            if lb_U is not None:
                cap = L - lb_U
                if cap > max_cap:
                    max_cap = cap
                if cap > 1:
                    cap2_directions.append({"q": q, "v": v, "cap": cap, "lb_U": lb_U})

        distinct_valid = (max_cap <= 1)
        node_dir = OUTDIR / f"orbit_{idx}"
        node_dir.mkdir(parents=True, exist_ok=True)

        # Save constraint system
        constraint_file = node_dir / "constraints.json"
        constraint_file.write_text(json.dumps({
            "cert_index": idx,
            "W_basis": list(W_basis),
            "W_rref": list(W),
            "dim": d,
            "quotient_dim": k,
            "target_L": L,
            "n_quotient_directions": npts,
            "max_line_cap": max_cap,
            "cap2_directions": cap2_directions,
            "distinct_valid": distinct_valid,
            "n_constraint_rows": len(rows),
            "constraint_meta": meta,
            "rows": [{"mask": m, "cap": c} for m, c in rows],
        }, indent=2) + "\n")

        if distinct_valid:
            # Build WANG512 binary and run safe-DFS
            bin_path = node_dir / f"orbit_{idx}_quotient.bin"
            write_wang512_binary(rows, bin_path, npts)
            print(f"  DFS mode: {len(rows)} rows, binary={bin_path}")
            dfs_result = run_dfs(bin_path, L, npts, args.dfs_timeout)
            (node_dir / "dfs_result.json").write_text(json.dumps(dfs_result, indent=2) + "\n")

            # Parse DFS JSON output
            dfs_json = None
            try:
                dfs_json = json.loads(dfs_result.get("stdout", "").strip().split("\n")[0])
            except (json.JSONDecodeError, IndexError):
                pass

            if dfs_json:
                solutions = dfs_json.get("solutions", None)
                complete = dfs_json.get("complete", False)
                dfs_domain = dfs_json.get("initial_domain_after_forbid", None)
                dfs_domain_cap0 = dfs_json.get("initial_domain_after_cap0", None)
                dfs_calls = dfs_json.get("dfs_calls", None)
            else:
                solutions = None
                complete = False
                dfs_domain = None
                dfs_domain_cap0 = None
                dfs_calls = None

            rec = {
                "cert_index": idx,
                "method": "safe_dfs_distinct",
                "distinct_valid": True,
                "target": L,
                "n_rows": len(rows),
                "max_line_cap": max_cap,
                "dfs_returncode": dfs_result["returncode"],
                "dfs_solutions": solutions,
                "dfs_complete": complete,
                "dfs_domain_after_forbid": dfs_domain,
                "dfs_domain_after_cap0": dfs_domain_cap0,
                "dfs_calls": dfs_calls,
                "dfs_elapsed_sec": dfs_result["elapsed_sec"],
            }
        else:
            # Orbit 489: use CP-SAT with integer multiplicities
            print(f"  CPSAT mode (cap>1): {len(rows)} rows, cap2={cap2_directions}")
            sol = solve_local_cp(k, L, rows, args.cpsat_timeout, 8)
            (node_dir / "cpsat_result.json").write_text(json.dumps(sol, indent=2) + "\n")
            rec = {
                "cert_index": idx,
                "method": "cpsat_integer",
                "distinct_valid": False,
                "cap2_directions": cap2_directions,
                "target": L,
                "n_rows": len(rows),
                "max_line_cap": max_cap,
                "cpsat_status": sol.get("status"),
                "cpsat_feasible": sol.get("feasible"),
                "cpsat_elapsed_sec": sol.get("elapsed_sec"),
            }

        results.append(rec)
        print(f"  Result: {json.dumps({k: v for k, v in rec.items() if k != 'dfs_stdout_tail'}, indent=2)}")

    summary = {
        "schema": "dim2_certificates_v1",
        "indices": indices,
        "results": results,
        "all_infeasible": all(
            (r.get("dfs_solutions") == 0 and r.get("dfs_complete", False))
            or r.get("cpsat_feasible") == False
            for r in results
        ),
    }
    out_path = OUTDIR / "certificate_summary.json"
    out_path.write_text(json.dumps(summary, indent=2) + "\n")
    print(f"\nSummary -> {out_path}")
    print(json.dumps({k: v for k, v in summary.items() if k != "results"}, indent=2))


if __name__ == "__main__":
    main()
