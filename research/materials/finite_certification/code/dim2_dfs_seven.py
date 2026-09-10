#!/usr/bin/env python3
"""Run safe-DFS for the 7 dim-2 orbits where max line cap = 1.

For these orbits, the distinct-support DFS is a valid proof of infeasibility.
We write the WANG512 binary and run the DFS with an exclusion list for
points 128-511 (outside the 127-point quotient domain).

Orbit 489 is skipped (max_cap = 2, DFS invalid).
"""
from __future__ import annotations
import json, pickle, struct, subprocess, sys, time
from pathlib import Path

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from node_local_occupation_closure import (
    rref_basis, pack_basis, free_bits_from_rref, lift_q,
    node_constraints
)

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
CACHE_PATH = Path("data/wang_f2_lb20/wang_orbit_closed_cache.pkl")
DFS_BIN = Path("scripts/wang_domain_dfs_safe")
OUTDIR = Path("data/dfs_certificates")


def write_wang512(rows_caps, outpath, npts=127):
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
            dim = bin(mask).count("1").bit_length()
            f.write(struct.pack("<BBH", int(cap), dim, 0))
            for w in words:
                f.write(struct.pack("<Q", w))


def main():
    with LUT_PATH.open("rb") as f:
        data = pickle.load(f)
    lut = data["lut"] if isinstance(data, dict) and "lut" in data else data
    with CACHE_PATH.open("rb") as f:
        cache = pickle.load(f)
    orbits = cache["orbits"]
    OUTDIR.mkdir(parents=True, exist_ok=True)

    # Build exclusion file (points 128-511)
    exclude_file = OUTDIR / "exclude_128_511.txt"
    exclude_pts = ",".join(str(p) for p in range(128, 512))
    exclude_file.write_text(exclude_pts)

    indices = [484, 485, 486, 487, 488, 490, 491]  # skip 489
    results = []

    for idx in indices:
        orb = next(o for o in orbits if o["cert_index"] == idx)
        W_basis = orb["basis"]
        W = rref_basis(W_basis, 9)
        k = 9 - len(W)
        L = orb["raw_lb"]
        npts = (1 << k) - 1

        rows, meta = node_constraints(W, lut, L)
        node_dir = OUTDIR / f"orbit_{idx}"
        node_dir.mkdir(parents=True, exist_ok=True)

        bin_path = node_dir / f"orbit_{idx}.bin"
        write_wang512(rows, bin_path, npts)

        # Run DFS with exclusion and output
        out_path = node_dir / "dfs_output.json"
        cmd = [
            str(DFS_BIN),
            "--constraints", str(bin_path),
            "--target", str(L),
            "--timeout", "600",
            "--output", str(out_path),
            "--exclude", exclude_pts,
        ]
        print(f"\n=== Orbit {idx}: W={W}, L={L}, npts={npts} ===")
        t0 = time.time()
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=660)
        elapsed = time.time() - t0

        # Parse JSON output
        dfs_json = None
        if out_path.exists():
            try:
                dfs_json = json.loads(out_path.read_text().strip())
            except json.JSONDecodeError:
                pass
        elif proc.stdout.strip():
            try:
                dfs_json = json.loads(proc.stdout.strip().split("\n")[0])
            except json.JSONDecodeError:
                pass

        if dfs_json:
            rec = {
                "cert_index": idx,
                "target": L,
                "n_rows": len(rows),
                "complete": dfs_json.get("complete", False),
                "solutions": dfs_json.get("solutions", None),
                "dfs_calls": dfs_json.get("dfs_calls", None),
                "max_depth": dfs_json.get("max_depth", None),
                "domain_after_forbid": dfs_json.get("initial_domain_after_forbid", None),
                "domain_after_cap0": dfs_json.get("initial_domain_after_cap0", None),
                "elapsed_sec": elapsed,
                "returncode": proc.returncode,
            }
        else:
            rec = {
                "cert_index": idx,
                "returncode": proc.returncode,
                "stderr": proc.stderr[:500],
                "elapsed_sec": elapsed,
            }

        results.append(rec)
        print(f"  {json.dumps({k:v for k,v in rec.items()}, indent=2)}")

    summary = {
        "schema": "dfs_certificates_v1",
        "indices": indices,
        "skipped_489": True,
        "results": results,
        "all_complete_zero": all(
            r.get("complete") and r.get("solutions") == 0
            for r in results
        ),
    }
    out = OUTDIR / "dfs_summary.json"
    out.write_text(json.dumps(summary, indent=2) + "\n")
    print(f"\nAll complete with 0 solutions: {summary['all_complete_zero']}")
    print(f"-> {out}")


if __name__ == "__main__":
    main()
