#!/usr/bin/env python3
"""analysis: rebuild E11 quotient Wang upper-bound rows in the native binary format.

Input is the canonical Wang LUT from research_record. Output is a this investigation binary
file with rows cap19<=max_cap, plus hashes for comparison with the peer file.
"""
from __future__ import annotations
import argparse, hashlib, json, struct, sys, time
from collections import Counter
from pathlib import Path

S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import rref_basis, unpack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
OUTDIR = Path("data/domain_dfs_soundness")
MASK9 = (1 << 9) - 1
N = 19
MAGIC = b"E11WANG1"


def contains_e11(key: int) -> bool:
    d = key & 0xF
    return d > 0 and (((key >> (4 + 9 * (d - 1))) & MASK9) == 1)


def key9_to_basis8(key9: int):
    raw = []
    for b in unpack_basis(key9):
        if b == 1:
            continue
        q = int(b)
        if q & 1:
            q ^= 1
        q8 = 0
        for bit in range(1, 9):
            if (q >> bit) & 1:
                q8 |= 1 << (bit - 1)
        if q8:
            raw.append(q8)
    return tuple(rref_basis(raw, n=8)) if raw else tuple()


def words_from_basis8(basis8):
    words = [0, 0, 0, 0]
    for m in range(1, 1 << len(basis8)):
        v = 0
        for i, b in enumerate(basis8):
            if (m >> i) & 1:
                v ^= b
        if v:
            words[v >> 6] |= 1 << (v & 63)
    return tuple(words)


def pack_rows(rows):
    blob = bytearray()
    blob.extend(MAGIC)
    blob.extend(struct.pack("<I", len(rows)))
    for cap, dim8, words in rows:
        blob.extend(struct.pack("<BBHQQQQ", int(cap), int(dim8), 0, *[int(w) for w in words]))
    return bytes(blob)


def sha_file(path: Path) -> str | None:
    if not path.exists():
        return None
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-cap", type=int, default=5)
    ap.add_argument("--outdir", type=Path, default=OUTDIR)
    ap.add_argument("--peer", type=Path, default=Path("data/wang_native/e11_wang_cap5.bin"))
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    lut, _ = load_lut(LUT_PATH)
    rows = []
    cap_hist_all = Counter(); dim_hist_all = Counter(); lb_hist_all = Counter()
    all_e11 = 0
    for key9, lb0 in lut.items():
        key9 = int(key9); lb = int(lb0)
        if not contains_e11(key9):
            continue
        all_e11 += 1
        cap = N - lb
        dim8 = (key9 & 0xF) - 1
        cap_hist_all[cap] += 1; dim_hist_all[dim8] += 1; lb_hist_all[lb] += 1
        if 0 <= cap <= args.max_cap and cap < N:
            basis8 = key9_to_basis8(key9)
            rows.append((cap, len(basis8), words_from_basis8(basis8)))
    blob = pack_rows(rows)
    bin_path = args.outdir / f"e11_wang_cap{args.max_cap}_rebuilt.bin"
    bin_path.write_bytes(blob)
    meta = {
        "schema": "s0908_rebuilt_e11_wang_cap_v1",
        "status": "ok",
        "source_lut": str(LUT_PATH),
        "max_cap": args.max_cap,
        "all_e11_rows": all_e11,
        "row_count_written": len(rows),
        "cap19_hist_all_e11": dict(sorted((int(k), int(v)) for k, v in cap_hist_all.items())),
        "dim8_hist_all_e11": dict(sorted((int(k), int(v)) for k, v in dim_hist_all.items())),
        "lb_hist_all_e11": dict(sorted((int(k), int(v)) for k, v in lb_hist_all.items())),
        "binary_path": str(bin_path),
        "binary_sha256": hashlib.sha256(blob).hexdigest(),
        "peer_binary_path": str(args.peer),
        "peer_binary_sha256": sha_file(args.peer),
        "matches_peer_binary": sha_file(args.peer) == hashlib.sha256(blob).hexdigest(),
        "elapsed_sec": time.time() - t0,
    }
    meta_path = args.outdir / f"e11_wang_cap{args.max_cap}_rebuilt.meta.json"
    meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n")
    print(json.dumps(meta, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
