#!/usr/bin/env python3
"""analysis: filter quotient Wang binaries to cap<=K for DFS saturation constraints.
Also extract cap-7 rows for pair-inequality generation."""
import struct, sys, hashlib, json, os
from pathlib import Path

MAGIC = b"E11WANG1"

def filter_binary(inpath, outpath, max_cap):
    data = Path(inpath).read_bytes()
    assert data[:8] == MAGIC
    n = struct.unpack_from('<I', data, 8)[0]
    out = bytearray(MAGIC + struct.pack('<I', 0))  # placeholder count
    kept = 0
    cap_hist = {}
    off = 12
    for i in range(n):
        cap = data[off]
        if cap <= max_cap:
            out += data[off:off+36]
            kept += 1
            cap_hist[cap] = cap_hist.get(cap, 0) + 1
        off += 36
    # Fix count
    struct.pack_into('<I', out, 8, kept)
    Path(outpath).write_bytes(bytes(out))
    sha = hashlib.sha256(bytes(out)).hexdigest()
    return kept, sha, cap_hist

def main():
    outdir = Path("data/quotient_dfs")
    outdir.mkdir(parents=True, exist_ok=True)
    
    configs = [
        ("rank2", "data/wang_native/quotient_binaries/rank2_all_n19.bin", 17),
        ("rank3", "data/wang_native/quotient_binaries/rank3_all_n19.bin", 273),
    ]
    
    manifest = {'schema': 's0908_quotient_filter_v1', 'outputs': []}
    
    for label, inpath, pivot in configs:
        for max_cap in [5, 10]:
            outname = f"{label}_cap{max_cap}_n19.bin"
            outpath = outdir / outname
            kept, sha, cap_hist = filter_binary(inpath, str(outpath), max_cap)
            rec = {
                'label': label, 'pivot': pivot, 'max_cap': max_cap,
                'rows': kept, 'sha256': sha, 'cap_hist': cap_hist,
                'path': str(outpath),
            }
            manifest['outputs'].append(rec)
            print(f"{label} cap<={max_cap}: {kept} rows, SHA256={sha[:16]}...")
    
    # Also extract cap-7 rows for pair inequality generation
    for label, inpath, pivot in configs:
        data = Path(inpath).read_bytes()
        n = struct.unpack_from('<I', data, 8)[0]
        out = bytearray(MAGIC + struct.pack('<I', 0))
        kept = 0
        off = 12
        for i in range(n):
            cap = data[off]
            if cap == 7:
                out += data[off:off+36]
                kept += 1
            off += 36
        struct.pack_into('<I', out, 8, kept)
        outname = f"{label}_cap7_n19.bin"
        outpath = outdir / outname
        Path(outpath).write_bytes(bytes(out))
        sha = hashlib.sha256(bytes(out)).hexdigest()
        rec = {'label': label, 'pivot': pivot, 'cap': 7, 'rows': kept, 'sha256': sha, 'path': str(outpath)}
        manifest['outputs'].append(rec)
        print(f"{label} cap=7: {kept} rows, SHA256={sha[:16]}...")
    
    mpath = outdir / "quotient_filter_manifest.json"
    mpath.write_text(json.dumps(manifest, indent=2) + '\n')
    print(f"\nManifest: {mpath}")
    print(json.dumps(manifest, indent=2))

if __name__ == '__main__':
    main()
