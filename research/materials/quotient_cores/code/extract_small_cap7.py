#!/usr/bin/env python3
"""Extract first N rows from E11WANG1 binary for targeted pair generation."""
import struct, hashlib, sys
from pathlib import Path

def extract_first_n(inpath, outpath, n):
    data = Path(inpath).read_bytes()
    assert data[:8] == b'E11WANG1'
    total = struct.unpack_from('<I', data, 8)[0]
    take = min(n, total)
    out = bytearray(b'E11WANG1' + struct.pack('<I', take))
    out += data[12:12+take*36]
    Path(outpath).write_bytes(bytes(out))
    sha = hashlib.sha256(bytes(out)).hexdigest()
    print(f"  Extracted {take}/{total} rows -> {outpath} SHA256={sha[:16]}")
    return take, sha

if __name__ == '__main__':
    outdir = Path("data/quotient_dfs")
    for label, path in [
        ("rank2", "data/quotient_dfs/rank2_cap7_n19.bin"),
        ("rank3", "data/quotient_dfs/rank3_cap7_n19.bin"),
    ]:
        for n in [32, 100]:
            extract_first_n(path, str(outdir / f"{label}_cap7_first{n}.bin"), n)
