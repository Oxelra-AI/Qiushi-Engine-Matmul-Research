#!/usr/bin/env python3
"""analysis: extract specific cap-7 Wang rows violated by relaxation supports.

Exports them in E11WANG1 format for use as pair-inequality sources.
Also exports all cap-7 rows (dim 5 and 6) for broader pair generation.
"""
import json, struct, sys
from pathlib import Path

def load_full_binary(path):
    """Load E11WANG1 binary and return list of (cap, dim, word_bytes)."""
    data = Path(path).read_bytes()
    assert data[:8] == b'E11WANG1'
    n = struct.unpack_from('<I', data, 8)[0]
    rows = []
    off = 12
    for _ in range(n):
        cap = data[off]; dim = data[off+1]; reserved = struct.unpack_from('<H', data, off+2)[0]
        words = data[off+4:off+36]
        rows.append((cap, dim, reserved, words))
        off += 36
    return rows

def write_wang_binary(path, selected_rows):
    """Write selected rows in E11WANG1 format."""
    out = bytearray(b'E11WANG1')
    out += struct.pack('<I', len(selected_rows))
    for (cap, dim, reserved, words) in selected_rows:
        out += struct.pack('<B', cap)
        out += struct.pack('<B', dim)
        out += struct.pack('<H', reserved)
        out += words
    Path(path).write_bytes(bytes(out))

def main():
    import hashlib
    full_path = "data/domain_dfs_soundness/e11_wang_cap16_rebuilt.bin"
    rows = load_full_binary(full_path)
    print(f"Loaded {len(rows)} rows from full table")
    
    # Rescan-identified violating row indices
    rescan = json.loads(Path("data/domain_dfs_soundness/rescan_branch0_cover512_solutions_head.json").read_text())
    viol_indices = set()
    for rec in rescan['records']:
        for v in rec['first_wang_violations']:
            viol_indices.add(v['row_index'])
    viol_indices = sorted(viol_indices)
    
    # Extract violating rows
    viol_rows = [rows[i] for i in viol_indices]
    outdir = Path("data/domain_dfs_soundness")
    
    viol_path = outdir / "e11_wang_cap7_violated31.bin"
    write_wang_binary(str(viol_path), viol_rows)
    sha = hashlib.sha256(viol_path.read_bytes()).hexdigest()
    print(f"Wrote {len(viol_rows)} violating rows to {viol_path}")
    print(f"  SHA256: {sha}")
    
    # Also extract ALL cap-7 rows for broader pair generation
    cap7_rows = [(c,d,r,w) for (c,d,r,w) in rows if c == 7]
    cap7_path = outdir / "e11_wang_cap7_all.bin"
    write_wang_binary(str(cap7_path), cap7_rows)
    sha7 = hashlib.sha256(cap7_path.read_bytes()).hexdigest()
    print(f"Wrote {len(cap7_rows)} cap-7 rows to {cap7_path}")
    print(f"  SHA256: {sha7}")
    
    # Extract cap-7 dim-5 and dim-6 separately for analysis
    d5 = [(c,d,r,w) for (c,d,r,w) in cap7_rows if d == 5]
    d6 = [(c,d,r,w) for (c,d,r,w) in cap7_rows if d == 6]
    print(f"  dim-5: {len(d5)}, dim-6: {len(d6)}")
    
    # Save manifest
    manifest = {
        'schema': 's0908_extract_cap7_v1',
        'violated31_path': str(viol_path),
        'violated31_count': len(viol_rows),
        'violated31_sha256': hashlib.sha256(viol_path.read_bytes()).hexdigest(),
        'violated31_indices': viol_indices,
        'cap7_all_path': str(cap7_path),
        'cap7_all_count': len(cap7_rows),
        'cap7_all_sha256': sha7,
        'cap7_dim5_count': len(d5),
        'cap7_dim6_count': len(d6),
    }
    mpath = outdir / "cap7_extract_manifest.json"
    mpath.write_text(json.dumps(manifest, indent=2) + '\n')
    print(f"Manifest: {mpath}")
    print(json.dumps(manifest, indent=2))

if __name__ == '__main__':
    main()
