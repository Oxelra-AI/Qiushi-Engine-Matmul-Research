#!/usr/bin/env python3
"""analysis: Merge existing quotient cap<=5 rows with new DC-lift rows.

Creates a single E11WANG1 binary for DFS with both original quotient rows
and the new lift-derived occupation constraints.
"""
import struct, hashlib, json
from pathlib import Path

ROOT = Path('research/research_record')
OUTDIR = ROOT / 'workspace/data/quotient_lift'

def sha256_file(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for c in iter(lambda: f.read(1<<20), b''): h.update(c)
    return h.hexdigest()

def read_wang_binary(path):
    """Read E11WANG1 binary, return list of (cap, dim, mask_bytes)."""
    rows = []
    with open(path, 'rb') as f:
        magic = f.read(8)
        assert magic == b'E11WANG1', f"Bad magic in {path}: {magic}"
        n = struct.unpack('<I', f.read(4))[0]
        for _ in range(n):
            hdr = f.read(4)
            mask = f.read(32)
            rows.append((hdr, mask))
    return rows

def merge_and_write(quotient_path, lift_path, out_path):
    """Merge two E11WANG1 binaries, deduplicating by mask."""
    q_rows = read_wang_binary(quotient_path)
    l_rows = read_wang_binary(lift_path)
    
    # Deduplicate: keep the tighter (smaller cap) for each mask
    by_mask = {}
    for hdr, mask in q_rows:
        cap = hdr[0]
        if mask not in by_mask or cap < by_mask[mask][0]:
            by_mask[mask] = (cap, hdr, mask)
    
    added = 0
    tightened = 0
    for hdr, mask in l_rows:
        cap = hdr[0]
        if mask not in by_mask:
            by_mask[mask] = (cap, hdr, mask)
            added += 1
        elif cap < by_mask[mask][0]:
            by_mask[mask] = (cap, hdr, mask)
            tightened += 1
    
    # Sort by cap, then mask
    all_rows = sorted(by_mask.values(), key=lambda r: (r[0], r[2]))
    
    # Write
    data = bytearray()
    data.extend(b'E11WANG1')
    data.extend(struct.pack('<I', len(all_rows)))
    for cap, hdr, mask in all_rows:
        data.extend(hdr)
        data.extend(mask)
    
    out_bytes = bytes(data)
    Path(out_path).write_bytes(out_bytes)
    sha = hashlib.sha256(out_bytes).hexdigest()
    
    return {
        'quotient_rows': len(q_rows),
        'lift_rows': len(l_rows),
        'merged_total': len(all_rows),
        'new_added': added,
        'tightened': tightened,
        'output_path': str(out_path),
        'sha256': sha,
    }

def main():
    results = {'schema': 's0908_merged_quotient_v1'}
    
    for pname, pivot in [('rank2', 17), ('rank3', 273)]:
        print(f"\n=== {pname} ===")
        
        if pivot == 17:
            q_path = ROOT / 'workspace/data/quotient_dfs/rank2_cap5_n19.bin'
        else:
            q_path = ROOT / 'workspace/data/quotient_dfs/rank3_cap5_n19.bin'
        
        l_path = OUTDIR / f'{pname}_dc_lift_rows.bin'
        o_path = OUTDIR / f'{pname}_merged_cap5_n19.bin'
        
        info = merge_and_write(q_path, l_path, o_path)
        results[pname] = info
        
        print(f"  Quotient rows: {info['quotient_rows']}")
        print(f"  Lift rows: {info['lift_rows']}")
        print(f"  New added: {info['new_added']}")
        print(f"  Tightened: {info['tightened']}")
        print(f"  Merged total: {info['merged_total']}")
        print(f"  SHA256: {info['sha256']}")
    
    out_path = OUTDIR / 'merged_quotient_manifest.json'
    out_path.write_text(json.dumps(results, indent=2) + '\n')
    print(f"\nSaved manifest to {out_path}")

if __name__ == '__main__':
    main()
