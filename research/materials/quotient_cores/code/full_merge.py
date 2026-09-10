#!/usr/bin/env python3
"""analysis: Create fully merged binary with ALL constraint types.

Sources:
1. Original quotient cap<=5 rows
2. DC-lift rows (graph family double-counting)
3. Q-containing lift rows (tighter caps from full tensor through q)

Deduplicates by mask, keeping tightest cap.
"""
import struct, hashlib, json
from pathlib import Path

ROOT = Path('research/research_record')
OUTDIR = ROOT / 'workspace/data/quotient_lift'

def read_wang(path):
    rows = {}  # mask_bytes -> (cap, dim, mask_bytes)
    with open(path, 'rb') as f:
        magic = f.read(8); assert magic == b'E11WANG1', f"Bad magic in {path}"
        n = struct.unpack('<I', f.read(4))[0]
        for _ in range(n):
            hdr = f.read(4); mask = f.read(32)
            cap = hdr[0]
            if mask not in rows or cap < rows[mask][0]:
                rows[mask] = (cap, hdr, mask)
    return rows

def main():
    results = {'schema': 's0908_full_merged_v1'}
    
    for pname in ['rank2', 'rank3']:
        print(f"\n=== {pname} ===")
        
        if pname == 'rank2':
            q_path = ROOT / 'workspace/data/quotient_dfs/rank2_cap5_n19.bin'
        else:
            q_path = ROOT / 'workspace/data/quotient_dfs/rank3_cap5_n19.bin'
        
        dc_path = OUTDIR / f'{pname}_dc_lift_rows.bin'
        qc_path = OUTDIR / f'{pname}_qcontaining_lift_rows.bin'
        
        # Read all sources
        q_rows = read_wang(q_path)
        dc_rows = read_wang(dc_path)
        qc_rows = read_wang(qc_path)
        
        print(f"  Quotient rows: {len(q_rows)}")
        print(f"  DC-lift rows: {len(dc_rows)}")
        print(f"  Q-containing rows: {len(qc_rows)}")
        
        # Merge: keep tightest cap per mask
        merged = dict(q_rows)
        added_dc = 0; tightened_dc = 0
        for mask, (cap, hdr, m) in dc_rows.items():
            if mask not in merged:
                merged[mask] = (cap, hdr, m); added_dc += 1
            elif cap < merged[mask][0]:
                merged[mask] = (cap, hdr, m); tightened_dc += 1
        
        added_qc = 0; tightened_qc = 0
        for mask, (cap, hdr, m) in qc_rows.items():
            if mask not in merged:
                merged[mask] = (cap, hdr, m); added_qc += 1
            elif cap < merged[mask][0]:
                merged[mask] = (cap, hdr, m); tightened_qc += 1
        
        print(f"  DC added: {added_dc}, tightened: {tightened_dc}")
        print(f"  QC added: {added_qc}, tightened: {tightened_qc}")
        print(f"  Merged total: {len(merged)}")
        
        # Cap histogram
        from collections import Counter
        cap_hist = Counter(v[0] for v in merged.values())
        print(f"  Cap histogram: {dict(sorted(cap_hist.items()))}")
        
        # Write binary
        all_rows = sorted(merged.values(), key=lambda r: (r[0], r[2]))
        out_path = OUTDIR / f'{pname}_full_merged_n19.bin'
        data = bytearray()
        data.extend(b'E11WANG1')
        data.extend(struct.pack('<I', len(all_rows)))
        for cap, hdr, mask in all_rows:
            data.extend(hdr); data.extend(mask)
        
        out_bytes = bytes(data)
        out_path.write_bytes(out_bytes)
        sha = hashlib.sha256(out_bytes).hexdigest()
        print(f"  Written: {out_path}, SHA256={sha}")
        
        results[pname] = {
            'quotient_rows': len(q_rows),
            'dc_rows': len(dc_rows),
            'qc_rows': len(qc_rows),
            'added_dc': added_dc,
            'tightened_dc': tightened_dc,
            'added_qc': added_qc,
            'tightened_qc': tightened_qc,
            'merged_total': len(merged),
            'cap_hist': {str(k): v for k, v in sorted(cap_hist.items())},
            'path': str(out_path),
            'sha256': sha,
        }
    
    out = OUTDIR / 'full_merged_manifest.json'
    out.write_text(json.dumps(results, indent=2) + '\n')
    print(f"\nManifest: {out}")

if __name__ == '__main__':
    main()
