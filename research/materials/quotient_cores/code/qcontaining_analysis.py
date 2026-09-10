#!/usr/bin/env python3
"""analysis: Extract q-containing full-tensor constraints as additional quotient rows.

For full-tensor rows W containing q:
  Occupation = 1 + |S ∩ π(W)|  (since both lifts of each quotient point are in W)
  Constraint: |S ∩ π(W)| ≤ cap20(W) - 1

These may be strictly tighter than the quotient's own cap for π(W).
"""
from __future__ import annotations
import json, struct, time, hashlib
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path('research/research_record')
WANG512 = Path('data/wang_native/full_tensor/full_wang512_cap5_len20_all_dim3.bin')
OUTDIR = ROOT / 'workspace/data/quotient_lift'

PIVOTS = {'rank2': 17, 'rank3': 273}

def lift0(p, pivot):
    h = (pivot & -pivot).bit_length() - 1
    low = p & ((1 << h) - 1)
    high = (p >> h) << (h + 1)
    return low | high

def sha256(data):
    return hashlib.sha256(data).hexdigest()

def main():
    t0 = time.time()
    results = {'schema': 's0908_qcontaining_constraints_v1'}
    
    for pname, pivot in PIVOTS.items():
        print(f"\n=== {pname} (pivot={pivot}) ===")
        lifts = [(p, lift0(p, pivot), lift0(p, pivot) ^ pivot) for p in range(1, 256)]
        
        # Load quotient caps
        if pivot == 17:
            qbin = ROOT / 'workspace/data/quotient_dfs/rank2_cap5_n19.bin'
        else:
            qbin = ROOT / 'workspace/data/quotient_dfs/rank3_cap5_n19.bin'
        
        q_caps = {}
        if qbin.exists():
            with open(qbin, 'rb') as f:
                magic = f.read(8)
                n_q = struct.unpack('<I', f.read(4))[0]
                for _ in range(n_q):
                    cap_q = struct.unpack('<B', f.read(1))[0]
                    dim_q = struct.unpack('<B', f.read(1))[0]
                    _res = struct.unpack('<H', f.read(2))[0]
                    wds = list(struct.unpack('<4Q', f.read(32)))
                    qm = 0
                    for w_idx, w in enumerate(wds):
                        qm |= w << (64 * w_idx)
                    if qm not in q_caps or cap_q < q_caps[qm]:
                        q_caps[qm] = cap_q
        
        # Process WANG512 rows containing q
        q_containing_rows = []
        new_tighter = []  # quotient constraints tighter than quotient LUT
        new_not_in_lut = []  # quotient projections not in quotient LUT
        
        with open(WANG512, 'rb') as f:
            magic = f.read(8); assert magic == b'WANG512\x01'
            n = struct.unpack('<I', f.read(4))[0]
            for idx in range(n):
                cap = struct.unpack('<B', f.read(1))[0]
                dim = struct.unpack('<B', f.read(1))[0]
                _res = struct.unpack('<H', f.read(2))[0]
                words = list(struct.unpack('<8Q', f.read(64)))
                def bit(ws, p): return (ws[p >> 6] >> (p & 63)) & 1
                
                if not bit(words, pivot):
                    continue  # not containing q
                
                # Build quotient mask
                qmask = 0
                for p, a0, a1 in lifts:
                    if bit(words, a0) or bit(words, a1):
                        qmask |= 1 << (p-1)
                
                if qmask == 0:
                    continue
                
                # Quotient constraint: |S ∩ π(W)| ≤ cap20(W) - 1
                qcap_from_full = cap - 1  # subtract 1 for q itself
                k = bin(qmask).count('1')
                
                q_containing_rows.append((qmask, qcap_from_full, dim, idx))
                
                # Compare with quotient LUT
                qcap_lut = q_caps.get(qmask, None)
                if qcap_lut is None:
                    if qcap_from_full <= 5:
                        new_not_in_lut.append((qmask, qcap_from_full, k, dim))
                elif qcap_from_full < qcap_lut:
                    new_tighter.append((qmask, qcap_from_full, qcap_lut, k, dim))
        
        print(f"  Total q-containing rows: {len(q_containing_rows)}")
        print(f"  Strictly tighter than quotient LUT: {len(new_tighter)}")
        print(f"  Not in quotient LUT (new, cap≤5): {len(new_not_in_lut)}")
        
        # Deduplicate: keep tightest per qmask
        best_per_mask = {}
        for qmask, qcap_full, dim, idx in q_containing_rows:
            if qmask not in best_per_mask or qcap_full < best_per_mask[qmask][0]:
                best_per_mask[qmask] = (qcap_full, dim, idx)
        
        # Count new useful constraints
        new_useful = []
        for qmask, (qcap_full, dim, idx) in best_per_mask.items():
            qcap_lut = q_caps.get(qmask, None)
            if qcap_lut is None and qcap_full <= 5:
                new_useful.append((qmask, qcap_full, dim))
            elif qcap_lut is not None and qcap_full < qcap_lut:
                new_useful.append((qmask, qcap_full, dim))
        
        print(f"  Distinct quotient projections from q-containing rows: {len(best_per_mask)}")
        print(f"  New useful (tighter or absent from LUT, cap≤5): {len(new_useful)}")
        
        # Cap distribution of new useful
        new_cap_hist = Counter(r[1] for r in new_useful)
        new_k_hist = Counter(bin(r[0]).count('1') for r in new_useful)
        print(f"  New by cap: {dict(sorted(new_cap_hist.items()))}")
        print(f"  New by k: {dict(sorted(new_k_hist.items()))}")
        
        # Export as E11WANG1
        if new_useful:
            bin_path = OUTDIR / f'{pname}_qcontaining_lift_rows.bin'
            data = bytearray()
            data.extend(b'E11WANG1')
            data.extend(struct.pack('<I', len(new_useful)))
            for qmask, qcap, dim in new_useful:
                data.extend(struct.pack('<BBH', qcap, dim, 0))
                for w_idx in range(4):
                    word = (qmask >> (64 * w_idx)) & ((1 << 64) - 1)
                    data.extend(struct.pack('<Q', word))
            bin_bytes = bytes(data)
            bin_path.write_bytes(bin_bytes)
            bin_sha = sha256(bin_bytes)
            print(f"  Exported to {bin_path}, SHA256={bin_sha}")
        
        # Check peer support against new constraints
        if pname == 'rank2':
            peer_support = [1,3,9,33,99,128,132,144,148,160,184,189,192,198,209,215,224,249,254]
            peer_mask = 0
            for p in peer_support:
                peer_mask |= 1 << (p - 1)
            
            violations = []
            for qmask, qcap, dim in new_useful:
                overlap = peer_mask & qmask
                occ = bin(overlap).count('1')
                if occ > qcap:
                    violations.append({
                        'qmask_hex': hex(qmask),
                        'cap': qcap,
                        'occ': occ,
                        'excess': occ - qcap,
                        'k': bin(qmask).count('1'),
                    })
            
            print(f"\n  Peer support violations from q-containing: {len(violations)}")
            for v in violations[:10]:
                print(f"    k={v['k']}, cap={v['cap']}, occ={v['occ']}, excess={v['excess']}")
        
        results[pname] = {
            'pivot': pivot,
            'q_containing_rows': len(q_containing_rows),
            'distinct_projections': len(best_per_mask),
            'new_tighter': len(new_tighter),
            'new_not_in_lut': len(new_not_in_lut),
            'new_useful': len(new_useful),
            'new_cap_hist': {str(k): v for k, v in sorted(new_cap_hist.items())},
            'new_k_hist': {str(k): v for k, v in sorted(new_k_hist.items())},
        }
    
    results['elapsed_sec'] = time.time() - t0
    out_path = OUTDIR / 'qcontaining_analysis.json'
    out_path.write_text(json.dumps(results, indent=2, default=str) + '\n')
    print(f"\nSaved to {out_path}, time={results['elapsed_sec']:.1f}s")

if __name__ == '__main__':
    main()
