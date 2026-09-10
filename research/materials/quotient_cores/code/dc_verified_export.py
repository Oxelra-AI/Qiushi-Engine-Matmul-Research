#!/usr/bin/env python3
"""analysis: Verify DC bound validity and export usable new quotient constraints.

The DC bound |S| <= sum(caps) / 2^{d-1} requires ALL 2^d graph subspaces.
If some graphs have cap > 5 (missing from WANG512), the DC bound is invalid.

This script:
1. Counts distinct graph patterns per family
2. Only accepts families with exactly 2^d patterns (all graphs present)
3. Exports valid new constraints in E11WANG1 format for the quotient DFS
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

def sha256(data_bytes):
    return hashlib.sha256(data_bytes).hexdigest()

def main():
    t0 = time.time()
    results = {'schema': 's0908_dc_verified_v1', 'pivots': {}}
    
    for pname, pivot in PIVOTS.items():
        print(f"\n=== {pname} (pivot={pivot}) ===")
        
        lifts = [(p, lift0(p, pivot), lift0(p, pivot) ^ pivot) for p in range(1, 256)]
        
        # Read rows, group by quotient mask with distinct graph patterns
        by_qmask = defaultdict(dict)  # qmask -> {(ag0,ag1) -> min_cap}
        dim_of = {}  # qmask -> dim
        
        with open(WANG512, 'rb') as f:
            magic = f.read(8); assert magic == b'WANG512\x01'
            n = struct.unpack('<I', f.read(4))[0]
            for idx in range(n):
                cap = struct.unpack('<B', f.read(1))[0]
                dim = struct.unpack('<B', f.read(1))[0]
                _res = struct.unpack('<H', f.read(2))[0]
                words = list(struct.unpack('<8Q', f.read(64)))
                def bit(ws, p): return (ws[p >> 6] >> (p & 63)) & 1
                if bit(words, pivot): continue
                ag0 = 0; ag1 = 0
                for p, a0, a1 in lifts:
                    if bit(words, a0): ag0 |= 1 << (p-1)
                    if bit(words, a1): ag1 |= 1 << (p-1)
                qmask = ag0 | ag1
                if qmask == 0: continue
                pat = (ag0, ag1)
                if pat not in by_qmask[qmask] or cap < by_qmask[qmask][pat]:
                    by_qmask[qmask][pat] = cap
                dim_of[qmask] = max(dim_of.get(qmask, 0), dim)
        
        # Load quotient caps for comparison
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
        
        # Analyze families
        complete_families = 0
        incomplete_families = 0
        new_valid_rows = []  # (qmask, dc_cap, k, dim, cap_sum, n_graphs)
        
        completeness_hist = Counter()  # expected_graphs -> actual_graphs
        dc_cap_valid_hist = Counter()
        dc_cap_valid_new_hist = Counter()
        
        for qmask, patterns in by_qmask.items():
            k = bin(qmask).count('1')
            d = dim_of.get(qmask, 1)
            expected = 1 << d
            actual = len(patterns)
            
            completeness_hist[(expected, actual)] += 1
            
            if actual == expected:
                complete_families += 1
                cap_sum = sum(patterns.values())
                half_dim = 1 << (d - 1) if d > 0 else 1
                dc_cap = min(cap_sum // half_dim, k)
                dc_cap_valid_hist[dc_cap] += 1
                
                qcap = q_caps.get(qmask, None)
                is_new = qcap is None or dc_cap < qcap
                
                if is_new and dc_cap <= 5 and dc_cap < k:  # non-trivial
                    dc_cap_valid_new_hist[dc_cap] += 1
                    new_valid_rows.append((qmask, dc_cap, k, d, cap_sum, actual))
            else:
                incomplete_families += 1
        
        print(f"  Complete families (all 2^d graphs): {complete_families}")
        print(f"  Incomplete families: {incomplete_families}")
        print(f"  Completeness distribution (top 10):")
        for (exp, act), cnt in sorted(completeness_hist.items(), key=lambda x: -x[1])[:10]:
            print(f"    expected={exp}, actual={act}: {cnt}")
        
        print(f"\n  Valid DC caps (complete families): {dict(sorted(dc_cap_valid_hist.items()))}")
        print(f"  New valid constraints (non-trivial, cap <= 5): {len(new_valid_rows)}")
        print(f"  New by DC cap: {dict(sorted(dc_cap_valid_new_hist.items()))}")
        
        new_valid_rows.sort(key=lambda r: (r[1], -r[2]))
        
        # Export new valid rows as E11WANG1 binary
        if new_valid_rows:
            bin_path = OUTDIR / f'{pname}_dc_lift_rows.bin'
            bin_data = bytearray()
            bin_data.extend(b'E11WANG1')
            bin_data.extend(struct.pack('<I', len(new_valid_rows)))
            for qmask, dc_cap, k, d, cs, ng in new_valid_rows:
                bin_data.extend(struct.pack('<BBH', dc_cap, d, 0))
                # Write 4 x 64-bit words for 256-bit mask
                for w_idx in range(4):
                    word = (qmask >> (64 * w_idx)) & ((1 << 64) - 1)
                    bin_data.extend(struct.pack('<Q', word))
            
            bin_bytes = bytes(bin_data)
            bin_path.write_bytes(bin_bytes)
            bin_sha = sha256(bin_bytes)
            print(f"\n  Exported {len(new_valid_rows)} rows to {bin_path}")
            print(f"  SHA256: {bin_sha}")
            
            # Show examples
            print(f"\n  Top new constraints:")
            for i, (qm, dc, k, d, cs, ng) in enumerate(new_valid_rows[:10]):
                pts = sorted([b+1 for b in range(255) if (qm >> b) & 1])
                qcap = q_caps.get(qm, '>5')
                print(f"    {i}: k={k}, dc_cap={dc}, dim={d}, qcap={qcap}, "
                      f"cap_sum={cs}, pts={pts[:8]}...")
            
            results['pivots'][pname] = {
                'pivot': pivot,
                'complete_families': complete_families,
                'incomplete_families': incomplete_families,
                'new_valid_rows': len(new_valid_rows),
                'dc_cap_valid_hist': {str(k): v for k, v in sorted(dc_cap_valid_hist.items())},
                'dc_cap_valid_new_hist': {str(k): v for k, v in sorted(dc_cap_valid_new_hist.items())},
                'binary_path': str(bin_path),
                'binary_sha256': bin_sha,
                'binary_rows': len(new_valid_rows),
                'top_examples': [
                    {'qmask_hex': hex(qm), 'dc_cap': dc, 'k': k, 'dim': d,
                     'cap_sum': cs, 'quotient_cap': q_caps.get(qm, None),
                     'points': sorted([b+1 for b in range(255) if (qm >> b) & 1])}
                    for qm, dc, k, d, cs, ng in new_valid_rows[:30]
                ],
            }
    
    results['elapsed_sec'] = time.time() - t0
    out_path = OUTDIR / 'dc_verified_export.json'
    out_path.write_text(json.dumps(results, indent=2, default=str) + '\n')
    print(f"\nSaved to {out_path}, time={results['elapsed_sec']:.1f}s")

if __name__ == '__main__':
    main()
