#!/usr/bin/env python3
"""analysis: Fast double-counting effective capacity from lift-bit graph families.

For a dim-d quotient subspace U with family of 2^d graph constraints:
  sum_ell A(ell) = |S| * 2^{d-1}

Therefore |S| <= floor(sum_ell cap(ell) / 2^{d-1}).

This is computable in O(1) per family (just sum the caps) and gives valid
quotient occupation constraints. For non-matching families (those not in the
quotient DFS), this can produce NEW rows with small effective cap.
"""
from __future__ import annotations
import json, struct, time
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

def main():
    t0 = time.time()
    results = {'schema': 's0908_dc_effective_cap_v1', 'pivots': {}}
    
    for pname, pivot in PIVOTS.items():
        print(f"\nProcessing {pname} (pivot={pivot})...")
        
        lifts = [(p, lift0(p, pivot), lift0(p, pivot) ^ pivot) for p in range(1, 256)]
        
        # Read rows, group by quotient projection
        by_qmask = defaultdict(list)  # qmask -> [(cap, dim)]
        with open(WANG512, 'rb') as f:
            magic = f.read(8); assert magic == b'WANG512\x01'
            n = struct.unpack('<I', f.read(4))[0]
            for idx in range(n):
                cap = struct.unpack('<B', f.read(1))[0]
                dim = struct.unpack('<B', f.read(1))[0]
                _res = struct.unpack('<H', f.read(2))[0]
                words = list(struct.unpack('<8Q', f.read(64)))
                def bit(ws, p): return (ws[p >> 6] >> (p & 63)) & 1
                if bit(words, pivot): continue  # skip q-containing rows
                qmask = 0
                for p, a0, a1 in lifts:
                    if bit(words, a0) or bit(words, a1):
                        qmask |= 1 << (p-1)
                if qmask == 0: continue
                by_qmask[qmask].append((cap, dim))
        
        print(f"  {len(by_qmask)} distinct quotient projections")
        
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
                    cap = struct.unpack('<B', f.read(1))[0]
                    dim = struct.unpack('<B', f.read(1))[0]
                    _res = struct.unpack('<H', f.read(2))[0]
                    words = list(struct.unpack('<4Q', f.read(32)))
                    qmask = 0
                    for w_idx, w in enumerate(words):
                        qmask |= w << (64 * w_idx)
                    if qmask not in q_caps or cap < q_caps[qmask]:
                        q_caps[qmask] = cap
            print(f"  {len(q_caps)} quotient rows loaded")
        
        # Compute DC bounds
        dc_results = []
        new_constraint_count = 0
        reduction_count = 0
        dc_cap_hist = Counter()
        improvement_hist = Counter()
        new_row_candidates = []  # (qmask, dc_cap, k) for non-matching with dc_cap <= 5
        
        for qmask, group in by_qmask.items():
            k = bin(qmask).count('1')
            
            # Get dimension from the rows
            dims = set(r[1] for r in group)
            d = max(dims)  # should be consistent
            
            # Count distinct graph patterns
            n_rows = len(group)
            cap_sum = sum(r[0] for r in group)
            
            # Double-counting bound
            half_dim = 1 << (d - 1) if d > 0 else 1
            dc_cap = cap_sum // half_dim
            dc_cap = min(dc_cap, k)  # can't exceed total points
            
            dc_cap_hist[dc_cap] += 1
            
            qcap = q_caps.get(qmask, None)
            
            if qcap is not None:
                if dc_cap < qcap:
                    reduction_count += 1
                    improvement_hist[qcap - dc_cap] += 1
            else:
                # Non-matching: quotient cap > 5
                if dc_cap <= 5:
                    new_constraint_count += 1
                    new_row_candidates.append((qmask, dc_cap, k, d, n_rows, cap_sum))
        
        new_row_candidates.sort(key=lambda r: (r[1], -r[2]))
        
        print(f"  DC cap histogram: {dict(sorted(dc_cap_hist.items()))}")
        print(f"  Matching families with DC < quotient: {reduction_count}")
        print(f"  Improvement histogram: {dict(sorted(improvement_hist.items()))}")
        print(f"  Non-matching with DC cap <= 5: {new_constraint_count}")
        
        # Categorize new constraints
        new_by_cap = Counter()
        new_by_k = Counter()
        for qmask, dc, k, d, nr, cs in new_row_candidates:
            new_by_cap[dc] += 1
            new_by_k[k] += 1
        
        print(f"  New rows by DC cap: {dict(sorted(new_by_cap.items()))}")
        print(f"  New rows by k: {dict(sorted(new_by_k.items()))}")
        
        # Show top new constraints
        if new_row_candidates:
            print(f"\n  Top new constraints:")
            for i, (qmask, dc, k, d, nr, cs) in enumerate(new_row_candidates[:10]):
                pts = sorted([b+1 for b in range(255) if (qmask >> b) & 1])
                print(f"    {i}: k={k}, dc_cap={dc}, dim={d}, n_rows={nr}, "
                      f"cap_sum={cs}, pts={pts[:5]}...")
        
        results['pivots'][pname] = {
            'pivot': pivot,
            'total_families': len(by_qmask),
            'dc_cap_hist': {str(k): v for k, v in sorted(dc_cap_hist.items())},
            'matching_reductions': reduction_count,
            'improvement_hist': {str(k): v for k, v in sorted(improvement_hist.items())},
            'new_constraints_count': new_constraint_count,
            'new_by_cap': {str(k): v for k, v in sorted(new_by_cap.items())},
            'new_by_k': {str(k): v for k, v in sorted(new_by_k.items())},
            'top_new_constraints': [
                {'qmask_hex': hex(qm), 'dc_cap': dc, 'k': k, 'dim': d,
                 'n_rows': nr, 'cap_sum': cs,
                 'points': sorted([b+1 for b in range(255) if (qm >> b) & 1])}
                for qm, dc, k, d, nr, cs in new_row_candidates[:100]
            ],
        }
    
    results['elapsed_sec'] = time.time() - t0
    out_path = OUTDIR / 'dc_effective_cap.json'
    out_path.write_text(json.dumps(results, indent=2, default=str) + '\n')
    print(f"\nSaved to {out_path}, time={results['elapsed_sec']:.1f}s")

if __name__ == '__main__':
    main()
