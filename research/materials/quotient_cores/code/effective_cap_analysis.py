#!/usr/bin/env python3
"""analysis: Compute effective capacity reduction from lift-bit graph families.

For a dim-d quotient subspace U with 2^d-1 nonzero points, the family of
2^d graph subspaces constrains both the occupation AND the lift bits.

The effective capacity is: max over (subset S, lift-bits eps) of |S|
subject to all graph constraints. When this is less than the quotient
single-row capacity, the lift-bit family provides tighter pruning.

For d=3 (k=7): brute-force over 128 eps assignments × 128 subsets.
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

def preprocess_rows(pivot):
    lifts = []
    for p in range(1, 256):
        a0 = lift0(p, pivot)
        a1 = a0 ^ pivot
        lifts.append((p, a0, a1))
    
    rows = []
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
            rows.append((cap, dim, qmask, ag0, ag1, idx))
    return rows


def compute_effective_cap(family_rows, k):
    """For a family of graph constraints over k quotient points,
    compute the effective capacity: max |S| over (S, eps) satisfying all constraints.
    
    family_rows: list of (cap, agree0_local, agree1_local) where masks are k-bit local.
    """
    max_m = 0
    best_eps = None
    best_subset = None
    
    # Iterate over all possible eps assignments (2^k)
    for eps_bits in range(1 << k):
        # For this eps, find max subset satisfying all constraints
        # Greedy: start with all k points, check constraints, remove if needed
        
        # For each graph constraint, count agreements
        selected = (1 << k) - 1  # all k bits
        
        # Check feasibility
        feasible = True
        for cap, ag0_local, ag1_local in family_rows:
            # Agreement count: #{p in selected : eps agrees with graph}
            # agree0: eps_p should be 0 for these points
            # agree1: eps_p should be 1 for these points
            agree_mask = (ag0_local & ~eps_bits) | (ag1_local & eps_bits)
            count = bin(agree_mask & selected).count('1')
            if count > cap:
                feasible = False
                break
        
        if feasible:
            max_m = k
            best_eps = eps_bits
            best_subset = selected
            break  # Can't do better than all k
        
        # If not feasible with all k, try subsets of decreasing size
        # For k=7, use greedy: remove the point that violates most constraints
        current = (1 << k) - 1
        for _ in range(k):
            ok = True
            worst_excess = -1
            worst_pt = -1
            for cap, ag0_local, ag1_local in family_rows:
                agree_mask = (ag0_local & ~eps_bits) | (ag1_local & eps_bits)
                count = bin(agree_mask & current).count('1')
                excess = count - cap
                if excess > 0:
                    ok = False
                    # Find which points contribute to this violation
                    violating = agree_mask & current
                    # Try removing each
                    tmp = violating
                    while tmp:
                        b = tmp & (-tmp)
                        pt_idx = b.bit_length() - 1
                        # Count how many constraints this point participates in excess
                        pt_excess = 0
                        for c2, a02, a12 in family_rows:
                            am2 = (a02 & ~eps_bits) | (a12 & eps_bits)
                            cnt2 = bin(am2 & current).count('1')
                            if cnt2 > c2 and (am2 & b):
                                pt_excess += cnt2 - c2
                        if pt_excess > worst_excess:
                            worst_excess = pt_excess
                            worst_pt = pt_idx
                        tmp ^= b
            
            if ok:
                m = bin(current).count('1')
                if m > max_m:
                    max_m = m
                    best_eps = eps_bits
                    best_subset = current
                break
            
            if worst_pt >= 0:
                current &= ~(1 << worst_pt)
            else:
                break
        
        m = bin(current).count('1')
        # Check feasibility of reduced set
        ok = True
        for cap, ag0_local, ag1_local in family_rows:
            agree_mask = (ag0_local & ~eps_bits) | (ag1_local & eps_bits)
            count = bin(agree_mask & current).count('1')
            if count > cap:
                ok = False
                break
        if ok and m > max_m:
            max_m = m
            best_eps = eps_bits
            best_subset = current
    
    return max_m, best_eps, best_subset


def compute_effective_cap_exact(family_rows, k):
    """Exact computation: try all (eps, subset) pairs for small k."""
    max_m = 0
    for eps_bits in range(1 << k):
        # For this eps, find max feasible subset
        # Try subsets from largest to smallest
        for subset in range(((1 << k) - 1), 0, -1):
            m = bin(subset).count('1')
            if m <= max_m:
                break  # Can't improve
            
            ok = True
            for cap, ag0_local, ag1_local in family_rows:
                agree_mask = (ag0_local & ~eps_bits) | (ag1_local & eps_bits)
                count = bin(agree_mask & subset).count('1')
                if count > cap:
                    ok = False
                    break
            
            if ok:
                max_m = m
                break
    
    return max_m


def main():
    t0 = time.time()
    results = {'schema': 's0908_effective_cap_v1', 'pivots': {}}
    
    for pname, pivot in PIVOTS.items():
        print(f"\nProcessing {pname} (pivot={pivot})...")
        rows = preprocess_rows(pivot)
        
        # Group by quotient mask
        by_qmask = defaultdict(list)
        for cap, dim, qmask, ag0, ag1, idx in rows:
            by_qmask[qmask].append((cap, dim, ag0, ag1, idx))
        
        # Also load quotient caps
        if pivot == 17:
            qbin = ROOT / 'workspace/data/quotient_dfs/rank2_cap5_n19.bin'
        else:
            qbin = ROOT / 'workspace/data/quotient_dfs/rank3_cap5_n19.bin'
        
        q_caps = {}
        if qbin.exists():
            with open(qbin, 'rb') as f:
                magic = f.read(8)
                n = struct.unpack('<I', f.read(4))[0]
                for _ in range(n):
                    cap = struct.unpack('<B', f.read(1))[0]
                    dim = struct.unpack('<B', f.read(1))[0]
                    _res = struct.unpack('<H', f.read(2))[0]
                    words = list(struct.unpack('<4Q', f.read(32)))
                    qmask = 0
                    for w_idx, w in enumerate(words):
                        qmask |= w << (64 * w_idx)
                    if qmask not in q_caps or cap < q_caps[qmask]:
                        q_caps[qmask] = cap
        
        # Analyze dim-3 families (k=7, exact brute-force feasible)
        dim3_count = 0
        reductions = []
        cap_reduction_hist = Counter()
        
        for qmask, group in by_qmask.items():
            k = bin(qmask).count('1')
            if k != 7:
                continue
            dim3_count += 1
            
            # Build local masks (remap to positions 0..6)
            pts = []
            tmp = qmask
            while tmp:
                b = tmp & (-tmp)
                pts.append(b.bit_length() - 1)
                tmp ^= b
            assert len(pts) == 7
            
            pt_to_local = {p: i for i, p in enumerate(pts)}
            
            family = []
            for cap, dim, ag0, ag1, idx in group:
                ag0_local = 0; ag1_local = 0
                for p in pts:
                    i = pt_to_local[p]
                    if (ag0 >> (p)) & 1:  # p is 0-indexed bit position
                        ag0_local |= 1 << i
                    if (ag1 >> (p)) & 1:
                        ag1_local |= 1 << i
                family.append((cap, ag0_local, ag1_local))
            
            # Compute effective cap
            eff_cap = compute_effective_cap_exact(family, 7)
            
            # Compare with quotient cap
            qcap = q_caps.get(qmask, None)
            if qcap is not None:
                reduction = qcap - eff_cap
                cap_reduction_hist[reduction] += 1
                if reduction > 0:
                    caps_in_family = sorted(set(r[0] for r in family))
                    reductions.append({
                        'qmask_hex': hex(qmask),
                        'k': k,
                        'quotient_cap': qcap,
                        'effective_cap': eff_cap,
                        'reduction': reduction,
                        'n_graphs': len(set((r[1], r[2]) for r in family)),
                        'cap_range': caps_in_family,
                    })
            
            if dim3_count % 5000 == 0:
                print(f"  Processed {dim3_count} dim-3 families...")
        
        reductions.sort(key=lambda r: -r['reduction'])
        
        print(f"  Total dim-3 families: {dim3_count}")
        print(f"  Cap reduction histogram: {dict(sorted(cap_reduction_hist.items()))}")
        print(f"  Families with reduction > 0: {len(reductions)}")
        if reductions:
            print(f"  Max reduction: {reductions[0]['reduction']}")
            for r in reductions[:5]:
                print(f"    qmask={r['qmask_hex']}, qcap={r['quotient_cap']}, "
                      f"eff={r['effective_cap']}, Δ={r['reduction']}, "
                      f"graphs={r['n_graphs']}, caps={r['cap_range']}")
        
        results['pivots'][pname] = {
            'pivot': pivot,
            'dim3_families': dim3_count,
            'cap_reduction_hist': dict(sorted(cap_reduction_hist.items())),
            'reductions_count': len(reductions),
            'max_reduction': reductions[0]['reduction'] if reductions else 0,
            'top_reductions': reductions[:50],
        }
    
    results['elapsed_sec'] = time.time() - t0
    out_path = OUTDIR / 'effective_cap_analysis.json'
    out_path.write_text(json.dumps(results, indent=2, default=str) + '\n')
    print(f"\nSaved to {out_path}")
    print(f"Total time: {results['elapsed_sec']:.1f}s")

if __name__ == '__main__':
    main()
