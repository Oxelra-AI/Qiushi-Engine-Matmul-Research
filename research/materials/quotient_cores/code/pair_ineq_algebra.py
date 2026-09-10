#!/usr/bin/env python3
"""analysis: verify the signed pair-inequality algebra and build pair constraints.

For two Wang rows R,S with caps c_R,c_S, adding the two upper bounds with |S|=19 gives:
   sum_{p in O} x_p - sum_{p in I} x_p >= 19 - c_R - c_S
where I=R cap S, O={1,...,255}\(R cup S).

This script:
1. Extracts the specific cap-7 rows violated by branch-0 relaxation supports
2. Verifies the signed-inequality algebra on those supports
3. Computes pairwise I, O, M statistics for all pairs
4. Identifies the strongest pairs (smallest |O|)
5. Checks if any pair creates an impossible or near-impossible constraint
"""
import json, struct, sys, itertools
from pathlib import Path

MAXP = 255
WORDS = 4

def load_rows_bin(path):
    """Load E11WANG1 binary."""
    data = Path(path).read_bytes()
    assert data[:8] == b'E11WANG1', f"bad magic: {data[:8]}"
    n = struct.unpack_from('<I', data, 8)[0]
    rows = []
    off = 12
    for i in range(n):
        cap = data[off]; dim = data[off+1]; off += 4
        wds = struct.unpack_from('<4Q', data, off); off += 32
        bits = set()
        for p in range(1, 256):
            w = p >> 6; b = p & 63
            if wds[w] & (1 << b): bits.add(p)
        rows.append({'cap': cap, 'dim': dim, 'bits': frozenset(bits), 'words': wds})
    return rows

def main():
    # Load full Wang table (cap<=16, all non-ambient)
    full_path = "data/domain_dfs_soundness/e11_wang_cap16_rebuilt.bin"
    full_rows = load_rows_bin(full_path)
    print(f"Loaded {len(full_rows)} full rows", file=sys.stderr)
    
    # Load rescan data
    rescan_path = "data/domain_dfs_soundness/rescan_branch0_cover512_solutions_head.json"
    rescan = json.loads(Path(rescan_path).read_text())
    
    # Collect violating row indices
    violating_indices = set()
    for rec in rescan['records']:
        for v in rec['first_wang_violations']:
            violating_indices.add(v['row_index'])
    
    violating_indices = sorted(violating_indices)
    print(f"Unique violating cap-7 row indices: {len(violating_indices)}")
    print(f"Indices: {violating_indices}")
    
    # Extract row data
    viol_rows = {}
    for ri in violating_indices:
        r = full_rows[ri]
        viol_rows[ri] = r
        print(f"  Row {ri}: cap={r['cap']}, dim={r['dim']}, |bits|={len(r['bits'])}")
    
    # Verify signed inequality on each relaxation support
    print("\n--- Verification of signed pair inequality on relaxation supports ---")
    for rec in rescan['records']:
        supp = set(rec['support'])
        assert len(supp) == 19
        viols = rec['first_wang_violations']
        
        # For each violating row, check the individual Wang bound
        for v in viols:
            ri = v['row_index']
            r = full_rows[ri]
            occ = len(supp & r['bits'])
            assert occ == v['occupancy']
            assert occ > r['cap']
        
        # For each pair of violating rows, check the signed inequality
        viol_ri = [v['row_index'] for v in viols]
        for i in range(len(viol_ri)):
            for j in range(i+1, min(len(viol_ri), i+4)):  # sample pairs
                ri, rj = viol_ri[i], viol_ri[j]
                R_bits = full_rows[ri]['bits']
                S_bits = full_rows[rj]['bits']
                c_R = full_rows[ri]['cap']
                c_S = full_rows[rj]['cap']
                
                I = R_bits & S_bits
                union_RS = R_bits | S_bits
                O = frozenset(range(1,256)) - union_RS
                threshold = 19 - c_R - c_S  # for cap-7,7: 5
                
                lhs = len(supp & O) - len(supp & I)
                
                if lhs < threshold:
                    print(f"  Support {rec['support_index']}, pair ({ri},{rj}): "
                          f"|I|={len(I)}, |O|={len(O)}, |M|={255-len(I)-len(O)}, "
                          f"threshold={threshold}, lhs={lhs} < {threshold} VIOLATED")
    
    # Compute all pairwise statistics
    print(f"\n--- Pairwise I,O,M statistics for {len(violating_indices)} rows ---")
    pairs_data = []
    all_pts = frozenset(range(1, 256))
    
    for i in range(len(violating_indices)):
        for j in range(i+1, len(violating_indices)):
            ri, rj = violating_indices[i], violating_indices[j]
            R = viol_rows[ri]['bits']
            S = viol_rows[rj]['bits']
            c_R = viol_rows[ri]['cap']
            c_S = viol_rows[rj]['cap']
            
            I = R & S
            union_RS = R | S
            O = all_pts - union_RS
            M = union_RS - I  # symmetric difference = (R\S) | (S\R)
            threshold = 19 - c_R - c_S
            
            pairs_data.append({
                'ri': ri, 'rj': rj,
                'c_R': c_R, 'c_S': c_S,
                'I_size': len(I), 'O_size': len(O), 'M_size': len(M),
                'union_size': len(union_RS), 'threshold': threshold,
                # Impossible if |O| < threshold (can't get enough O-points)
                'impossible_alone': len(O) < threshold,
                # Very tight if |O| is close to threshold
                'slack': len(O) - threshold,
            })
    
    # Sort by O_size (smallest = strongest)
    pairs_data.sort(key=lambda x: x['O_size'])
    
    impossible_count = sum(1 for p in pairs_data if p['impossible_alone'])
    print(f"Total pairs: {len(pairs_data)}")
    print(f"Impossible pairs (|O| < threshold): {impossible_count}")
    
    # Show tightest pairs
    print("\nTightest 30 pairs:")
    for p in pairs_data[:30]:
        tag = " ** IMPOSSIBLE" if p['impossible_alone'] else ""
        print(f"  ({p['ri']},{p['rj']}): |I|={p['I_size']}, |O|={p['O_size']}, "
              f"|M|={p['M_size']}, threshold={p['threshold']}, slack={p['slack']}{tag}")
    
    # Show O_size histogram
    o_hist = {}
    for p in pairs_data:
        o = p['O_size']
        o_hist[o] = o_hist.get(o, 0) + 1
    print("\n|O| histogram:")
    for o in sorted(o_hist.keys()):
        print(f"  |O|={o}: {o_hist[o]} pairs")
    
    # Also check: which relaxation supports violate which pairs?
    print("\n--- Pair violations on relaxation supports ---")
    pair_violation_counts = {}
    for rec in rescan['records']:
        supp = set(rec['support'])
        for p in pairs_data[:50]:  # check tightest 50
            ri, rj = p['ri'], p['rj']
            R = viol_rows[ri]['bits']
            S = viol_rows[rj]['bits']
            I = R & S
            O = all_pts - (R | S)
            lhs = len(supp & O) - len(supp & I)
            if lhs < p['threshold']:
                key = (ri, rj)
                pair_violation_counts[key] = pair_violation_counts.get(key, 0) + 1
    
    print(f"Pairs that violate at least one relaxation support: {len(pair_violation_counts)}")
    for (ri,rj), count in sorted(pair_violation_counts.items(), key=lambda x: -x[1])[:20]:
        p = next(x for x in pairs_data if x['ri']==ri and x['rj']==rj)
        print(f"  ({ri},{rj}): violated by {count}/5 supports, "
              f"|I|={p['I_size']}, |O|={p['O_size']}, threshold={p['threshold']}")
    
    # Save results
    out = {
        'schema': 's0908_pair_ineq_algebra_v1',
        'violating_row_indices': violating_indices,
        'violating_row_count': len(violating_indices),
        'pair_count': len(pairs_data),
        'impossible_pair_count': impossible_count,
        'tightest_30': pairs_data[:30],
        'O_size_histogram': {str(k):v for k,v in sorted(o_hist.items())},
        'pair_violations_on_relaxation_supports': {
            f"{ri},{rj}": cnt for (ri,rj), cnt in pair_violation_counts.items()
        },
    }
    
    outpath = Path("data/domain_dfs_soundness/pair_ineq_algebra.json")
    outpath.parent.mkdir(parents=True, exist_ok=True)
    outpath.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(f"\nSaved to {outpath}")
    print(json.dumps(out, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
