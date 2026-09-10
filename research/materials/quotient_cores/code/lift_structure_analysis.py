#!/usr/bin/env python3
"""analysis: Analyze lift-bit constraint structure for quotient pivots.

Key question: which full-tensor Wang rows (not containing q) add information
beyond what the quotient tensor's own Wang rows provide?

For a row W with q not in W, projection pi(W) = U is a quotient subspace.
The quotient row for U says |P ∩ U| <= cap_quotient(U).
The full row says #{p in P ∩ U : eps_p = ell_W(p)} <= cap20(W).

The lift-bit row is STRICTLY TIGHTER when cap20(W) < |P ∩ U| is possible
under quotient rows, AND the lift-bit constraint eliminates some lift
assignments that quotient alone allows.

For a fixed U, there are 2^dim(U) possible graph subspaces (one per linear
functional on U). Each gives a different ell_W pattern. When multiple graphs
over the same U all have small cap20, they jointly constrain the lift-bit
distribution, potentially creating parity/circuit structure.

The example: dim-2 U with all 4 graphs at cap 2, active k=3,
gives eps_u + eps_v + eps_{u+v} = 1 (mod 2) — a parity constraint!
"""
from __future__ import annotations
import json, struct, time, hashlib, sys
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
    """Return only non-q rows with their lift patterns."""
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
            
            def bit(ws, p):
                return (ws[p >> 6] >> (p & 63)) & 1
            
            if bit(words, pivot):
                continue  # skip rows containing q
            
            ag0 = 0; ag1 = 0
            for p, a0, a1 in lifts:
                if bit(words, a0): ag0 |= 1 << (p-1)
                if bit(words, a1): ag1 |= 1 << (p-1)
            
            qmask = ag0 | ag1
            if qmask == 0:
                continue  # no quotient points in this row
            
            rows.append((cap, dim, qmask, ag0, ag1, idx))
    
    return rows

def analyze_graph_families(rows, pivot_name):
    """Group rows by their quotient projection and analyze the graph structure."""
    # Group by quotient mask
    by_qmask = defaultdict(list)
    for cap, dim, qmask, ag0, ag1, idx in rows:
        by_qmask[qmask].append((cap, dim, ag0, ag1, idx))
    
    print(f"\n=== {pivot_name} graph family analysis ===")
    print(f"Total non-q rows: {len(rows)}")
    print(f"Distinct quotient projections: {len(by_qmask)}")
    
    # For each quotient subspace, analyze the graph family
    families = []
    parity_examples = []
    
    for qmask, group in sorted(by_qmask.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        k = bin(qmask).count('1')
        caps = [r[0] for r in group]
        dims = set(r[1] for r in group)
        
        # Count distinct lift patterns (agree0, agree1)
        patterns = {}
        for cap, dim, ag0, ag1, idx in group:
            pat = (ag0, ag1)
            if pat not in patterns or cap < patterns[pat][0]:
                patterns[pat] = (cap, dim, idx)
        
        min_cap = min(caps)
        max_cap = max(caps)
        n_graphs = len(patterns)
        
        # For dim-d subspace, max possible graphs = 2^d (including the trivial identity)
        # The quotient mask has k = 2^d - 1 nonzero points for a dim-d subspace
        
        # Check for parity structure: if all graphs have the same cap,
        # the lift bits over this subspace are constrained by a code
        if k >= 3 and n_graphs >= 3 and min_cap < k:
            fam = {
                'qmask_hex': hex(qmask),
                'k': k,
                'n_graphs': n_graphs,
                'min_cap': min_cap,
                'max_cap': max_cap,
                'dims': sorted(dims),
                'patterns': [],
            }
            for (ag0, ag1), (cap, dim, idx) in sorted(patterns.items(), key=lambda kv: kv[1][0]):
                pts_0 = sorted([b+1 for b in range(255) if (ag0 >> b) & 1])
                pts_1 = sorted([b+1 for b in range(255) if (ag1 >> b) & 1])
                fam['patterns'].append({
                    'agree0': pts_0,  # quotient points where lift0 ∈ W
                    'agree1': pts_1,
                    'cap20': cap,
                    'n_agree0': len(pts_0),
                    'n_agree1': len(pts_1),
                })
            families.append(fam)
            
            # Check for parity: if all graphs have same cap and k = 2*cap + 1,
            # the constraints force an odd number of a specific parity
            if min_cap == max_cap and k == 2 * min_cap + 1 and n_graphs == k + 1:
                parity_examples.append(fam)
    
    families.sort(key=lambda f: (f['min_cap'], -f['k'], -f['n_graphs']))
    
    print(f"Families with k>=3, n_graphs>=3, min_cap < k: {len(families)}")
    print(f"Parity examples (k=2c+1, all same cap, n_graphs=k+1): {len(parity_examples)}")
    
    # Print top families
    for i, fam in enumerate(families[:10]):
        print(f"\n  Family {i}: k={fam['k']}, graphs={fam['n_graphs']}, "
              f"caps=[{fam['min_cap']},{fam['max_cap']}], dims={fam['dims']}")
        for j, pat in enumerate(fam['patterns'][:4]):
            print(f"    Graph {j}: agree0={pat['n_agree0']}, agree1={pat['n_agree1']}, cap={pat['cap20']}")
    
    return families, parity_examples

def analyze_quotient_vs_full(rows, pivot, pivot_name):
    """Compare full-tensor row caps with quotient-tensor row caps.
    
    For each non-q row W with projection U, the quotient cap is cap_q(U) = 19 - LB(T/q/U).
    The full cap is cap20(W). If cap20(W) < cap_q(U), the full row is strictly tighter.
    
    We don't have the quotient LUT directly, but we can compare with the quotient
    binary's rows for the same subspace.
    """
    # Load quotient rows for comparison
    if pivot == 17:
        qbin = Path('data/quotient_dfs/rank2_cap5_n19.bin')
    else:
        qbin = Path('data/quotient_dfs/rank3_cap5_n19.bin')
    
    if not qbin.exists():
        # Try peer path
        if pivot == 17:
            qbin = Path('data/wang_native/quotient_binaries/rank2_all_n19.bin')
        else:
            qbin = Path('data/wang_native/quotient_binaries/rank3_all_n19.bin')
    
    if not qbin.exists():
        print(f"  Quotient binary not found for {pivot_name}, skipping comparison")
        return {}
    
    # Load quotient rows: E11WANG1 format (256-bit masks)
    q_caps = {}  # qmask -> min quotient cap
    with open(qbin, 'rb') as f:
        magic = f.read(8); assert magic == b'E11WANG1', f"Bad magic: {magic}"
        n = struct.unpack('<I', f.read(4))[0]
        for _ in range(n):
            cap = struct.unpack('<B', f.read(1))[0]
            dim = struct.unpack('<B', f.read(1))[0]
            _res = struct.unpack('<H', f.read(2))[0]
            words = list(struct.unpack('<4Q', f.read(32)))
            qmask = 0
            for w_idx, w in enumerate(words):
                qmask |= w << (64 * w_idx)
            if qmask in q_caps:
                q_caps[qmask] = min(q_caps[qmask], cap)
            else:
                q_caps[qmask] = cap
    
    print(f"\n  Quotient rows loaded: {len(q_caps)} distinct masks")
    
    # Compare: for each full non-q row, check if its cap20 < quotient cap for same projection
    tighter_count = 0
    same_count = 0
    looser_count = 0
    no_match = 0
    tighter_examples = []
    
    by_qmask = defaultdict(list)
    for cap, dim, qmask, ag0, ag1, idx in rows:
        by_qmask[qmask].append((cap, dim, ag0, ag1, idx))
    
    for qmask, group in by_qmask.items():
        min_full_cap = min(r[0] for r in group)
        if qmask in q_caps:
            qcap = q_caps[qmask]
            # The full row cap applies to occupation counting selected lifts in W
            # The quotient row cap applies to total quotient points in U
            # These are different things! The full row is tighter because it
            # counts only the matching-lift points, not all points.
            # But the quotient cap also counts all points, which is an upper bound
            # on the matching-lift count.
            # So full cap < quotient cap means: even the lift-aware count is bounded
            # more tightly than the quotient occupation.
            if min_full_cap < qcap:
                tighter_count += 1
                k = bin(qmask).count('1')
                if len(tighter_examples) < 20:
                    tighter_examples.append({
                        'qmask_hex': hex(qmask),
                        'k': k,
                        'full_cap': min_full_cap,
                        'quotient_cap': qcap,
                        'gap': qcap - min_full_cap,
                        'n_graphs': len(set((r[2], r[3]) for r in group)),
                    })
            elif min_full_cap == qcap:
                same_count += 1
            else:
                looser_count += 1
        else:
            no_match += 1
    
    print(f"  Full cap < quotient cap: {tighter_count}")
    print(f"  Full cap == quotient cap: {same_count}")
    print(f"  Full cap > quotient cap: {looser_count}")
    print(f"  No matching quotient row: {no_match}")
    
    if tighter_examples:
        print(f"\n  First tighter examples:")
        for ex in tighter_examples[:5]:
            print(f"    k={ex['k']}, full={ex['full_cap']}, quotient={ex['quotient_cap']}, "
                  f"gap={ex['gap']}, graphs={ex['n_graphs']}")
    
    return {
        'tighter': tighter_count,
        'same': same_count,
        'looser': looser_count,
        'no_match': no_match,
        'tighter_examples': tighter_examples,
    }

def main():
    t0 = time.time()
    results = {'schema': 's0908_lift_structure_analysis_v1'}
    
    for pname, pivot in PIVOTS.items():
        print(f"\nPreprocessing for {pname} (pivot={pivot})...")
        rows = preprocess_rows(pivot)
        print(f"  {len(rows)} non-q rows with quotient points")
        
        families, parity_ex = analyze_graph_families(rows, pname)
        comparison = analyze_quotient_vs_full(rows, pivot, pname)
        
        results[pname] = {
            'pivot': pivot,
            'non_q_rows': len(rows),
            'n_families_interesting': len(families),
            'n_parity_examples': len(parity_ex),
            'comparison': comparison,
            'top_families': families[:20],
            'parity_examples': parity_ex[:10],
        }
    
    results['elapsed_sec'] = time.time() - t0
    out_path = OUTDIR / 'lift_structure_analysis.json'
    out_path.write_text(json.dumps(results, indent=2, default=str) + '\n')
    print(f"\nSaved to {out_path}")
    print(f"Total time: {results['elapsed_sec']:.1f}s")

if __name__ == '__main__':
    main()
