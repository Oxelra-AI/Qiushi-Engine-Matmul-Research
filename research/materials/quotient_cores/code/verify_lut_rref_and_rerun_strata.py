#!/usr/bin/env python3
"""analysis: Verify LUT RREF property and rerun all 38 matching strata profiles.

Critical question: analysis claimed analysis's make_pivot_dict/in_span_piv was
buggy because "non-echelon bases sharing the same highest bit" cause collisions.
But if the LUT stores keys produced by rref_key() → rref_basis() → pack_basis(),
then all unpacked bases ARE in RREF and have distinct highest bits, so
make_pivot_dict is correct.

This script:
1. Loads the full 8,283,458-row LUT
2. Verifies every key has RREF basis (unique highest bits, reduced echelon)
3. Spot-checks in_span_piv vs span_of on random samples
4. Reruns process_stratum for all 38 matching strata with the same functions
5. Reports the corrected residual profile

If the RREF property holds, the old matching strata work from earlier analysis
was actually correct all along, and "15/38 closed" is still valid.
"""
from __future__ import annotations
import json
import pickle
import random
import sys
import time
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

from wang_capacity_lazy import unpack_basis, rref_basis, pack_basis, subspace_points_from_basis

N = 9
MASK_ALL = (1 << N) - 1

# ── Reproduce analysis helpers exactly ──
def make_pivot_dict(basis: Sequence[int]) -> Dict[int, int]:
    return {int(b).bit_length() - 1: int(b) for b in basis if int(b)}

def in_span_piv(piv: Dict[int, int], v: int) -> bool:
    x = int(v)
    while x:
        p = x.bit_length() - 1
        b = piv.get(p)
        if b is None:
            return False
        x ^= b
    return True

# ── Reference span via full enumeration ──
def span_of(basis: Sequence[int]) -> frozenset:
    s = {0}
    for b in basis:
        s |= {x ^ b for x in s}
    return frozenset(s)

def verify_lut_rref(lut: Dict[int, int]):
    """Check that every LUT key encodes an RREF basis."""
    violations = 0
    checked = 0
    for key in lut:
        basis = unpack_basis(key)
        checked += 1
        # 1. Each vector must be nonzero
        for b in basis:
            if b == 0:
                violations += 1
                if violations <= 5:
                    print(f"  ZERO vector in key {hex(key)}: basis={basis}")
                continue
        # 2. Highest bits must be distinct
        hbits = [int(b).bit_length() - 1 for b in basis if b]
        if len(set(hbits)) != len(hbits):
            violations += 1
            if violations <= 5:
                print(f"  DUPLICATE highest bits in key {hex(key)}: hbits={hbits}, basis={[hex(b) for b in basis]}")
            continue
        # 3. Reduced: for each pivot p, no other vector has bit p set
        for i, bi in enumerate(basis):
            pi = int(bi).bit_length() - 1
            for j, bj in enumerate(basis):
                if j != i and ((int(bj) >> pi) & 1):
                    violations += 1
                    if violations <= 5:
                        print(f"  NON-REDUCED in key {hex(key)}: vector {j} has bit {pi} of pivot {i}")
                    break
        # 4. Round-trip: pack(rref(basis)) == key
        rt_key = pack_basis(rref_basis(basis))
        if rt_key != key:
            violations += 1
            if violations <= 5:
                print(f"  ROUNDTRIP fail: key={hex(key)}, rt={hex(rt_key)}")
    print(f"RREF check: {checked} keys, {violations} violations")
    return violations

def spot_check_membership(lut: Dict[int, int], n_samples=10000):
    """Compare in_span_piv vs span_of on random key/point pairs."""
    keys = list(lut.keys())
    mismatches = 0
    for _ in range(n_samples):
        key = random.choice(keys)
        basis = unpack_basis(key)
        piv = make_pivot_dict(basis)
        sp = span_of(basis)
        pt = random.randint(1, MASK_ALL)
        a = in_span_piv(piv, pt)
        b = (pt in sp)
        if a != b:
            mismatches += 1
            if mismatches <= 3:
                print(f"  MISMATCH: key={hex(key)}, pt={pt}, piv={a}, span={b}, basis={basis}")
    print(f"Spot check: {n_samples} samples, {mismatches} mismatches")
    return mismatches

def process_stratum_correct(lut: Dict[int, int], matching: Sequence[int], hr_set: set, hr_list: Sequence[int]):
    """Same as analysis's process_stratum, reproduced for verification."""
    matching = [int(x) for x in matching]
    k = len(matching)
    target = 20 - k
    lb_min = max(20 - k - 1, 0)

    vertex_key: Dict[int, int] = {}
    edge_key: Dict[Tuple[int, int], int] = {}
    impossible = []
    row_counts = {'filtered': 0, 'res_neg': 0, 'res0': 0, 'res1': 0}

    for key, lb in lut.items():
        if lb < lb_min:
            continue
        cap = 20 - lb
        needed_for_le1 = cap - 1
        if needed_for_le1 > k:
            continue
        row_counts['filtered'] += 1

        basis = unpack_basis(key)
        piv = make_pivot_dict(basis)

        cnt = 0
        for mi, m in enumerate(matching):
            if in_span_piv(piv, m):
                cnt += 1
            if cnt + (k - mi - 1) < needed_for_le1:
                break
        else:
            pass
        if cnt + (k - mi - 1) < needed_for_le1:
            continue

        residual = cap - cnt
        if residual < 0:
            row_counts['res_neg'] += 1
            impossible.append({'key': int(key), 'lb': int(lb), 'cap': int(cap), 'matching_count': int(cnt)})
            continue

        pts = [int(x) for x in subspace_points_from_basis(basis) if int(x) in hr_set]
        if residual == 0:
            row_counts['res0'] += 1
            for h in pts:
                vertex_key.setdefault(h, int(key))
        elif residual == 1:
            row_counts['res1'] += 1
            for i, a in enumerate(pts):
                for b in pts[i+1:]:
                    x, y = (a, b) if a < b else (b, a)
                    edge_key.setdefault((x, y), int(key))

    survivors = [int(h) for h in hr_list if int(h) not in vertex_key]
    ss = set(survivors)
    survivor_edges = {str(p): key for p, key in edge_key.items() if p[0] in ss and p[1] in ss}
    return {
        'target': target,
        'impossible_row_count': len(impossible),
        'vertex_excluded': len(vertex_key),
        'survivor_count': len(survivors),
        'survivor_edge_count': len(survivor_edges),
        'row_counts': row_counts,
    }


def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--lut', default='data/wang_f2_lb20/wang_subspace_lut.pkl')
    parser.add_argument('--strata', default='data/matching_strata/anchored_matching_strata.json')
    parser.add_argument('--out', default='data/lut_verify_and_strata/results.json')
    parser.add_argument('--spot-samples', type=int, default=100000)
    args = parser.parse_args()

    out_dir = Path(args.out).parent
    out_dir.mkdir(parents=True, exist_ok=True)

    print(f"Loading LUT {args.lut}...")
    t0 = time.time()
    with open(args.lut, 'rb') as f:
        data = pickle.load(f)
    lut = {int(k): int(v) for k, v in data['lut'].items()}
    print(f"  {len(lut)} rows, {time.time()-t0:.1f}s")

    # 1. Verify RREF property
    print("\n=== RREF Verification ===")
    rref_violations = verify_lut_rref(lut)

    # 2. Spot-check membership
    print(f"\n=== Spot-check membership ({args.spot_samples} samples) ===")
    membership_mismatches = spot_check_membership(lut, args.spot_samples)

    # 3. Load strata and higher-rank point set
    print("\n=== Loading strata ===")
    with open(args.strata) as f:
        strata_data = json.load(f)

    # Higher-rank points: all nonzero 9-bit except rank-1 matrices
    rank1_pts = set()
    for u in range(1, 8):
        for v in range(1, 8):
            m = 0
            for i in range(3):
                if (u >> i) & 1:
                    m |= v << (3 * i)
            rank1_pts.add(m)
    assert len(rank1_pts) == 49
    hr_set = set(range(1, 512)) - rank1_pts
    hr_list = sorted(hr_set)
    print(f"  rank-1 points: {len(rank1_pts)}, higher-rank: {len(hr_set)}")

    # 4. Run all 38 strata
    print("\n=== Running all 38 matching strata ===")
    strata_results = []
    idx = 0
    for k_str in sorted(strata_data['representatives_by_k'], key=int):
        for rep in strata_data['representatives_by_k'][k_str]:
            matching = rep['canonical']
            k = int(rep['k'])
            t1 = time.time()
            profile = process_stratum_correct(lut, matching, hr_set, hr_list)
            elapsed = time.time() - t1
            status = 'impossible' if profile['impossible_row_count'] > 0 else \
                     'zero_survivors' if profile['survivor_count'] == 0 else 'open'
            result = {
                'idx': idx,
                'k': k,
                'matching': matching,
                'status': status,
                'target_hr_points': profile['target'],
                'impossible_row_count': profile['impossible_row_count'],
                'vertex_excluded': profile['vertex_excluded'],
                'survivor_count': profile['survivor_count'],
                'survivor_edge_count': profile['survivor_edge_count'],
                'row_counts': profile['row_counts'],
                'elapsed_sec': round(elapsed, 2),
            }
            strata_results.append(result)
            tag = '✗' if status == 'impossible' else ('✓' if status == 'zero_survivors' else '?')
            print(f"  [{tag}] idx{idx:02d} k={k} matching={matching} "
                  f"survivors={profile['survivor_count']} edges={profile['survivor_edge_count']} "
                  f"({elapsed:.1f}s)")
            idx += 1

    # Summarize
    closed_count = sum(1 for r in strata_results if r['status'] != 'open')
    open_count = sum(1 for r in strata_results if r['status'] == 'open')
    impossible_count = sum(1 for r in strata_results if r['status'] == 'impossible')
    zero_surv_count = sum(1 for r in strata_results if r['status'] == 'zero_survivors')

    summary = {
        'rref_violations': rref_violations,
        'membership_mismatches': membership_mismatches,
        'lut_rows': len(lut),
        'spot_check_samples': args.spot_samples,
        'strata_count': len(strata_results),
        'closed_by_impossible': impossible_count,
        'closed_by_zero_survivors': zero_surv_count,
        'open': open_count,
        'total_closed_direct': closed_count,
        'strata': strata_results,
    }

    Path(args.out).write_text(json.dumps(summary, indent=2) + '\n')
    print(f"\n=== Summary ===")
    print(f"RREF violations: {rref_violations}")
    print(f"Membership mismatches: {membership_mismatches}")
    print(f"Strata: {len(strata_results)} total, {closed_count} closed directly, {open_count} open")
    print(f"  impossible (neg residual): {impossible_count}")
    print(f"  zero survivors: {zero_surv_count}")
    print(f"Saved to {args.out}")

if __name__ == '__main__':
    main()
