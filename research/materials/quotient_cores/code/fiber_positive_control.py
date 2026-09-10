#!/usr/bin/env python3
"""analysis: positive control for the fiber test using synthetic d<k examples.

We construct scenarios where a known repair exists and verify the fiber test
finds it.  The approach: take the cn122 rank-23 span, which has 29 rank-one
matrices.  Take a set of m<22 of them as "retained", ensure the quotient E has
dim d < m_repair = m_total - m_retained = k, then verify the fiber test finds
the known remaining rank-one columns.

Test 1 (d=k control): Retain 21 cn122 columns, k=2, d should be 2.
Test 2 (synthetic d<k): Find a retained set where d < k by picking
columns whose quotient directions partially overlap with W.
"""
from __future__ import annotations
import itertools, json, sys, time
from pathlib import Path
from typing import Dict, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
import residual_repair_geometry as rg
from fiber_resolution import fiber_test
from free_ab_k_scan_corrected import canonical_reduce


OUTDIR = Path('data/fiber')


def main():
    t0 = time.time()
    sources = rg.load_sources()
    D_cols = rg.D_columns_as_ints()
    terms = sources['cn122_qmm']
    n = len(terms)
    results = []

    # Test 1: d=k controls (should find repair = original removed columns)
    print("=== d=k positive controls ===")
    for k in [1, 2]:
        ok = 0
        tested = 0
        for block in itertools.combinations(range(n), k):
            retained_idx = [i for i in range(n) if i not in block]
            retained_cols = [rg.vec_mask9_to_outer81(terms[i][0], terms[i][1])
                             for i in retained_idx]
            tagged, E_reps, rank_L, d = rg.build_quotient_basis(retained_cols, D_cols)
            if d != k:
                continue
            tested += 1
            status, info, stats = fiber_test(tagged, d, k)
            if status in ('E_SPAN_OK', 'FIBER_OK'):
                ok += 1
            if tested <= 3:
                print(f"  k={k}, block={block}, d={d}, status={status}, "
                      f"F0_rank={stats.get('F0_rank')}")
        print(f"  k={k}: {ok}/{tested} d=k controls pass fiber test")
        results.append({'test': f'd_eq_k_control_k{k}', 'ok': ok, 'tested': tested})

    # Test 2: find d<k blocks and check fiber test
    print("\n=== d<k census and fiber test ===")
    for k in [2, 3, 4]:
        d_lt_k_blocks = []
        for block in itertools.combinations(range(n), k + 1):
            retained_idx = [i for i in range(n) if i not in block]
            retained_cols = [rg.vec_mask9_to_outer81(terms[i][0], terms[i][1])
                             for i in retained_idx]
            tagged, E_reps, rank_L, d = rg.build_quotient_basis(retained_cols, D_cols)
            if d < k:
                d_lt_k_blocks.append((block, d, rank_L, tagged))
                if len(d_lt_k_blocks) >= 20:
                    break
        print(f"  k={k}: found {len(d_lt_k_blocks)} d<k blocks from C({n},{k+1})")
        fiber_ok = 0
        for block, d, rank_L, tagged in d_lt_k_blocks[:10]:
            status, info, stats = fiber_test(tagged, d, k)
            if status in ('E_SPAN_OK', 'FIBER_OK'):
                fiber_ok += 1
            if len(d_lt_k_blocks) <= 5:
                print(f"    block={block}, d={d}, k={k}, status={status}, "
                      f"F0_rank={stats.get('F0_rank')}, "
                      f"best={stats.get('best_combined_rank')}")
        results.append({
            'test': f'd_lt_k_fiber_k{k}',
            'total_found': len(d_lt_k_blocks),
            'tested': min(10, len(d_lt_k_blocks)),
            'fiber_ok': fiber_ok
        })

    # Test 3: synthetic control - use the 6 extra rank-ones in cn122 span
    # If we remove 2 original columns that share an A-value and add the extra
    # rank-one (their sum), we know a "repair" exists.  Build the quotient and
    # verify the fiber test sees the extra rank-one.
    print("\n=== Synthetic fiber control: known extra rank-ones ===")
    # Load rank-one list from lattice analysis
    lat = json.load(open(OUTDIR.parent / 'rankone_lattice' / 'cn122' / 'rankone_lattice_dim22.json'))
    ro_list = lat['results']['cn122_qmm']['rank_one_list_head']
    extra = [(a, b, t) for a, b, t in ro_list if bin(t).count('1') > 1]
    print(f"  Extra rank-ones (sum of 2 original): {len(extra)}")
    for a, b, t in extra:
        bits = [i for i in range(23) if (t >> i) & 1]
        # These two columns sum to (a, b) which is rank-one
        retained_idx = [i for i in range(23) if i not in bits]
        retained_cols = [rg.vec_mask9_to_outer81(terms[i][0], terms[i][1])
                         for i in retained_idx]
        tagged, E_reps, rank_L, d = rg.build_quotient_basis(retained_cols, D_cols)
        # Since we removed exactly 2 columns, d should be 2.
        # But these 2 columns sum to a rank-one in the span, so the quotient
        # direction of their sum is zero (it's in the retained span + E).
        # Actually, the extra rank-one IS their sum, and it's in the span of
        # all 23 columns.  Since we removed exactly the two columns that
        # constitute this extra, and the extra is in the original 23-dim span,
        # the extra rank-one might or might not be in L+E.
        # Test:
        v_extra = rg.vec_mask9_to_outer81(a, b)
        rem, tag = canonical_reduce(tagged, v_extra)
        # k=2 removed columns, d should be <=2
        status, info, stats = fiber_test(tagged, d, 2)
        print(f"  removed={bits}, extra a={a} b={b}, d={d}, "
              f"extra_rem={'0' if rem==0 else 'nonzero'}, "
              f"fiber: {status}, F0_rank={stats.get('F0_rank')}")
        results.append({
            'test': 'synthetic_extra_rankone',
            'removed': bits,
            'extra_ab': [a, b],
            'd': d,
            'extra_in_L_plus_E': rem == 0,
            'fiber_status': status,
        })

    out = {
        'schema': 's0908_fiber_positive_control_v1',
        'results': results,
        'elapsed_sec': time.time() - t0,
    }
    op = OUTDIR / 'fiber_positive_control.json'
    op.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(f"\nSaved: {op}")
    print(json.dumps({'elapsed_sec': out['elapsed_sec']}, indent=2))


if __name__ == '__main__':
    main()
