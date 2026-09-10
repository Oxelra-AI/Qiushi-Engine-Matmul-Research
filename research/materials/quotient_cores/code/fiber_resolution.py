#!/usr/bin/env python3
"""analysis: exact fiber-based resolution of d<k cancellation cases.

For a retained span L, E=pi(col(D)) with dim d, and k repair slots with d<k,
a rank-22 repair exists iff some subspace H of Q/E with dim(H)<=k-d satisfies
  span(S inter rho^{-1}(H)) = rho^{-1}(H)
where S is the set of quotient images of rank-one matrices and rho:Q->Q/E.

For slack one (k-d=1), H is either {0} (the existing intersection test) or
{0,z} for one nonzero outside direction z.  Group attainable images into fibers
F_z = {s in S : rho(s)=z}.  For the zero case, F_0 must span E.  For each
nonzero fiber F_z, choose any s_0 in F_z; then success iff
  span(F_0 union {s+s_0 : s in F_z}) = E.

All differences s+s_0 lie in E, so the test uses only d-dimensional tag algebra.
A successful test recovers explicit (a,b) representatives and solves C globally.

Positive controls: for the known rank-23 scheme, deleting k+1 terms gives a
retained block where the original terms should be recoverable by the fiber test
when the block is slack-one.

review deduplication: the same retained complement appears k+1 times across
different first-deletion choices, so we group by retained set before testing.
"""
from __future__ import annotations
import argparse, itertools, json, sys, time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, FrozenSet, List, Optional, Sequence, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
import residual_repair_geometry as rg
from ab_residual_block_search import build_final_and_verify
from free_ab_k_scan_corrected import canonical_reduce

OUTDIR = Path('data/fiber')


def popcnt(x: int) -> int:
    return bin(x).count('1')


def tags_rank(tags) -> int:
    return rg.tags_rank(tags)


def fiber_test(tagged_basis: Dict[int, Tuple[int, int]], d: int, k: int,
               ) -> Tuple[str, Optional[dict], dict]:
    """Full fiber test for one retained block.

    Returns (status, witness_info_or_None, stats).
    status is one of:
      'E_SPAN_OK'      -- F_0 alone spans E (usual d=k test succeeds for a d<k block)
      'FIBER_OK'       -- some outside fiber z gives a spanning combination
      'NO_FIBER_COVER' -- exhausted all fibers, none spans E
    """
    # Enumerate all rank-one quotient images
    fibers: Dict[int, Dict[int, Tuple[int, int]]] = defaultdict(dict)
    # fibers[remainder][tag] = (a, b) -- first representative for that tag
    for a in range(1, 512):
        for beta in range(9):
            b_elem = 1 << beta
            v = rg.vec_mask9_to_outer81(a, b_elem)
            rem, tag = canonical_reduce(tagged_basis, v)
            if tag not in fibers[rem]:
                fibers[rem][(tag, beta)] = None  # placeholder, build tag->rep later

    # Actually we need (a, b_full) representatives; use the kernel approach
    # for efficiency: for fixed a, find all b with given (rem, tag).
    fibers2: Dict[int, Dict[int, Tuple[int, int]]] = defaultdict(dict)
    # fibers2[rem][tag] = (a, b)
    # BUG FIX (analysis review): must include tag=0 entries for nonzero rem.
    # Only (rem=0, tag=0) is the true zero quotient vector and should be excluded.
    for a in range(1, 512):
        for b in range(1, 512):
            v = rg.vec_mask9_to_outer81(a, b)
            rem, tag = canonical_reduce(tagged_basis, v)
            if (rem != 0 or tag != 0) and tag not in fibers2[rem]:
                fibers2[rem][tag] = (a, b)

    stats = {
        'total_fibers': len(fibers2),
        'F0_size': len(fibers2.get(0, {})),
    }

    # F_0: rank-one images in L+E
    F0_tags = list(fibers2.get(0, {}).keys())
    F0_rank = tags_rank(F0_tags)
    stats['F0_rank'] = F0_rank

    if F0_rank >= d:
        # F_0 already spans E (would have been caught by d=k test)
        reps = []
        piv: Dict[int, int] = {}
        for tag in F0_tags:
            x = int(tag)
            while x:
                p = x.bit_length() - 1
                if p in piv:
                    x ^= piv[p]
                else:
                    piv[p] = x
                    a, b = fibers2[0][tag]
                    reps.append((a, b, tag))
                    break
            if len(reps) >= d:
                break
        return 'E_SPAN_OK', {'reps': reps}, stats

    # Test each nonzero outside fiber
    nonzero_rems = sorted(r for r in fibers2 if r != 0 and fibers2[r])
    stats['nonzero_fiber_count'] = len(nonzero_rems)

    best_combined = F0_rank
    for rem in nonzero_rems:
        fiber_z = fibers2[rem]  # tag -> (a, b)
        if not fiber_z:
            continue
        # Pick a reference s_0 from F_z
        ref_tag = next(iter(fiber_z))
        ref_a, ref_b = fiber_z[ref_tag]
        # Differences: for each (tag, (a,b)) in F_z, diff = tag XOR ref_tag lies in E
        diff_tags = set()
        for tag in fiber_z:
            diff = tag ^ ref_tag
            if diff:
                diff_tags.add(diff)
        # Combined: F_0 tags union diff_tags
        combined_tags = list(set(F0_tags) | diff_tags)
        combined_rank = tags_rank(combined_tags)
        if combined_rank > best_combined:
            best_combined = combined_rank
        if combined_rank >= d:
            # Success! Extract d representatives
            # Need: d independent tags from combined, with lift to (a,b).
            # Build a basis from F_0 and diffs.
            reps: List[Tuple[int, int, int]] = []
            piv2: Dict[int, int] = {}
            # First try F_0 tags (they need one slot each)
            for tag in F0_tags:
                x = int(tag)
                while x:
                    p = x.bit_length() - 1
                    if p in piv2:
                        x ^= piv2[p]
                    else:
                        piv2[p] = x
                        a, b = fibers2[0][tag]
                        reps.append((a, b, tag))
                        break
                if len(reps) >= d:
                    break
            if len(reps) < d:
                # Add from diffs (each diff tag comes from a F_z element + reference)
                for diff_tag in diff_tags:
                    x = int(diff_tag)
                    while x:
                        p = x.bit_length() - 1
                        if p in piv2:
                            x ^= piv2[p]
                        else:
                            piv2[p] = x
                            # The diff came from tag = diff_tag ^ ref_tag
                            orig_tag = diff_tag ^ ref_tag
                            if orig_tag in fiber_z:
                                a, b = fiber_z[orig_tag]
                            else:
                                a, b = ref_a, ref_b  # fallback (shouldn't happen)
                            reps.append((a, b, orig_tag))
                            break
                    if len(reps) >= d:
                        break
            if len(reps) < d:
                # Need the reference element itself
                reps.append((ref_a, ref_b, ref_tag))

            # We need k = d+1 rank-one columns to span ρ^{-1}({0,z}).
            # d columns span E (from the independent tags above)
            # 1 column with outside component z (the reference or any F_z element)
            # Make sure the reference is included if not already
            all_used = {tag for _a, _b, tag in reps}
            if ref_tag not in all_used:
                reps.append((ref_a, ref_b, ref_tag))

            return 'FIBER_OK', {
                'rem': int(rem),
                'ref_tag': int(ref_tag),
                'ref_ab': (int(ref_a), int(ref_b)),
                'diff_count': len(diff_tags),
                'combined_rank': combined_rank,
                'reps': [(int(a), int(b), int(t)) for a, b, t in reps],
            }, stats

    stats['best_combined_rank'] = best_combined
    return 'NO_FIBER_COVER', None, stats


def resolve_blocks(name: str, terms: Sequence[Tuple[int, int, int]],
                   D_cols: Sequence[int], k: int,
                   positive_control: bool = True) -> dict:
    """Resolve all d<k blocks from a k-slot deletion scan."""
    n = len(terms)
    # Group by retained set to avoid redundant tests
    retained_to_blocks: Dict[FrozenSet[int], List[Tuple[int, ...]]] = defaultdict(list)
    for del_idx in range(n):
        for block in itertools.combinations(
                [i for i in range(n) if i != del_idx][:n-1], k):
            removed = frozenset({del_idx}) | frozenset(block)
            retained = frozenset(range(n)) - removed
            retained_to_blocks[retained].append((del_idx,) + block)

    results = {
        'source': name, 'k': k, 'n_terms': n,
        'unique_retained_sets': 0, 'tested': 0,
        'status_hist': Counter(),
        'witnesses': [],
        'details': [],
        'positive_controls': [],
    }

    # Positive control: take blocks from the rank-23 scheme where original
    # removed columns have d<k and check that the fiber test recovers them
    if positive_control:
        pc_tested = 0; pc_ok = 0; pc_d_eq_k = 0
        for removed_set_tuple in itertools.combinations(range(n), k + 1):
            removed_set = frozenset(removed_set_tuple)
            retained_set = frozenset(range(n)) - removed_set
            retained_cols = [rg.vec_mask9_to_outer81(terms[i][0], terms[i][1])
                             for i in sorted(retained_set)]
            tagged, E_reps, rank_L, d = rg.build_quotient_basis(retained_cols, D_cols)
            if d == k + 1:
                continue  # d = removed count, always the case for independent cols
            if d < k:
                # This is a slack-one case (since d = k+1 - excess but d < k means
                # the removed cols had dependencies modulo retained)
                pc_tested += 1
                status, info, stats = fiber_test(tagged, d, k)
                ok = status in ('E_SPAN_OK', 'FIBER_OK')
                if ok:
                    pc_ok += 1
                results['positive_controls'].append({
                    'removed': sorted(removed_set),
                    'd': d, 'k': k, 'status': status,
                    'ok': ok, 'stats': stats
                })
            elif d == k:
                pc_d_eq_k += 1
        results['pc_tested'] = pc_tested
        results['pc_ok'] = pc_ok
        results['pc_d_eq_k_skipped'] = pc_d_eq_k

    # Now test actual d<k blocks from the deletion scan
    seen_retained: set = set()
    for del_idx in range(n):
        seed_terms = list(terms[:del_idx] + terms[del_idx + 1:])
        for block in itertools.combinations(range(n - 1), k):
            # Map block indices back to original term indices
            orig_indices = [i if i < del_idx else i + 1 for i in block]
            removed = frozenset({del_idx}) | frozenset(orig_indices)
            retained = frozenset(range(n)) - removed
            if retained in seen_retained:
                continue
            seen_retained.add(retained)

            retained_cols = [rg.vec_mask9_to_outer81(terms[i][0], terms[i][1])
                             for i in sorted(retained)]
            tagged, E_reps, rank_L, d = rg.build_quotient_basis(retained_cols, D_cols)
            if d >= k:
                continue  # not a d<k case

            results['unique_retained_sets'] += 1
            results['tested'] += 1
            status, info, stats = fiber_test(tagged, d, k)
            results['status_hist'][status] += 1

            detail = {
                'retained': sorted(retained),
                'removed': sorted(removed),
                'd': d, 'k': k, 'rank_L': rank_L,
                'status': status,
                'stats': stats,
            }

            if status in ('E_SPAN_OK', 'FIBER_OK') and info:
                # Try to build actual A/B and verify
                reps = info.get('reps', [])
                A_choices = [a for a, b, t in reps]
                B_choices = [b for a, b, t in reps]
                # Use the first (k+1) deleted terms as slots
                removed_sorted = sorted(removed)
                # Rebuild seed_terms for verification
                retained_sorted = sorted(retained)
                retained_terms = [terms[i] for i in retained_sorted]
                # Build full 22-term A,B lists
                A_full = [terms[i][0] for i in retained_sorted]
                B_full = [terms[i][1] for i in retained_sorted]
                # Add repair terms
                for a, b, t in reps[:k]:
                    A_full.append(a)
                    B_full.append(b)
                if len(A_full) >= 22:
                    from linear_completion import (
                        build_t333_f2, tensor_to_D, gf2_solve_multi, vec_to_mask,
                        verify_decomposition_f2,
                    )
                    cols = [rg.vec_mask9_to_outer81(a, b) for a, b in zip(A_full[:22], B_full[:22])]
                    K = rg.build_K_np_from_int_cols(cols)
                    D_np = tensor_to_D(build_t333_f2())
                    CT = gf2_solve_multi(K, D_np)
                    if CT is not None:
                        C_full = [vec_to_mask(CT[i]) for i in range(22)]
                        diff = verify_decomposition_f2(list(A_full[:22]), list(B_full[:22]), C_full)
                        detail['brent_diff'] = int(diff)
                        if diff == 0:
                            witness = {
                                'A': list(map(int, A_full[:22])),
                                'B': list(map(int, B_full[:22])),
                                'C': list(map(int, C_full)),
                                'brent_diff': 0,
                            }
                            results['witnesses'].append(witness)
                            detail['witness'] = True
                    else:
                        detail['brent_diff'] = -1  # solve failed

            if info:
                detail['info'] = {k: v for k, v in info.items() if k != 'reps'}
            results['details'].append(detail)

    results['status_hist'] = dict(results['status_hist'])
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--sources', default='cn122_qmm')
    ap.add_argument('--k', type=int, default=3)
    ap.add_argument('--outdir', type=Path, default=OUTDIR)
    ap.add_argument('--no-positive-control', action='store_true')
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    sources = rg.load_sources()
    D_cols = rg.D_columns_as_ints()
    out = {
        'schema': 's0908_fiber_resolution_v1',
        'meaning': ('Exact fiber-based resolution of d<k cancellation cases in '
                    'the free A/B retained-neighborhood scan.  For slack-one cases '
                    '(k-d=1), tests all outside fibers to determine whether any '
                    'combination of rank-one images spans the required subspace.  '
                    'A witness is a full rank-22 decomposition verified on all Brent '
                    'equations; absence excludes all A/B replacements in the given '
                    'retained-column neighborhood, including cancellation-bearing ones.'),
        'k': args.k,
        'results': {},
        'witnesses': [],
    }
    for name in [x.strip() for x in args.sources.split(',') if x.strip()]:
        if name not in sources:
            print(f'missing {name}', flush=True)
            continue
        print(f'=== fiber resolution {name} k={args.k} ===', flush=True)
        r = resolve_blocks(name, sources[name], D_cols, args.k,
                           positive_control=not args.no_positive_control)
        out['results'][name] = r
        out['witnesses'].extend(r['witnesses'])
        print(json.dumps({
            'source': name,
            'unique_retained_sets': r['unique_retained_sets'],
            'tested': r['tested'],
            'status_hist': r['status_hist'],
            'witnesses': len(r['witnesses']),
            'pc_tested': r.get('pc_tested'),
            'pc_ok': r.get('pc_ok'),
        }, indent=2, sort_keys=True), flush=True)
    out['elapsed_sec'] = time.time() - t0
    op = args.outdir / f'fiber_resolution_k{args.k}.json'
    op.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'ok', 'out': str(op), 'witnesses': len(out['witnesses']),
                      'elapsed_sec': out['elapsed_sec']}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
