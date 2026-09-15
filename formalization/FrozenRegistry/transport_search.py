"""Find exact transports to existing proved spaces; Lean checks every witness."""
import argparse
import json
from pathlib import Path
import sys
from functools import lru_cache
from itertools import combinations

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from generate_certificate import actions, rref, span


def canonical_rows(images):
    rows = images.copy()
    n, d = rows.shape
    index = np.arange(n)
    rank = np.zeros(n, dtype=np.int64)
    columns = np.arange(d)
    for bit in range(8, -1, -1):
        possible = ((rows >> bit) & 1).astype(bool) & (columns >= rank[:, None])
        found = possible.any(axis=1)
        chosen = possible.argmax(axis=1)
        selected = index[found]
        old = rows[selected, rank[found]].copy()
        rows[selected, rank[found]] = rows[selected, chosen[found]]
        rows[selected, chosen[found]] = old
        pivot = rows[index, np.minimum(rank, d - 1)]
        eliminate = (((rows >> bit) & 1).astype(bool) & found[:, None]
                     & (columns != rank[:, None]))
        rows ^= np.where(eliminate, pivot[:, None], 0).astype(np.uint16)
        rank += found
    assert np.all(rank == d)
    return rows


def packed(basis):
    return sum(int(c) << (9 * i) for i, c in enumerate(basis))


def packed_rows(rows):
    if rows.shape[1] > 7:
        return np.array([packed(row) for row in rows], dtype=object)
    return np.sum(rows.astype(np.uint64) <<
                  (9 * np.arange(rows.shape[1], dtype=np.uint64)), axis=1)


@lru_cache(maxsize=None)
def coefficient_spaces(n, d):
    result = []
    for pivot_set in combinations(range(n), d):
        pivots = list(reversed(pivot_set))
        free = [(i, j) for i, p in enumerate(pivots)
                for j in range(p) if j not in pivots]
        for mask in range(1 << len(free)):
            rows = [1 << p for p in pivots]
            for bit, (i, j) in enumerate(free):
                if mask >> bit & 1:
                    rows[i] |= 1 << j
            result.append(rows)
    return np.array(result, dtype=np.uint16)


def search(candidates, remaining, containment=False):
    ps, qs, qis, table, trans = actions()
    by_dimension = {}
    for c in candidates:
        if c['basis'] is None:
            continue
        basis = rref(c['basis'])
        by_key = by_dimension.setdefault(len(basis), {})
        key = packed(basis)
        old = by_key.get(key)
        if old is None or (c['bound'], -len(c['theorem'])) > (old['bound'], -len(old['theorem'])):
            by_key[key] = c
    if containment:
        minima = {}
        for rep in remaining:
            d = len(rref(rep['basis']))
            minima[d] = min(minima.get(d, rep['lb']), rep['lb'])
        sources = [(d, c) for d, group in by_dimension.items() for c in group.values()]
        for d, lower in sorted(minima.items(), reverse=True):
            options = by_dimension.setdefault(d, {})
            for n, c in sources:
                if n <= d or c['bound'] < lower:
                    continue
                basis = tuple(reversed(rref(c['basis'])))
                images = np.zeros(1 << n, dtype=np.uint16)
                for mask in range(1, 1 << n):
                    low = mask & -mask
                    images[mask] = images[mask ^ low] ^ basis[low.bit_length() - 1]
                subspaces = images[coefficient_spaces(n, d)]
                assert all(tuple(row) == rref(row) for row in subspaces[:5])
                keys = packed_rows(subspaces)
                for key in keys:
                    key = int(key)
                    old = options.get(key)
                    if old is None or old['bound'] < c['bound']:
                        options[key] = c
            print('Containment options', d, len(options), flush=True)
    results = []
    for rep in remaining:
        d = len(rref(rep['basis']))
        assert 1 <= d <= 9
        options = {k: c for k, c in by_dimension.get(d, {}).items() if c['bound'] >= rep['lb']}
        hit = None
        for flip in [False, True]:
            basis = trans[rep['basis']] if flip else rep['basis']
            images = canonical_rows(table[:, basis])
            keys = packed_rows(images)
            idx = next((i for i, k in enumerate(keys) if int(k) in options), None)
            if idx is None:
                continue
            candidate = options[int(keys[idx])]
            action = table[idx, trans] if flip else table[idx]
            inverse = np.argsort(action)
            target = [int(c) for c in images[idx]]
            pairs = [[c, int(inverse[c])] for c in target]
            assert all(b in span(rep['basis']) and action[b] == a for a, b in pairs)
            assert rref(action[rep['basis']]) == tuple(target)
            assert all(c in span(candidate['basis']) for c in target)
            hit = dict(rep, candidate=candidate, witness={
                'P': int(ps[idx]), 'Q': int(qs[idx]), 'Qinv': int(qis[idx]),
                'flip': flip, 'pairs': pairs})
            break
        results.append(hit or dict(rep, reason='no_adequate_exact_orbit_match_in_candidate_pool'))
        print(rep['index'], candidate['theorem'] if hit else 'unmatched', flush=True)
    return results


def emit(results, path):
    from generate_certificate import literal
    lines = ['import FrozenRegistry.Bridge', '',
             'set_option maxHeartbeats 16000000', 'set_option maxRecDepth 100000', '',
             'namespace QiushiMatmul.FrozenRegistry.Transport', '']
    names = []
    for row in results:
        if 'witness' not in row:
            continue
        i, w, c = row['index'], row['witness'], row['candidate']
        target = [a for a, _ in w['pairs']]
        pairs = '[' + ', '.join(f'({a}, {b})' for a, b in w['pairs']) + ']'
        name = f'bound{i:03}'
        names.append(name)
        lines += [f'theorem orbit{i:03} :',
                  f'    frozenWangTable.OrbitImage {i} (spanCodes {literal(target)}) := by',
                  f'  exact frozenOrbitImage_of_code_transport frozenWangTable {i} {pairs}',
                  f'    (codeMat {w["P"]}) (codeMat {w["Q"]}) (codeMat {w["Qinv"]}) {str(w["flip"]).lower()}',
                  '    (by decide) (by decide) (by decide)',
                  f'    (by rw [show frozenWangTable.basis {i} = {literal(row["basis"])} by decide]; decide)',
                  f'    (by rw [show frozenWangTable.basis {i} = {literal(row["basis"])} by decide]; decide)', '',
                  f'theorem {name} :',
                  f'    QuotientRankAtLeast (spanCodes (frozenWangTable.basis {i}))',
                  f'      (frozenWangTable.lower {i}) := by',
                  f'  have h := {c["theorem"]}',
                  f'  change QuotientRankAtLeast (spanCodes {literal(c["basis"])}) {c["bound"]} at h',
                  f'  have htarget := bind_contained {literal(target)} {literal(c["basis"])}',
                  '    h (by decide) (Nat.le_refl _)',
                  f'  exact bind_orbit frozenWangTable {i} orbit{i:03} htarget (by decide)', '']
    lines += ['end QiushiMatmul.FrozenRegistry.Transport', '', 'run_cmd do',
              '  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]',
              '  for name in #[' + ', '.join('``QiushiMatmul.FrozenRegistry.Transport.' + n for n in names) + '] do',
              '    let axioms ← Lean.collectAxioms name',
              '    for ax in axioms do', '      unless allowed.contains ax do',
              '        throwError "Unexpected axiom {ax} in {name}"',
              '    Lean.logInfo m!"TRANSPORT_AXIOMS {name}: {axioms}"',
              f'  Lean.logInfo "TRANSPORT_CHECKED {len(names)}"', '']
    path.write_text('\n'.join(lines))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidates', type=Path, required=True)
    parser.add_argument('--remaining', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--containment', action='store_true')
    parser.add_argument('--emit', type=Path)
    args = parser.parse_args()
    results = search(json.loads(args.candidates.read_text()), json.loads(args.remaining.read_text()), args.containment)
    args.output.write_text(json.dumps(results, indent=2) + '\n')
    if args.emit:
        emit(results, args.emit)
    print(json.dumps({'matched': sum('witness' in r for r in results),
                      'unmatched': [r['index'] for r in results if 'witness' not in r]}), flush=True)


if __name__ == '__main__':
    main()
