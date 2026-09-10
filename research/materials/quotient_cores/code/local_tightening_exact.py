#!/usr/bin/env python3
"""analysis: exact local capacity tightening by child-row compatibility search.

Given an E11WANG1 row system with trusted capacities, test parent rows U of a
fixed dimension and cap C.  To lower U from cap C to cap target_occ-1, search
for a target_occ-point set T inside U satisfying every strict child row V<=U
with cap(V)<target_occ, using the exact condition |T cap V| <= cap(V).

The search is exact but local.  It exposes the compatibility structure:
capacity-one children define forbidden pairs; remaining children are checked
incrementally as small hyperedge-cap constraints.  A reported lowered row is a
valid consequence of the supplied child rows, not a global branch proof.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, struct, time
from collections import Counter
from pathlib import Path

MAGIC = b'E11WANG1'
REC = '<BBHQQQQ'
SZ = struct.calcsize(REC)


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda: f.read(1 << 20), b''):
            h.update(c)
    return h.hexdigest()


def load_rows(path: Path):
    d = path.read_bytes()
    assert d[:8] == MAGIC, (path, d[:8])
    n = struct.unpack('<I', d[8:12])[0]
    assert len(d) == 12 + n * SZ, (path, len(d), 12+n*SZ)
    rows = []
    hist = Counter()
    for i in range(n):
        cap, dim, pad, w0, w1, w2, w3 = struct.unpack(REC, d[12+i*SZ:12+(i+1)*SZ])
        mask = int(w0) | (int(w1) << 64) | (int(w2) << 128) | (int(w3) << 192)
        rows.append({'idx': i, 'cap': int(cap), 'dim': int(dim), 'mask': mask, 'pop': mask.bit_count()})
        hist[(int(dim), int(cap))] += 1
    return rows, {'path': str(path), 'sha256': sha(path), 'count': n, 'dim_cap_hist': {f'{d}:{c}': int(v) for (d,c),v in sorted(hist.items())}}


def points(mask: int):
    return [i for i in range(1, 256) if (mask >> i) & 1]


def pack_row(cap: int, dim: int, mask: int) -> bytes:
    words = [(mask >> (64*j)) & ((1 << 64)-1) for j in range(4)]
    return struct.pack(REC, int(cap), int(dim), 0, *words)


def write_rows(path: Path, rows, new_cap: int):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('wb') as f:
        f.write(MAGIC)
        f.write(struct.pack('<I', len(rows)))
        for r in rows:
            f.write(pack_row(new_cap, r['dim'], r['mask']))


def bit_positions(x: int):
    while x:
        lsb = x & -x
        yield lsb.bit_length() - 1
        x ^= lsb


def analyze_parent(U, rows, target_occ: int):
    Upts = points(U['mask'])
    n = len(Upts)
    pos = {p: i for i, p in enumerate(Upts)}
    constraints = []
    child_cap_hist = Counter()
    child_dim_hist = Counter()
    child_active_pop_hist = Counter()
    for r in rows:
        m = r['mask']
        if m == 0 or m == U['mask']:
            continue
        if (m & ~U['mask']) != 0:
            continue
        if r['cap'] >= target_occ:
            continue
        cm = 0
        # Since m subset U, iterate U points for local positions; n <= 127 in intended use.
        for p in Upts:
            if (m >> p) & 1:
                cm |= 1 << pos[p]
        apop = cm.bit_count()
        if apop <= r['cap']:
            continue
        constraints.append({'idx': r['idx'], 'cap': r['cap'], 'dim': r['dim'], 'cmask': cm, 'pop': apop})
        child_cap_hist[r['cap']] += 1
        child_dim_hist[r['dim']] += 1
        child_active_pop_hist[apop] += 1

    # Compatibility graph allowed by cap-1 child rows.
    allmask = (1 << n) - 1
    compat = [allmask ^ (1 << i) for i in range(n)]
    pair_first_child = {}
    for ch in constraints:
        if ch['cap'] != 1:
            continue
        inds = list(bit_positions(ch['cmask']))
        for a, b in itertools.combinations(inds, 2):
            compat[a] &= ~(1 << b)
            compat[b] &= ~(1 << a)
            if a > b:
                a, b = b, a
            pair_first_child.setdefault((a, b), ch['idx'])
    blocked_pairs = n*(n-1)//2 - sum((compat[i] >> (i+1)).bit_count() for i in range(n))

    # Constraint incidence for incremental exact search.
    inc = [[] for _ in range(n)]
    for ci, ch in enumerate(constraints):
        for v in bit_positions(ch['cmask']):
            inc[v].append(ci)
    counts = [0] * len(constraints)
    chosen = []
    stats = Counter()
    first_rejects = []
    witness = None

    def max_clique_possible(cand: int, need: int) -> bool:
        # Greedy coloring upper bound would be overkill; popcount is enough for small target,
        # with pair-compat pruning handled in recursion.
        return cand.bit_count() >= need

    def rec(cand: int, depth: int) -> bool:
        nonlocal witness
        stats['nodes'] += 1
        need = target_occ - depth
        if need == 0:
            witness = [Upts[i] for i in chosen]
            return True
        if not max_clique_possible(cand, need):
            stats['shortage_prunes'] += 1
            return False
        # Iterate vertices in increasing local order for deterministic certificates/witnesses.
        c = cand
        while c:
            lsb = c & -c
            v = lsb.bit_length() - 1
            c ^= lsb
            # Branch-and-bound: after removing v, if too few remain and this branch fails,
            # loop will end naturally.
            bad = None
            changed = []
            for ci in inc[v]:
                counts[ci] += 1
                changed.append(ci)
                if counts[ci] > constraints[ci]['cap'] and bad is None:
                    bad = ci
            if bad is None:
                chosen.append(v)
                nxt = c & compat[v]
                if rec(nxt, depth+1):
                    return True
                chosen.pop()
            else:
                stats['constraint_prunes'] += 1
                if constraints[bad]['cap'] == 1:
                    stats['cap1_pair_prunes'] += 1
                elif constraints[bad]['cap'] == 2:
                    stats['cap2_prunes'] += 1
                elif constraints[bad]['cap'] == 3:
                    stats['cap3_prunes'] += 1
                elif constraints[bad]['cap'] == 4:
                    stats['cap4_prunes'] += 1
                if len(first_rejects) < 20:
                    first_rejects.append({'partial_plus': [Upts[i] for i in chosen+[v]], 'child_idx': constraints[bad]['idx'], 'child_cap': constraints[bad]['cap'], 'child_dim': constraints[bad]['dim']})
            for ci in reversed(changed):
                counts[ci] -= 1
        return False

    rec(allmask, 0)
    compatible_pair_degrees = [compat[i].bit_count() for i in range(n)]
    return {
        'feasible_set': witness,
        'parent_point_count': n,
        'child_count': len(constraints),
        'child_cap_hist': {str(k): int(v) for k, v in sorted(child_cap_hist.items())},
        'child_dim_hist': {str(k): int(v) for k, v in sorted(child_dim_hist.items())},
        'child_active_pop_hist': {str(k): int(v) for k, v in sorted(child_active_pop_hist.items())},
        'blocked_pair_count_from_cap1': int(blocked_pairs),
        'compatible_pair_count_from_cap1': int(sum((compat[i] >> (i+1)).bit_count() for i in range(n))),
        'compatible_pair_degree_hist': {str(k): int(v) for k, v in sorted(Counter(compatible_pair_degrees).items())},
        'search_stats': {str(k): int(v) for k, v in sorted(stats.items())},
        'first_rejects': first_rejects,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--rows', type=Path, required=True)
    ap.add_argument('--pivot-label', required=True)
    ap.add_argument('--dim', type=int, required=True)
    ap.add_argument('--cap', type=int, required=True)
    ap.add_argument('--target-occ', type=int, default=0, help='default cap: one-ARTIFACT lowering from cap to cap-1')
    ap.add_argument('--limit', type=int, default=0, help='0 means all candidates')
    ap.add_argument('--outdir', type=Path, default=Path('data/quotient_lift/tightening'))
    ap.add_argument('--label', default='')
    ap.add_argument('--detail-limit', type=int, default=80)
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    rows, meta = load_rows(args.rows)
    candidates = [r for r in rows if r['dim'] == args.dim and r['cap'] == args.cap]
    if args.limit:
        candidates = candidates[:args.limit]
    target_occ = args.target_occ or args.cap
    new_cap = target_occ - 1
    tightened = []
    feasible = []
    details = []
    agg_child_cap = Counter(); agg_child_dim = Counter(); agg_active_pop = Counter(); agg_pair_counts = Counter(); agg_search = Counter()
    for j, U in enumerate(candidates):
        res = analyze_parent(U, rows, target_occ)
        for k,v in res['child_cap_hist'].items(): agg_child_cap[int(k)] += int(v)
        for k,v in res['child_dim_hist'].items(): agg_child_dim[int(k)] += int(v)
        for k,v in res['child_active_pop_hist'].items(): agg_active_pop[int(k)] += int(v)
        agg_pair_counts[res['blocked_pair_count_from_cap1']] += 1
        for k,v in res['search_stats'].items(): agg_search[k] += int(v)
        rec = {'row_idx': U['idx'], 'dim': U['dim'], 'old_cap': U['cap'], 'tested_target_occ': target_occ, 'new_cap_if_tightened': new_cap, 'pop': U['pop'], 'mask_hex': hex(U['mask']), 'result': res}
        if res['feasible_set'] is None:
            tightened.append(U)
            if len(details) < args.detail_limit:
                details.append(rec)
        else:
            feasible.append({'row_idx': U['idx'], 'witness': res['feasible_set'], 'mask_hex': hex(U['mask'])})
            if len(details) < args.detail_limit or len(feasible) <= 50:
                details.append(rec)
        if (j+1) % 25 == 0 or j+1 == len(candidates):
            print(args.pivot_label, j+1, '/', len(candidates), 'tightened', len(tightened), 'feasible', len(feasible), 'elapsed', f'{time.time()-t0:.2f}', flush=True)
    label = args.label or f'{args.pivot_label}_dim{args.dim}_cap{args.cap}_target{target_occ}'
    outbin = args.outdir/f'{label}_tightened_to_cap{new_cap}_rows.bin'
    write_rows(outbin, tightened, new_cap)
    out = {
        'schema': 's0908_local_tightening_exact_v1',
        'meaning': 'Each tightened row U is justified by exact local search: no target_occ-point subset of U satisfies all supplied strict child rows V<=U with cap(V)<target_occ under |T∩V|<=cap(V). This is a consequence of the supplied row system and not by itself a global branch exclusion.',
        'rows_meta': meta,
        'pivot_label': args.pivot_label,
        'dim': args.dim,
        'cap': args.cap,
        'target_occ': target_occ,
        'new_cap': new_cap,
        'candidate_count': len(candidates),
        'tightened_count': len(tightened),
        'feasible_count': len(feasible),
        'feasible_examples': feasible[:50],
        'tightened_row_indices': [r['idx'] for r in tightened],
        'aggregate_child_cap_hist': {str(k): int(v) for k,v in sorted(agg_child_cap.items())},
        'aggregate_child_dim_hist': {str(k): int(v) for k,v in sorted(agg_child_dim.items())},
        'aggregate_child_active_pop_hist': {str(k): int(v) for k,v in sorted(agg_active_pop.items())},
        'blocked_pair_count_from_cap1_parent_hist': {str(k): int(v) for k,v in sorted(agg_pair_counts.items())},
        'aggregate_search_stats': {str(k): int(v) for k,v in sorted(agg_search.items())},
        'results_head': details,
        'output_rows': str(outbin),
        'output_rows_sha256': sha(outbin),
        'elapsed_sec': time.time() - t0,
    }
    outjson = args.outdir/f'{label}_exact.json'
    outjson.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'json': str(outjson), 'binary': str(outbin), 'candidate_count': len(candidates), 'tightened_count': len(tightened), 'feasible_count': len(feasible), 'sha256': sha(outbin), 'elapsed_sec': out['elapsed_sec'], 'aggregate_search_stats': out['aggregate_search_stats']}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
