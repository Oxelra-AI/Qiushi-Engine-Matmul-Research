#!/usr/bin/env python3
"""analysis: corrected exact enumeration for dim-5 cap-3 quotient-row tightening.

This repairs the analysis exact triple test.  For a parent quotient Wang row
U with current cap 3, a 3-point subset T inside U is compatible with strict
child rows V<=U only if |T cap V| <= cap(V) for every child with cap(V)<3.
The earlier exact exporter only rejected T when T was wholly contained in a
strict child.  That weaker test is sufficient for already-exported tightened
rows, but it overstates feasibility of surviving triples.

For transparency, this script separates cap-1 child rows (incompatible pairs)
from cap-2 child rows (forbidden triples), computes exact existence of a
compatible triple, and exports all parents for which no compatible triple
exists as cap<=2 consequences.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, struct, time
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path('research/research_record')
OUTDIR = ROOT/'workspace/data/quotient_lift/tightening'
OUTDIR.mkdir(parents=True, exist_ok=True)
ROWS = {
    'rank2': Path('data/wang_native/quotient_binaries/rank2_all_n19.bin'),
    'rank3': Path('data/wang_native/quotient_binaries/rank3_all_n19.bin'),
}
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
    assert len(d) == 12 + n * SZ, (path, len(d), 12 + n * SZ)
    rows = []
    hist = Counter()
    for i in range(n):
        cap, dim, pad, w0, w1, w2, w3 = struct.unpack(REC, d[12+i*SZ:12+(i+1)*SZ])
        mask = int(w0) | (int(w1) << 64) | (int(w2) << 128) | (int(w3) << 192)
        row = {'idx': i, 'cap': int(cap), 'dim': int(dim), 'mask': mask, 'pop': mask.bit_count(), 'words': (int(w0), int(w1), int(w2), int(w3))}
        rows.append(row)
        hist[(int(dim), int(cap))] += 1
    return rows, {
        'path': str(path),
        'sha256': sha(path),
        'count': n,
        'dim_cap_hist': {f'{d}:{c}': int(v) for (d, c), v in sorted(hist.items())},
    }


def pts(mask: int):
    return [i for i in range(1, 256) if (mask >> i) & 1]


def pack_row(cap: int, dim: int, mask: int) -> bytes:
    words = [(mask >> (64*j)) & ((1 << 64) - 1) for j in range(4)]
    return struct.pack(REC, int(cap), int(dim), 0, *words)


def write_rows(path: Path, rows):
    with path.open('wb') as f:
        f.write(MAGIC)
        f.write(struct.pack('<I', len(rows)))
        for r in rows:
            f.write(pack_row(2, r['dim'], r['mask']))


def strict_children_inside(U, allrows):
    """Return strict child constraints mapped to local parent positions."""
    Umask = U['mask']
    Upts = pts(Umask)
    pos = {p: i for i, p in enumerate(Upts)}
    children = []
    child_cap_hist = Counter()
    child_dim_hist = Counter()
    active_pop_hist = Counter()
    for r in allrows:
        m = r['mask']
        if m == 0 or m == Umask:
            continue
        if (m & ~Umask) != 0:
            continue
        if r['cap'] >= 3:
            continue
        cm = 0
        for p in Upts:
            if (m >> p) & 1:
                cm |= 1 << pos[p]
        apop = cm.bit_count()
        # A child whose active size is at most its cap cannot constrain any subset of U.
        if apop <= r['cap']:
            continue
        children.append({'idx': r['idx'], 'cap': r['cap'], 'dim': r['dim'], 'cmask': cm, 'pop': apop})
        child_cap_hist[r['cap']] += 1
        child_dim_hist[r['dim']] += 1
        active_pop_hist[apop] += 1
    return Upts, children, child_cap_hist, child_dim_hist, active_pop_hist


def analyze_row(U, allrows):
    Upts, children, child_cap_hist, child_dim_hist, active_pop_hist = strict_children_inside(U, allrows)

    # Pair graph from cap-1 children: if two points lie in such a child, the pair cannot occur.
    pair_blocked = [[False] * len(Upts) for _ in Upts]
    pair_first_child = {}
    cap1_child_count = 0
    cap2_child_count = 0
    for ch in children:
        inds = [i for i in range(len(Upts)) if (ch['cmask'] >> i) & 1]
        if ch['cap'] == 1:
            cap1_child_count += 1
            for a, b in itertools.combinations(inds, 2):
                if not pair_blocked[a][b]:
                    pair_first_child[(a, b)] = ch['idx']
                pair_blocked[a][b] = pair_blocked[b][a] = True
        elif ch['cap'] == 2:
            cap2_child_count += 1

    total_pairs = len(Upts) * (len(Upts) - 1) // 2
    blocked_pair_count = sum(1 for a in range(len(Upts)) for b in range(a+1, len(Upts)) if pair_blocked[a][b])
    independent_pair_count = total_pairs - blocked_pair_count

    feasible = None
    triple_count = 0
    pair_rejects = 0
    cap2_rejects = 0
    other_rejects = 0
    first_rejects = []
    first_pair_ok_cap2_bad = []
    top_blocking_children = Counter()
    compatible_pair_degrees = [0] * len(Upts)

    for a, b in itertools.combinations(range(len(Upts)), 2):
        if not pair_blocked[a][b]:
            compatible_pair_degrees[a] += 1
            compatible_pair_degrees[b] += 1

    for comb in itertools.combinations(range(len(Upts)), 3):
        triple_count += 1
        a, b, c = comb
        # Fast pair rejection generated by cap-1 children.
        bad_pair = None
        for u, v in ((a, b), (a, c), (b, c)):
            if pair_blocked[u][v]:
                bad_pair = tuple(sorted((u, v)))
                break
        if bad_pair is not None:
            pair_rejects += 1
            child_idx = pair_first_child.get(bad_pair)
            if child_idx is not None:
                top_blocking_children[child_idx] += 1
            if len(first_rejects) < 25:
                first_rejects.append({'triple': [Upts[i] for i in comb], 'reason': 'cap1_pair', 'pair': [Upts[i] for i in bad_pair], 'child_idx': child_idx})
            continue
        tm = (1 << a) | (1 << b) | (1 << c)
        bad_child = None
        for ch in children:
            # Correct condition: any child intersection exceeding its cap rejects the triple.
            if (tm & ch['cmask']).bit_count() > ch['cap']:
                bad_child = ch
                break
        if bad_child is None:
            feasible = [Upts[i] for i in comb]
            break
        if bad_child['cap'] == 2:
            cap2_rejects += 1
            if len(first_pair_ok_cap2_bad) < 10:
                first_pair_ok_cap2_bad.append({'triple': [Upts[i] for i in comb], 'child_idx': bad_child['idx'], 'child_dim': bad_child['dim'], 'child_cap': bad_child['cap']})
        else:
            other_rejects += 1
        top_blocking_children[bad_child['idx']] += 1
        if len(first_rejects) < 25:
            first_rejects.append({'triple': [Upts[i] for i in comb], 'reason': f'cap{bad_child["cap"]}_intersection', 'child_idx': bad_child['idx'], 'child_dim': bad_child['dim'], 'child_cap': bad_child['cap']})

    return {
        'feasible_triple': feasible,
        'triple_count_checked_until_witness_or_exhaustion': triple_count,
        'child_count': len(children),
        'child_cap_hist': {str(k): int(v) for k, v in sorted(child_cap_hist.items())},
        'child_dim_hist': {str(k): int(v) for k, v in sorted(child_dim_hist.items())},
        'child_active_pop_hist': {str(k): int(v) for k, v in sorted(active_pop_hist.items())},
        'cap1_child_count': cap1_child_count,
        'cap2_child_count': cap2_child_count,
        'parent_point_count': len(Upts),
        'blocked_pair_count_from_cap1': blocked_pair_count,
        'independent_pair_count_from_cap1': independent_pair_count,
        'max_compatible_pair_degree': max(compatible_pair_degrees) if compatible_pair_degrees else 0,
        'compatible_pair_degree_hist': {str(k): int(v) for k, v in sorted(Counter(compatible_pair_degrees).items())},
        'reject_counts_before_witness_or_exhaustion': {
            'cap1_pair': pair_rejects,
            'cap2_or_other_full_intersection': cap2_rejects,
            'other': other_rejects,
        },
        'top_blocking_children': [{'idx': int(i), 'count': int(c)} for i, c in top_blocking_children.most_common(12)],
        'first_rejects': first_rejects,
        'first_pair_ok_cap2_bad': first_pair_ok_cap2_bad,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pivot', choices=['rank2', 'rank3'], required=True)
    ap.add_argument('--dim', type=int, default=5)
    ap.add_argument('--cap', type=int, default=3)
    ap.add_argument('--max-results', type=int, default=100, help='number of detailed row results to store before storing only feasible examples and indices')
    args = ap.parse_args()
    t0 = time.time()
    rows, meta = load_rows(ROWS[args.pivot])
    cand = [r for r in rows if r['dim'] == args.dim and r['cap'] == args.cap]
    tightened = []
    feasible = []
    details = []
    agg_child_cap = Counter()
    agg_child_dim = Counter()
    agg_active_pop = Counter()
    agg_pair_blocks = Counter()
    for j, U in enumerate(cand):
        res = analyze_row(U, rows)
        for k, v in res['child_cap_hist'].items(): agg_child_cap[int(k)] += int(v)
        for k, v in res['child_dim_hist'].items(): agg_child_dim[int(k)] += int(v)
        for k, v in res['child_active_pop_hist'].items(): agg_active_pop[int(k)] += int(v)
        agg_pair_blocks[res['blocked_pair_count_from_cap1']] += 1
        rec = {'row_idx': U['idx'], 'dim': U['dim'], 'old_cap': U['cap'], 'new_cap_if_tightened': 2, 'pop': U['pop'], 'result': res}
        if res['feasible_triple'] is None:
            tightened.append(U)
            if len(details) < args.max_results:
                details.append(rec)
        else:
            feasible.append({'row_idx': U['idx'], 'triple': res['feasible_triple'], 'result_summary': {k: res[k] for k in ['child_count','child_cap_hist','child_dim_hist','blocked_pair_count_from_cap1','independent_pair_count_from_cap1','triple_count_checked_until_witness_or_exhaustion']}})
            # Feasible survivors are precisely what changed relative to analysis, so keep them all if small.
            if len(details) < args.max_results or len(feasible) <= 50:
                details.append(rec)
        if (j + 1) % 50 == 0 or j + 1 == len(cand):
            print(args.pivot, j+1, '/', len(cand), 'tightened', len(tightened), 'feasible', len(feasible), flush=True)
    outbin = OUTDIR/f'{args.pivot}_dim{args.dim}_cap{args.cap}_corrected_tightened_to_cap2_rows.bin'
    write_rows(outbin, tightened)
    out = {
        'schema': 's0908_corrected_dim5_cap3_tightening_v1',
        'meaning': 'For each parent row U with quotient cap 3, this exhaustively tests every 3-point subset T of U against all strict child rows V<=U using the correct condition |T∩V| <= cap(V). If no compatible triple exists, U can be replaced by cap<=2 as a consequence of the child rows. Rows previously tightened by the weaker analysis containment test remain valid; feasible triples reported in analysis are not used.',
        'pivot': args.pivot,
        'dim': args.dim,
        'cap': args.cap,
        'rows_meta': meta,
        'candidate_count': len(cand),
        'tightened_count': len(tightened),
        'feasible_count': len(feasible),
        'feasible_examples': feasible[:50],
        'tightened_row_indices': [r['idx'] for r in tightened],
        'aggregate_child_cap_hist': {str(k): int(v) for k, v in sorted(agg_child_cap.items())},
        'aggregate_child_dim_hist': {str(k): int(v) for k, v in sorted(agg_child_dim.items())},
        'aggregate_child_active_pop_hist': {str(k): int(v) for k, v in sorted(agg_active_pop.items())},
        'blocked_pair_count_from_cap1_parent_hist': {str(k): int(v) for k, v in sorted(agg_pair_blocks.items())},
        'results_head': details,
        'output_rows': str(outbin),
        'output_rows_sha256': sha(outbin),
        'elapsed_sec': time.time() - t0,
    }
    outjson = OUTDIR/f'{args.pivot}_dim{args.dim}_cap{args.cap}_corrected_tightened_to_cap2_exact.json'
    outjson.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'json': str(outjson), 'binary': str(outbin), 'candidate_count': len(cand), 'tightened_count': len(tightened), 'feasible_count': len(feasible), 'sha256': sha(outbin), 'elapsed_sec': out['elapsed_sec']}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
