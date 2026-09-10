#!/usr/bin/env python3
"""analysis: fast exact bottom-up capacity tightening by enumerating true child subspaces.

Input is an E11WANG1 quotient-row table, preferably already containing previous
local tightenings.  For every parent row U with a chosen (dim,cap), test whether
there exists a target_occ-point subset T of U satisfying all strict child rows
V<U whose current capacity is < target_occ.  The exact condition is
|T cap V| <= cap(V).  If no such T exists, U is exported with capacity
target_occ-1.

Unlike the first exact script, this does not scan all rows for every parent.  It
constructs a basis of U, enumerates the true subspaces of F2^dim, maps them into
the ambient quotient point set, and looks up their current capacities by mask.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, struct, time
from collections import Counter, defaultdict
from functools import lru_cache
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
    best = {}
    hist = Counter()
    for i in range(n):
        cap, dim, pad, w0, w1, w2, w3 = struct.unpack(REC, d[12+i*SZ:12+(i+1)*SZ])
        mask = int(w0) | (int(w1) << 64) | (int(w2) << 128) | (int(w3) << 192)
        row = {'idx': i, 'cap': int(cap), 'dim': int(dim), 'mask': mask, 'pop': mask.bit_count()}
        rows.append(row)
        hist[(int(dim), int(cap))] += 1
        old = best.get(mask)
        if old is None or int(cap) < old['cap']:
            best[mask] = row
    return rows, best, {'path': str(path), 'sha256': sha(path), 'count': n, 'unique_masks': len(best), 'dim_cap_hist': {f'{d}:{c}': int(v) for (d,c),v in sorted(hist.items())}}


def points(mask: int):
    return [i for i in range(1, 256) if (mask >> i) & 1]


def gf2_rank(vs):
    basis = [0] * 9
    r = 0
    for x in vs:
        y = x
        while y:
            p = y.bit_length() - 1
            if basis[p]:
                y ^= basis[p]
            else:
                basis[p] = y
                r += 1
                break
    return r


def independent_basis_from_mask(mask: int, dim: int):
    basis = []
    r = 0
    for p in points(mask):
        nr = gf2_rank(basis + [p])
        if nr > r:
            basis.append(p)
            r = nr
            if r == dim:
                break
    # Verify span equals mask.
    sm = 0
    for x in range(1, 1 << len(basis)):
        v = 0
        for i, b in enumerate(basis):
            if (x >> i) & 1:
                v ^= b
        sm |= 1 << v
    if r != dim or sm != mask:
        raise ValueError(f'bad parent basis dim={dim} rank={r} span_pop={sm.bit_count()} mask_pop={mask.bit_count()}')
    return tuple(basis)


@lru_cache(None)
def local_subspace_masks(d: int, k: int):
    """All k-dimensional subspaces of F2^d as masks on nonzero local vectors."""
    if k == 0:
        return (0,)
    if k == d:
        return (((1 << (1 << d)) - 1) & ~1,)
    # Use orthogonal duality for hyperplanes and co-hyperplanes when cheap.
    if k == d - 1:
        masks = []
        for a in range(1, 1 << d):
            m = 0
            for x in range(1, 1 << d):
                if ((a & x).bit_count() & 1) == 0:
                    m |= 1 << x
            masks.append(m)
        return tuple(sorted(set(masks)))
    # For d<=6 this direct combination enumeration is small enough for k<=4.
    vals = list(range(1, 1 << d))
    seen = set()
    for comb in itertools.combinations(vals, k):
        if gf2_rank(comb) != k:
            continue
        m = 0
        for coeff in range(1, 1 << k):
            v = 0
            for i, b in enumerate(comb):
                if (coeff >> i) & 1:
                    v ^= b
            m |= 1 << v
        seen.add(m)
    return tuple(sorted(seen))


def map_local_mask(local_mask: int, parent_basis) -> int:
    out = 0
    d = len(parent_basis)
    lm = local_mask
    while lm:
        lsb = lm & -lm
        x = lsb.bit_length() - 1
        v = 0
        for i, b in enumerate(parent_basis):
            if (x >> i) & 1:
                v ^= b
        out |= 1 << v
        lm ^= lsb
    return out


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


def bit_positions(mask: int):
    while mask:
        lsb = mask & -mask
        yield lsb.bit_length() - 1
        mask ^= lsb


def analyze_parent(U, cap_by_mask, target_occ: int):
    parent_basis = independent_basis_from_mask(U['mask'], U['dim'])
    Upts = points(U['mask'])
    pos = {p: i for i, p in enumerate(Upts)}
    constraints = []
    missing_children = 0
    child_cap_hist = Counter(); child_dim_hist = Counter(); child_active_pop_hist = Counter()
    for cd in range(1, U['dim']):
        for lm in local_subspace_masks(U['dim'], cd):
            am = map_local_mask(lm, parent_basis)
            ch = cap_by_mask.get(am)
            if ch is None:
                missing_children += 1
                continue
            if ch['cap'] >= target_occ:
                continue
            cm = 0
            for p in Upts:
                if (am >> p) & 1:
                    cm |= 1 << pos[p]
            apop = cm.bit_count()
            if apop <= ch['cap']:
                continue
            constraints.append({'idx': ch['idx'], 'cap': ch['cap'], 'dim': ch['dim'], 'cmask': cm, 'pop': apop})
            child_cap_hist[ch['cap']] += 1
            child_dim_hist[ch['dim']] += 1
            child_active_pop_hist[apop] += 1

    n = len(Upts)
    allmask = (1 << n) - 1
    compat = [allmask ^ (1 << i) for i in range(n)]
    pair_first_child = {}
    for ch in constraints:
        if ch['cap'] != 1:
            continue
        inds = list(bit_positions(ch['cmask']))
        for a, b in itertools.combinations(inds, 2):
            if a > b: a, b = b, a
            compat[a] &= ~(1 << b)
            compat[b] &= ~(1 << a)
            pair_first_child.setdefault((a,b), ch['idx'])
    compatible_pair_count = sum((compat[i] >> (i+1)).bit_count() for i in range(n))
    blocked_pairs = n*(n-1)//2 - compatible_pair_count

    inc = [[] for _ in range(n)]
    for ci, ch in enumerate(constraints):
        for v in bit_positions(ch['cmask']):
            inc[v].append(ci)
    counts = [0] * len(constraints)
    chosen = []
    stats = Counter()
    first_rejects = []
    witness = None

    def rec(cand: int, depth: int) -> bool:
        nonlocal witness
        stats['nodes'] += 1
        need = target_occ - depth
        if need == 0:
            witness = [Upts[i] for i in chosen]
            return True
        if cand.bit_count() < need:
            stats['shortage_prunes'] += 1
            return False
        # Cheap bound: if no compatible pair remains and need>=2, fail.
        if need >= 2:
            has_pair = False
            ctmp = cand
            while ctmp and not has_pair:
                lsb = ctmp & -ctmp; v = lsb.bit_length()-1; ctmp ^= lsb
                if (ctmp & compat[v]):
                    has_pair = True
            if not has_pair:
                stats['pair_bound_prunes'] += 1
                return False
        c = cand
        while c:
            lsb = c & -c
            v = lsb.bit_length() - 1
            c ^= lsb
            bad = None
            changed = []
            for ci in inc[v]:
                counts[ci] += 1
                changed.append(ci)
                if counts[ci] > constraints[ci]['cap'] and bad is None:
                    bad = ci
            if bad is None:
                chosen.append(v)
                if rec(c & compat[v], depth+1):
                    return True
                chosen.pop()
            else:
                stats['constraint_prunes'] += 1
                stats[f'cap{constraints[bad]["cap"]}_prunes'] += 1
                if len(first_rejects) < 20:
                    first_rejects.append({'partial_plus': [Upts[i] for i in chosen+[v]], 'child_idx': constraints[bad]['idx'], 'child_cap': constraints[bad]['cap'], 'child_dim': constraints[bad]['dim']})
            for ci in reversed(changed):
                counts[ci] -= 1
        return False

    rec(allmask, 0)
    degree_hist = Counter([compat[i].bit_count() for i in range(n)])
    return {
        'feasible_set': witness,
        'parent_point_count': n,
        'missing_children': missing_children,
        'child_count': len(constraints),
        'child_cap_hist': {str(k): int(v) for k,v in sorted(child_cap_hist.items())},
        'child_dim_hist': {str(k): int(v) for k,v in sorted(child_dim_hist.items())},
        'child_active_pop_hist': {str(k): int(v) for k,v in sorted(child_active_pop_hist.items())},
        'blocked_pair_count_from_cap1': int(blocked_pairs),
        'compatible_pair_count_from_cap1': int(compatible_pair_count),
        'compatible_pair_degree_hist': {str(k): int(v) for k,v in sorted(degree_hist.items())},
        'search_stats': {str(k): int(v) for k,v in sorted(stats.items())},
        'first_rejects': first_rejects,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--rows', type=Path, required=True)
    ap.add_argument('--pivot-label', required=True)
    ap.add_argument('--dim', type=int, required=True)
    ap.add_argument('--cap', type=int, required=True)
    ap.add_argument('--target-occ', type=int, default=0, help='default: cap, to test lowering cap to cap-1')
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--outdir', type=Path, default=Path('data/quotient_lift/tightening'))
    ap.add_argument('--label', default='')
    ap.add_argument('--detail-limit', type=int, default=80)
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    rows, cap_by_mask, meta = load_rows(args.rows)
    candidates = [r for r in rows if r['dim'] == args.dim and r['cap'] == args.cap]
    if args.limit:
        candidates = candidates[:args.limit]
    target_occ = args.target_occ or args.cap
    new_cap = target_occ - 1
    tightened = []
    feasible = []
    details = []
    agg_child_cap = Counter(); agg_child_dim = Counter(); agg_active_pop = Counter(); agg_pair_counts = Counter(); agg_search = Counter(); missing_total = 0
    for j, U in enumerate(candidates):
        res = analyze_parent(U, cap_by_mask, target_occ)
        missing_total += res['missing_children']
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
        if (j+1) % 1000 == 0 or (j+1) % 25 == 0 and len(candidates) <= 500 or j+1 == len(candidates):
            print(args.pivot_label, j+1, '/', len(candidates), 'tightened', len(tightened), 'feasible', len(feasible), 'elapsed', f'{time.time()-t0:.2f}', flush=True)
    label = args.label or f'{args.pivot_label}_dim{args.dim}_cap{args.cap}_target{target_occ}'
    outbin = args.outdir/f'{label}_tightened_to_cap{new_cap}_rows.bin'
    write_rows(outbin, tightened, new_cap)
    out = {
        'schema': 's0908_local_tightening_subspace_enum_v1',
        'meaning': 'Each tightened row U is justified by exact child-subspace enumeration and backtracking: no target_occ-point subset of U satisfies all known strict child capacities under |T∩V|<=cap(V). The proof depends on the supplied row table capacities and remains a local consequence, not a complete rank lower bound.',
        'rows_meta': meta,
        'pivot_label': args.pivot_label,
        'dim': args.dim,
        'cap': args.cap,
        'target_occ': target_occ,
        'new_cap': new_cap,
        'candidate_count': len(candidates),
        'tightened_count': len(tightened),
        'feasible_count': len(feasible),
        'missing_child_lookups_total': missing_total,
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
    print(json.dumps({'json': str(outjson), 'binary': str(outbin), 'candidate_count': len(candidates), 'tightened_count': len(tightened), 'feasible_count': len(feasible), 'missing_child_lookups_total': missing_total, 'sha256': sha(outbin), 'elapsed_sec': out['elapsed_sec'], 'aggregate_search_stats': out['aggregate_search_stats']}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
