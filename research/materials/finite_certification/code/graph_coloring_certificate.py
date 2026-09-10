#!/usr/bin/env python3
r"""Build direct Wang-row graph certificates for fixed matching strata.

For a fixed nonadjacent rank-1 matching M (including E11), Wang occupation rows
with residual capacity

    r(Phi) = (20 - L(Phi)) - |M \cap Phi|

have immediate consequences for the higher-rank completion variables:

  r < 0: the fixed matching itself violates a Wang row.
  r = 0: every higher-rank point in Phi is forbidden.
  r = 1: every pair of surviving higher-rank points in Phi is incompatible.

A completion with length 20 would need target = 20-|M| higher-rank points.  To
certify no such completion from r=0,1 consequences alone, this script tries to
partition the surviving higher-rank vertices into < target cliques of the
incompatibility graph (equivalently, color the complement graph with < target
colors).  This is a directly checkable upper-bound certificate for the
independence number, unlike an unfinished maximum-independent-set search.

The produced certificate remains an A-side Wang-support certificate over F2. It
is not a full tensor-rank lower bound unless the whole global cover is closed.
"""
import argparse
import json
import pathlib
import pickle
import sys
import time
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

SDIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SDIR))
from wang_capacity_lazy import unpack_basis, subspace_points_from_basis, matrix_rank_of_mask  # noqa:E402


def rank1_points() -> set:
    pts = set()
    for u in range(1, 8):
        for v in range(1, 8):
            m = 0
            for i in range(3):
                if (u >> i) & 1:
                    m |= v << (3 * i)
            pts.add(m)
    return pts


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


def load_lut(path: pathlib.Path) -> Dict[int, int]:
    with path.open('rb') as f:
        data = pickle.load(f)
    if isinstance(data, dict) and 'lut' in data:
        lut = data['lut']
    else:
        lut = data
    return {int(k): int(v) for k, v in lut.items()}


def iter_strata(strata_path: pathlib.Path, k_filter: int = 0) -> List[Tuple[int, dict]]:
    with strata_path.open() as f:
        sd = json.load(f)
    out = []
    idx = 0
    for k_str in sorted(sd['representatives_by_k'], key=int):
        for rep in sd['representatives_by_k'][k_str]:
            k = int(rep['k'])
            if not k_filter or k == k_filter:
                out.append((idx, rep))
            idx += 1
    return out


def process_stratum(lut: Dict[int, int], matching: Sequence[int], hr_set: set, hr_list: Sequence[int]):
    """Extract r<0 rows, r=0 vertex exclusions, and r=1 pair exclusions."""
    matching = [int(x) for x in matching]
    k = len(matching)
    target = 20 - k
    # For r <= 1, need L >= 20-k-1 before matching incidence can matter.
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
        # Early exit: cannot reach r <= 1 anymore.
        for mi, m in enumerate(matching):
            if in_span_piv(piv, m):
                cnt += 1
            if cnt + (k - mi - 1) < needed_for_le1:
                break
        else:
            # Completed without break, so r <= 1 is still possible.
            pass
        if cnt + (k - mi - 1) < needed_for_le1:
            continue

        residual = cap - cnt
        if residual < 0:
            row_counts['res_neg'] += 1
            impossible.append({'key': int(key), 'lb': int(lb), 'cap': int(cap), 'matching_count': int(cnt)})
            # Keep scanning so the summary still describes row families, but the
            # first such row already certifies the stratum impossible.
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
    survivor_edges = {p: key for p, key in edge_key.items() if p[0] in ss and p[1] in ss}
    return {
        'target': target,
        'impossible_rows': impossible,
        'vertex_key': vertex_key,
        'survivors': survivors,
        'edge_key': survivor_edges,
        'row_counts': row_counts,
    }


def build_complement_adj(n: int, edge_pairs_idx: Iterable[Tuple[int, int]]) -> List[set]:
    """Complement of the incompatibility graph on n vertices."""
    incomp = [set() for _ in range(n)]
    for i, j in edge_pairs_idx:
        incomp[i].add(j)
        incomp[j].add(i)
    comp = []
    full = set(range(n))
    for i in range(n):
        comp.append(full - {i} - incomp[i])
    return comp


def greedy_dsatur_coloring(adj: List[set], max_colors: int) -> Optional[List[int]]:
    """Greedy DSATUR coloring of graph adj using at most max_colors colors."""
    n = len(adj)
    colors = [-1] * n
    degrees = [len(a) for a in adj]
    for _ in range(n):
        best = None
        best_key = None
        for v in range(n):
            if colors[v] != -1:
                continue
            sat = len({colors[u] for u in adj[v] if colors[u] != -1})
            key = (sat, degrees[v], -v)
            if best_key is None or key > best_key:
                best_key = key
                best = v
        used = {colors[u] for u in adj[best] if colors[u] != -1}
        chosen = None
        for c in range(max_colors):
            if c not in used:
                chosen = c
                break
        if chosen is None:
            return None
        colors[best] = chosen
    return colors


def dsatur_backtrack_coloring(adj: List[set], max_colors: int, time_limit: float) -> Tuple[Optional[List[int]], bool]:
    """Search for a proper coloring with <= max_colors. Returns (colors, completed)."""
    n = len(adj)
    colors = [-1] * n
    degrees = [len(a) for a in adj]
    t0 = time.time()
    timed_out = False

    # Greedy seed; if it succeeds, no backtracking is needed.
    seed = greedy_dsatur_coloring(adj, max_colors)
    if seed is not None:
        return seed, True

    def choose_vertex() -> int:
        best = -1
        best_key = None
        for v in range(n):
            if colors[v] != -1:
                continue
            forbidden = {colors[u] for u in adj[v] if colors[u] != -1}
            forbidden.discard(-1)
            avail = max_colors - len(forbidden)
            key = (-avail, len(forbidden), degrees[v], -v)
            if best_key is None or key > best_key:
                best_key = key
                best = v
        return best

    def rec(colored_count: int) -> bool:
        nonlocal timed_out
        if time.time() - t0 > time_limit:
            timed_out = True
            return False
        if colored_count == n:
            return True
        v = choose_vertex()
        used = {colors[u] for u in adj[v] if colors[u] != -1}
        # Prefer low colors, but try colors with largest future reuse first.
        candidates = [c for c in range(max_colors) if c not in used]
        if not candidates:
            return False
        candidates.sort(key=lambda c: -sum(1 for x in colors if x == c))
        for c in candidates:
            colors[v] = c
            if rec(colored_count + 1):
                return True
            colors[v] = -1
            if timed_out:
                return False
        return False

    ok = rec(0)
    return (list(colors) if ok else None), (not timed_out)


def color_classes_from_assignment(survivors: Sequence[int], colors: Sequence[int]) -> List[List[int]]:
    groups: Dict[int, List[int]] = {}
    for h, c in zip(survivors, colors):
        groups.setdefault(int(c), []).append(int(h))
    return [sorted(v) for _, v in sorted(groups.items())]


def certify_stratum(idx: int, st: dict, info: dict, out_dir: pathlib.Path,
                     color_time: float, source_paths: dict) -> dict:
    matching = [int(x) for x in st['canonical']]
    target = int(info['target'])
    rec = {
        'idx': int(idx),
        'k': int(st['k']),
        'matching': matching,
        'orbit_size': int(st.get('orbit_image_count', st.get('enumerated_members', 0))),
        'target': target,
        'impossible_rows': len(info['impossible_rows']),
        'vertex_excluded': len(info['vertex_key']),
        'surviving': len(info['survivors']),
        'surviving_edges': len(info['edge_key']),
        'row_counts': info['row_counts'],
    }

    cert = {
        'schema': 'fixed_matching_graph_certificate_v1',
        'field': 'F2',
        'meaning': ('Direct Wang-row support certificate for one fixed matching stratum; '
                    'it certifies only the A-side occupation necessary condition for this stratum.'),
        'source_paths': source_paths,
        'idx': rec['idx'],
        'k': rec['k'],
        'matching': matching,
        'target_higher_rank_count': target,
        'orbit_size': rec['orbit_size'],
        'row_counts': info['row_counts'],
    }

    if info['impossible_rows']:
        rec['status'] = 'certified_excluded_matching_violates'
        cert['certificate_type'] = 'matching_violates'
        cert['violating_row'] = info['impossible_rows'][0]
    elif len(info['survivors']) < target:
        rec['status'] = 'certified_excluded_vertex_count'
        cert['certificate_type'] = 'vertex_count'
        cert['vertex_exclusions'] = [[int(h), int(k)] for h, k in sorted(info['vertex_key'].items())]
        cert['survivors'] = [int(x) for x in info['survivors']]
    else:
        survivors = info['survivors']
        idx_of = {h: i for i, h in enumerate(survivors)}
        edge_idx = [(idx_of[a], idx_of[b]) for (a, b) in info['edge_key']]
        comp_adj = build_complement_adj(len(survivors), edge_idx)
        max_colors = target - 1
        t0 = time.time()
        colors, color_completed = dsatur_backtrack_coloring(comp_adj, max_colors, color_time)
        rec['color_search_completed'] = bool(color_completed)
        rec['color_elapsed_sec'] = round(time.time() - t0, 3)
        if colors is not None:
            classes = color_classes_from_assignment(survivors, colors)
            rec['status'] = 'certified_excluded_clique_cover'
            rec['color_count'] = len(classes)
            rec['color_class_sizes'] = [len(c) for c in classes]
            cert['certificate_type'] = 'clique_cover'
            cert['max_color_count_allowed'] = max_colors
            cert['vertex_exclusions'] = [[int(h), int(k)] for h, k in sorted(info['vertex_key'].items())]
            cert['survivors'] = [int(x) for x in survivors]
            cert['color_classes'] = classes
            pair_rows = []
            for cls in classes:
                for i, a in enumerate(cls):
                    for b in cls[i+1:]:
                        key = info['edge_key'].get((min(a, b), max(a, b)))
                        if key is None:
                            raise RuntimeError(f'color class is not a clique: missing edge {a},{b}')
                        pair_rows.append([int(min(a, b)), int(max(a, b)), int(key)])
            cert['intra_color_edge_rows'] = pair_rows
            rec['intra_color_edge_row_count'] = len(pair_rows)
        else:
            rec['status'] = 'unresolved_no_coloring_found'
            rec['color_count'] = None
            cert['certificate_type'] = 'unresolved'
            cert['vertex_exclusions_head'] = [[int(h), int(k)] for h, k in sorted(info['vertex_key'].items())[:200]]
            cert['survivors'] = [int(x) for x in survivors]
            cert['note'] = 'No <=target-1 coloring of the complement graph was found within this run; this is not an exclusion.'

    cert_path = out_dir / f"stratum_idx{idx:03d}_k{rec['k']}_{'_'.join(map(str, matching))}.cert.json"
    with cert_path.open('w') as f:
        json.dump(cert, f, indent=2, sort_keys=True)
    rec['certificate_path'] = str(cert_path)
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--strata', default='workspace/data/matching_strata/anchored_matching_strata.json')
    ap.add_argument('--lut', default='workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    ap.add_argument('--k-filter', type=int, default=7)
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--color-time', type=float, default=20.0)
    args = ap.parse_args()

    out_dir = pathlib.Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    r1 = rank1_points()
    hr_list = sorted(m for m in range(1, 512) if m not in r1)
    hr_set = set(hr_list)
    if len(r1) != 49 or len(hr_list) != 462:
        raise RuntimeError('unexpected rank-1/HR universe size')

    strata_path = pathlib.Path(args.strata)
    lut_path = pathlib.Path(args.lut)
    strata = iter_strata(strata_path, args.k_filter)

    print(f'Loading LUT from {lut_path} ...')
    t0 = time.time()
    lut = load_lut(lut_path)
    print(f'Loaded {len(lut):,} LUT rows in {time.time()-t0:.2f}s')

    source_paths = {'strata': str(strata_path), 'lut': str(lut_path)}
    results = []
    for idx, st in strata:
        matching = [int(x) for x in st['canonical']]
        print(f'[{idx}] k={st["k"]} matching={matching}')
        ts = time.time()
        info = process_stratum(lut, matching, hr_set, hr_list)
        rec = certify_stratum(idx, st, info, out_dir, args.color_time, source_paths)
        rec['elapsed_sec'] = round(time.time() - ts, 3)
        print(json.dumps({k: rec[k] for k in rec if k not in ('certificate_path', 'row_counts')}, sort_keys=True))
        results.append(rec)

    certified = [r for r in results if str(r.get('status', '')).startswith('certified_excluded')]
    summary = {
        'schema': 'fixed_matching_graph_certificate_summary_v1',
        'k_filter': args.k_filter,
        'total_tested': len(results),
        'total_certified_excluded': len(certified),
        'results': results,
        'interpretation': ('These are support-side Wang occupation certificates for fixed matching strata. '
                           'They do not close the global rank problem without the adjacent-pair branch and lower-k matching strata.'),
    }
    summary_path = out_dir / f'summary_k{args.k_filter:02d}.json'
    with summary_path.open('w') as f:
        json.dump(summary, f, indent=2, sort_keys=True)
    print(f'Saved {summary_path}')
    print(f'Certified excluded: {len(certified)}/{len(results)}')


if __name__ == '__main__':
    main()
