#!/usr/bin/env python3
"""analysis finite-system tools for the surviving coset lower-bound route.

The module builds a WANG512 restricted row binary for the residual rank-one
problem after fixing a high-rank set H in the normalized column coset.  It uses
independent row construction from the Wang LUT rather than reading a previous
CEGAR active set.  The restricted variables are the allowed rank-one A-directions
from surviving_coset_ansatz.analyze_H(H); H is forced by reducing each cap by
|W cap H| and each row mask is intersected with the allowed set.  Tautological
rows are omitted; any negative residual cap is emitted as an empty cap-0 row.

It can also build length-n variants for the same H to see whether the model is
at the expected edge, and it can test known A-multisets against a length-n full
Wang binary.
"""
from __future__ import annotations
import argparse, hashlib, json, pickle, struct, subprocess, sys, time
from collections import Counter
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from surviving_coset_ansatz import analyze_H, canonical_coset_points, load_lut, rank_one_uv_map  # type: ignore

NBITS = 9
MAGIC = b"WANG512\x01"
DEFAULT_LUT = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
DEFAULT_ANALYSIS = Path("data/coset_ansatz/surviving_coset_ansatz.json")
DEFAULT_OUTROOT = Path("data/coset_cert")
DEFAULT_DFS = Path("scripts/wang_domain_dfs_safe")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def unpack_key(key: int) -> Tuple[int, ...]:
    d = int(key) & 0xF
    packed = int(key) >> 4
    return tuple((packed >> (NBITS * i)) & ((1 << NBITS) - 1) for i in range(d))


def span_points_from_basis(basis: Sequence[int]) -> List[int]:
    pts = []
    d = len(basis)
    for m in range(1, 1 << d):
        x = 0
        for i, b in enumerate(basis):
            if (m >> i) & 1:
                x ^= int(b)
        if 1 <= x <= 511:
            pts.append(x)
    return pts


def words_from_points(pts: Iterable[int]) -> Tuple[int, ...]:
    words = [0] * 8
    for p in pts:
        p = int(p)
        if 1 <= p <= 511:
            words[p >> 6] |= 1 << (p & 63)
    return tuple(words)


def points_from_words(words: Sequence[int]) -> List[int]:
    out = []
    for wi, w0 in enumerate(words):
        w = int(w0)
        while w:
            lb = w & -w
            b = lb.bit_length() - 1
            p = 64 * wi + b
            if 1 <= p <= 511:
                out.append(p)
            w ^= lb
    return out


def write_wang512(path: Path, rows: Sequence[Tuple[int, int, Tuple[int, ...]]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('wb') as f:
        f.write(MAGIC)
        f.write(struct.pack('<I', len(rows)))
        for cap, dim, words in rows:
            f.write(struct.pack('<BBH', int(cap), int(dim), 0))
            for w in words:
                f.write(struct.pack('<Q', int(w)))


def load_H_from_analysis(analysis_path: Path, h_index: int) -> List[int]:
    obj = json.loads(analysis_path.read_text())
    return [int(x) for x in obj['analyses'][h_index]['H']]


def build_restricted(lut: Dict[int, int], H: Sequence[int], length: int, outdir: Path) -> Dict:
    p, _coset, _rank2, _rank3 = canonical_coset_points()
    hrec = analyze_H(lut, H, p)
    allowed = [int(x) for x in hrec['allowed_rank_one']]
    allowed_set = set(allowed)
    H = [int(x) for x in H]
    H_set = set(H)
    H_words = words_from_points(H)
    allowed_words = words_from_points(allowed)
    rows = []
    raw_rows = 0; taut = 0; neg = 0; missing = 0
    cap_hist = Counter(); dim_hist = Counter(); support_hist = Counter(); h_occ_hist = Counter()
    source_row_indices = []
    # Deterministic LUT order is insertion order from Wang build; row ids below are semantic ids in this iteration, not original binary ids.
    for semantic_idx, (key, lb) in enumerate(lut.items()):
        dim = int(key) & 0xF
        if dim == 0:
            continue
        basis = unpack_key(key)
        pts = span_points_from_basis(basis)
        h_occ = sum(1 for x in H if x in pts)
        cap = int(length) - int(lb) - h_occ
        if cap >= len(allowed):
            # Could still be taut after intersection; quick skip for broad high cap.
            pass
        restricted_pts = [x for x in pts if x in allowed_set]
        if cap < 0:
            rows.append((0, dim, (0, 0, 0, 0, 0, 0, 0, 0)))
            neg += 1; raw_rows += 1; cap_hist[0] += 1; dim_hist[dim] += 1; support_hist[0] += 1; h_occ_hist[h_occ] += 1; source_row_indices.append(semantic_idx)
        elif len(restricted_pts) == 0:
            taut += 1
        elif cap >= len(restricted_pts):
            taut += 1
        else:
            rows.append((cap, dim, words_from_points(restricted_pts)))
            raw_rows += 1; cap_hist[cap] += 1; dim_hist[dim] += 1; support_hist[len(restricted_pts)] += 1; h_occ_hist[h_occ] += 1; source_row_indices.append(semantic_idx)
    # Add per-left/right caps <= 5 in the same binary for the safe DFS. These are Wang rows for row/column rank-one planes at n=20;
    # for n != 20 keep them as the length-n semantic cap length-15, since LB(uF^3)=15.
    uv = rank_one_uv_map(); manual = 0
    family_cap = int(length) - 15
    for side in ['left', 'right']:
        for val in range(1, 8):
            pts = [x for x in allowed if (uv[x][0] if side == 'left' else uv[x][1]) == val]
            if pts and family_cap < len(pts):
                rows.append((family_cap, 3, words_from_points(pts)))
                manual += 1; cap_hist[family_cap] += 1; dim_hist[3] += 1; support_hist[len(pts)] += 1
    # Deduplicate exact (cap,words) pairs; dimension is metadata only, keep minimum dim for record.
    by_key: Dict[Tuple[int, Tuple[int, ...]], int] = {}
    for cap, dim, words in rows:
        k = (int(cap), tuple(words))
        if k not in by_key or dim < by_key[k]:
            by_key[k] = dim
    rows_dedup = [(cap, dim, words) for (cap, words), dim in sorted(by_key.items(), key=lambda z: (z[0][0], z[0][1]))]
    out_bin = outdir / f'H_restricted_len{length}.wang512.bin'
    write_wang512(out_bin, rows_dedup)
    meta = {
        'schema': 'coset_restricted_wang512_v1', 'H': H, 'H_firstrows': hrec['firstrows'], 'length': int(length),
        'target_rank_one_terms': max(0, int(length) - len(H)), 'allowed_rank_one_count': len(allowed),
        'allowed_rank_one': allowed, 'allowed_rank_one_uv': hrec['allowed_rank_one_uv'],
        'source_lut_entries': len(lut), 'raw_non_taut_rows_before_dedup': raw_rows, 'manual_family_rows_added_before_dedup': manual,
        'rows_written': len(rows_dedup), 'tautological_source_rows': taut, 'negative_residual_rows': neg,
        'cap_hist_written': dict(sorted((int(k), int(v)) for k, v in Counter(c for c,_,__ in rows_dedup).items())),
        'dim_hist_written': dict(sorted((int(k), int(v)) for k, v in Counter(d for _,d,__ in rows_dedup).items())),
        'support_size_hist_written': dict(sorted((int(sum(w.bit_count() for w in words)), int(v)) for words, v in Counter(tuple(ws) for _,__,ws in rows_dedup).items())),
        'pre_dedup_cap_hist': dict(sorted((int(k), int(v)) for k, v in cap_hist.items())),
        'pre_dedup_dim_hist': dict(sorted((int(k), int(v)) for k, v in dim_hist.items())),
        'pre_dedup_support_hist': dict(sorted((int(k), int(v)) for k, v in support_hist.items())),
        'h_occ_hist_non_taut': dict(sorted((int(k), int(v)) for k, v in h_occ_hist.items())),
        'binary_path': str(out_bin), 'binary_sha256': sha256(out_bin), 'size_bytes': out_bin.stat().st_size,
        'expected_size_bytes': 12 + 68 * len(rows_dedup), 'size_matches': out_bin.stat().st_size == 12 + 68 * len(rows_dedup),
        'H_words': [int(w) for w in H_words], 'allowed_words': [int(w) for w in allowed_words],
    }
    (outdir / f'H_restricted_len{length}.meta.json').write_text(json.dumps(meta, indent=2, sort_keys=True) + '\n')
    return meta


def run_dfs(meta: Dict, timeout: int, dfs_bin: Path, outdir: Path) -> Dict:
    target = int(meta['target_rank_one_terms'])
    out_json = outdir / f'dfs_len{meta["length"]}.json'
    used_json = outdir / f'dfs_len{meta["length"]}_used_rows.json'
    # The safe DFS always has ambient domain 1..511 for WANG512 files.  The
    # restricted binary only contains masks on the allowed rank-one directions,
    # so all other ambient points must be explicitly forbidden.  analysis found
    # that omitting this exclusion gives spurious solutions outside the ansatz.
    allowed = set(int(x) for x in meta.get('allowed_rank_one', []))
    exclude = ','.join(str(p) for p in range(1, 512) if p not in allowed)
    cmd = [str(dfs_bin), '--constraints', meta['binary_path'], '--target', str(target), '--timeout', str(timeout), '--max-solutions', '1', '--exclude', exclude, '--output', str(out_json), '--used-output', str(used_json)]
    t0 = time.time()
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 60)
    rec = {'schema': 'safe_dfs_run_v1', 'command': cmd, 'returncode': int(proc.returncode), 'elapsed_sec': time.time() - t0,
           'stdout_tail': '\n'.join(proc.stdout.splitlines()[-40:]), 'stderr_tail': '\n'.join(proc.stderr.splitlines()[-80:]),
           'out_json': str(out_json), 'used_rows_json': str(used_json), 'used_rows_sha256': sha256(used_json) if used_json.exists() else None}
    if out_json.exists():
        try:
            rec['result'] = json.loads(out_json.read_text())
        except Exception as e:
            rec['result_parse_error'] = str(e)
    (outdir / f'dfs_len{meta["length"]}_run.json').write_text(json.dumps(rec, indent=2, sort_keys=True) + '\n')
    return rec


def scan_multiset_full(lut: Dict[int, int], multiset: Sequence[int], length: int) -> Dict:
    counts = Counter(int(x) for x in multiset)
    violations = 0; max_excess = 0; excess_total = 0; rows = 0; cap_hist = Counter(); dim_hist = Counter(); head = []
    for key, lb in lut.items():
        dim = int(key) & 0xF
        if dim == 0:
            continue
        basis = unpack_key(key)
        pts = set(span_points_from_basis(basis))
        occ = sum(m for p, m in counts.items() if p in pts)
        cap = int(length) - int(lb)
        rows += 1
        if occ > cap:
            ex = occ - cap; violations += 1; excess_total += ex; max_excess = max(max_excess, ex); cap_hist[cap] += 1; dim_hist[dim] += 1
            if len(head) < 20:
                head.append({'key': str(key), 'basis': list(basis), 'lb': int(lb), 'cap': cap, 'dim': dim, 'occ': occ, 'excess': ex})
    return {'schema': 'full_lut_multiset_scan_v1', 'length': int(length), 'multiset_size': len(multiset),
            'distinct_count': len(counts), 'max_multiplicity': max(counts.values()) if counts else 0,
            'rows_checked': rows, 'violation_count': violations, 'excess_total': excess_total, 'max_excess': max_excess,
            'cap_hist_violated': dict(sorted((int(k), int(v)) for k, v in cap_hist.items())),
            'dim_hist_violated': dict(sorted((int(k), int(v)) for k, v in dim_hist.items())), 'violation_head': head}


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    b = sub.add_parser('build-run')
    b.add_argument('--h-index', type=int, default=0); b.add_argument('--length', type=int, default=20); b.add_argument('--timeout', type=int, default=600)
    b.add_argument('--lut', type=Path, default=DEFAULT_LUT); b.add_argument('--analysis', type=Path, default=DEFAULT_ANALYSIS); b.add_argument('--outroot', type=Path, default=DEFAULT_OUTROOT); b.add_argument('--dfs-bin', type=Path, default=DEFAULT_DFS); b.add_argument('--no-run', action='store_true')
    l = sub.add_parser('ladder')
    l.add_argument('--h-index', type=int, default=0); l.add_argument('--lengths', default='20,21,22,23,24'); l.add_argument('--timeout', type=int, default=600)
    l.add_argument('--lut', type=Path, default=DEFAULT_LUT); l.add_argument('--analysis', type=Path, default=DEFAULT_ANALYSIS); l.add_argument('--outroot', type=Path, default=DEFAULT_OUTROOT); l.add_argument('--dfs-bin', type=Path, default=DEFAULT_DFS)
    s = sub.add_parser('scan-control')
    s.add_argument('--control', type=Path, required=True); s.add_argument('--lengths', default='20,21,22,23,24'); s.add_argument('--lut', type=Path, default=DEFAULT_LUT); s.add_argument('--out', type=Path, default=DEFAULT_OUTROOT/'rank23_full_lut_ladder.json')
    args = ap.parse_args()
    if args.cmd == 'build-run':
        lut = load_lut(args.lut); H = load_H_from_analysis(args.analysis, args.h_index); outdir = args.outroot / f'H{args.h_index:02d}_len{args.length}'
        meta = build_restricted(lut, H, args.length, outdir); dfs = None if args.no_run else run_dfs(meta, args.timeout, args.dfs_bin, outdir)
        summary = {'meta': meta, 'dfs': dfs}
        (outdir / 'summary.json').write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
        print(json.dumps({'outdir': str(outdir), 'rows': meta['rows_written'], 'target': meta['target_rank_one_terms'], 'dfs_complete': None if dfs is None else dfs.get('result',{}).get('complete'), 'dfs_solutions': None if dfs is None else dfs.get('result',{}).get('solutions'), 'dfs_timeout': None if dfs is None else dfs.get('result',{}).get('timeout')}, indent=2, sort_keys=True))
    elif args.cmd == 'ladder':
        lut = load_lut(args.lut); H = load_H_from_analysis(args.analysis, args.h_index); cases=[]
        for n in [int(x) for x in args.lengths.split(',') if x.strip()]:
            outdir = args.outroot / f'H{args.h_index:02d}_len{n}'
            meta = build_restricted(lut, H, n, outdir)
            dfs = run_dfs(meta, args.timeout, args.dfs_bin, outdir)
            cases.append({'length': n, 'meta': meta, 'dfs': dfs})
        out = args.outroot / f'H{args.h_index:02d}_ladder.json'
        out.parent.mkdir(parents=True, exist_ok=True); out.write_text(json.dumps({'schema':'coset_restricted_ladder_v1','h_index':args.h_index,'cases':cases}, indent=2, sort_keys=True)+'\n')
        print(json.dumps({'out': str(out), 'cases': [{'length': c['length'], 'target': c['meta']['target_rank_one_terms'], 'complete': c['dfs'].get('result',{}).get('complete'), 'solutions': c['dfs'].get('result',{}).get('solutions'), 'timeout': c['dfs'].get('result',{}).get('timeout'), 'rows': c['meta']['rows_written']} for c in cases]}, indent=2, sort_keys=True))
    elif args.cmd == 'scan-control':
        lut = load_lut(args.lut); obj = json.loads(args.control.read_text())
        if 'full_a_multiset' in obj:
            ms = obj['full_a_multiset']
        elif 'results' in obj and obj['results']:
            ms = obj['results'][0].get('final_multiset') or obj['results'][0].get('seed')
        else:
            ms = obj.get('a_multiset') or obj.get('support')
        if ms is None:
            raise ValueError('could not find multiset in control')
        recs = [scan_multiset_full(lut, ms, int(n)) for n in args.lengths.split(',') if n.strip()]
        out = {'schema':'rank23_full_lut_ladder_v1','control':str(args.control),'multiset':[int(x) for x in ms],'scans':recs}
        args.out.parent.mkdir(parents=True, exist_ok=True); args.out.write_text(json.dumps(out, indent=2, sort_keys=True)+'\n')
        print(json.dumps({'out':str(args.out),'summary':[{'length':r['length'],'violations':r['violation_count'],'max_excess':r['max_excess']} for r in recs]}, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
