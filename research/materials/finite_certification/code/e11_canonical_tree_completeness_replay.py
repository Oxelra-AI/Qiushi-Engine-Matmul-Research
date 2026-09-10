#!/usr/bin/env python3
"""Regenerate a shallow canonical E11 support tree and compare terminal records.

This complements e11_canonical_tree_replay_verify.py.  It checks that the JSONL
terminal records are not merely individually valid, but complete for the stated
canonical augmentation tree: every generated canonical child either appears as an
eliminated capacity-pruned prefix or, at max depth, as an occupation-feasible leaf.

The check is practical for shallow/tree-pilot depths; a future full depth-19
certificate may need a partitioned version of the same replay logic.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import sys
import time
from collections import Counter
from pathlib import Path

import numpy as np

SCRIPTS_A02 = Path("scripts")
if str(SCRIPTS_A02) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_A02))

from e11_canonical_multiset_tree import (  # noqa: E402
    build_or_load_membership,
    load_perms,
    make_canonical_functions,
    point_caps_from_cache,
    tuple_to_counts,
)
from e11_capacity_incremental_sat import build_or_load_constraint_cache  # noqa: E402


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def load_prefix_set(path: Path, key: str) -> set[tuple[int, ...]]:
    out: set[tuple[int, ...]] = set()
    with path.open() as f:
        for ln, line in enumerate(f, 1):
            if not line.strip():
                continue
            rec = json.loads(line)
            tup = tuple(int(x) for x in rec[key])
            if tup in out:
                raise ValueError(f'duplicate terminal prefix in {path}:{ln}: {tup}')
            out.add(tup)
    return out


def first_violation(occ: np.ndarray, caps: np.ndarray) -> int | None:
    bad = np.flatnonzero(occ > caps)
    return None if len(bad) == 0 else int(bad[0])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--summary', type=Path, required=True)
    ap.add_argument('--out', type=Path, default=None)
    args = ap.parse_args()
    t0 = time.time()
    summary = json.loads(args.summary.read_text())
    files = summary['files']
    max_depth = int(summary['max_depth'])
    if int(summary.get('node_limit', 0)) != 0 or not bool(summary.get('exhausted_declared_tree')):
        raise SystemExit('completeness replay currently expects an exhausted, non-node-limited shallow tree')

    elim_path = Path(files['eliminated_prefixes_jsonl'])
    leaf_path = Path(files['occupation_feasible_leaves_jsonl'])
    frontier_path = Path(files['frontier_jsonl'])
    eliminated_records = load_prefix_set(elim_path, 'prefix')
    leaf_records = load_prefix_set(leaf_path, 'multiset')
    if frontier_path.stat().st_size != 0:
        raise SystemExit('frontier file is nonempty for an exhausted tree')

    cache = build_or_load_constraint_cache(Path('data/wang_f2_lb20/wang_subspace_lut.pkl'), Path(files['cache']), int(summary['rank_s']), False)
    M = build_or_load_membership(cache, Path(files['membership']), False)
    caps = np.asarray(cache['caps'], dtype=np.int16)
    singleton_caps = point_caps_from_cache(cache)
    perms = load_perms(Path(files['perms']))
    canonical, canonical_parent = make_canonical_functions(perms)

    found_elim: set[tuple[int, ...]] = set()
    found_leaf: set[tuple[int, ...]] = set()
    unexpected = []
    counts = Counter()
    root: tuple[int, ...] = tuple()
    stack = [(root, np.zeros(256, dtype=np.int16), np.zeros(len(caps), dtype=np.int16))]
    max_frontier = 0
    while stack:
        max_frontier = max(max_frontier, len(stack))
        ms, mult, occ = stack.pop()
        depth = len(ms)
        counts[f'popped_{depth}'] += 1
        if depth == max_depth:
            # Leaves should have been recorded by parent expansion, but tolerate root max-depth=0.
            found_leaf.add(ms)
            continue
        for p in range(1, 256):
            counts[f'attempt_{depth}'] += 1
            if mult[p] >= singleton_caps[p]:
                counts[f'skip_cap_{depth}'] += 1
                continue
            child = tuple(sorted(ms + (p,)))
            if canonical(child) != child:
                counts[f'skip_noncanon_{depth}'] += 1
                continue
            if canonical_parent(child) != ms:
                counts[f'skip_parent_{depth}'] += 1
                continue
            occ2 = occ + M[p].astype(np.int16)
            bad = first_violation(occ2, caps)
            if bad is not None:
                counts[f'pruned_{len(child)}'] += 1
                found_elim.add(child)
                if child not in eliminated_records and len(unexpected) < 20:
                    unexpected.append({'type': 'missing_eliminated_record', 'prefix': list(child), 'bad_index': bad, 'occ': int(occ2[bad]), 'cap': int(caps[bad])})
                continue
            m2 = mult.copy(); m2[p] += 1
            if len(child) == max_depth:
                counts[f'leaf_{len(child)}'] += 1
                found_leaf.add(child)
                if child not in leaf_records and len(unexpected) < 20:
                    unexpected.append({'type': 'missing_leaf_record', 'prefix': list(child)})
            else:
                stack.append((child, m2, occ2))
                counts[f'pushed_{len(child)}'] += 1

    extra_elim = list(eliminated_records - found_elim)[:20]
    extra_leaf = list(leaf_records - found_leaf)[:20]
    ok = not unexpected and not extra_elim and not extra_leaf and len(found_elim) == len(eliminated_records) and len(found_leaf) == len(leaf_records)
    result = {
        'purpose': 'terminal-completeness replay for canonical E11 A-multiset tree',
        'summary': str(args.summary),
        'max_depth': max_depth,
        'summary_sha256': sha256_file(args.summary),
        'eliminated_record_count': len(eliminated_records),
        'leaf_record_count': len(leaf_records),
        'found_eliminated_count': len(found_elim),
        'found_leaf_count': len(found_leaf),
        'counts': {str(k): int(v) for k, v in sorted(counts.items())},
        'max_frontier_size': int(max_frontier),
        'unexpected_head': unexpected,
        'extra_eliminated_records_head': [list(x) for x in extra_elim],
        'extra_leaf_records_head': [list(x) for x in extra_leaf],
        'all_terminal_records_complete': bool(ok),
        'meaning': 'This verifies completeness of the emitted terminal records for the stated shallow canonical tree; it is not a depth-19 occupation proof unless applied to an exhausted depth-19 tree.',
        'elapsed_sec': time.time() - t0,
    }
    out = args.out or args.summary.with_name(args.summary.stem + '_terminal_completeness.json')
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True)[:5000])
    print(f'wrote {out}')
    if not ok:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
