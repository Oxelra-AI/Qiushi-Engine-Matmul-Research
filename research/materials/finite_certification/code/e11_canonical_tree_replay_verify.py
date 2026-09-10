#!/usr/bin/env python3
"""Replay-check records emitted by e11_canonical_multiset_tree.py.

The verifier recomputes, from the cached E11 Wang constraints and the verified
quotient permutations, that:
  * eliminated-prefix JSONL records are canonical prefixes whose stored subspace
    is truly over capacity;
  * surviving max-depth leaves are canonical and have no Wang-capacity violation;
  * summary counts and file line counts agree.

This is an execution-level certificate checker for shallow/pilot canonical trees.
For a future full max_depth=19 run, the same checker is the first local replay
ARTIFACT before any mathematical conclusion is drawn from the record.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import sys
import time
from pathlib import Path

import numpy as np

SCRIPTS_A02 = Path("scripts")
if str(SCRIPTS_A02) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_A02))

from e11_canonical_multiset_tree import (  # noqa: E402
    build_or_load_membership,
    counts_to_tuple,
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


def load_jsonl(path: Path):
    with path.open() as f:
        for ln, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                yield ln, json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f'{path}:{ln}: bad JSON: {exc}') from exc


def occupancy(M: np.ndarray, ms: tuple[int, ...]) -> np.ndarray:
    occ = np.zeros(M.shape[1], dtype=np.int16)
    for p in ms:
        occ += M[int(p)].astype(np.int16)
    return occ


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--summary', type=Path, required=True)
    ap.add_argument('--max-record-check', type=int, default=0, help='0 means all records')
    ap.add_argument('--out', type=Path, default=None)
    args = ap.parse_args()
    t0 = time.time()

    summary = json.loads(args.summary.read_text())
    files = summary['files']
    elim_path = Path(files['eliminated_prefixes_jsonl'])
    leaf_path = Path(files['occupation_feasible_leaves_jsonl'])
    frontier_path = Path(files['frontier_jsonl'])
    cache = build_or_load_constraint_cache(Path('data/wang_f2_lb20/wang_subspace_lut.pkl'), Path(files['cache']), int(summary['rank_s']), False)
    M = build_or_load_membership(cache, Path(files['membership']), False)
    caps = np.asarray(cache['caps'], dtype=np.int16)
    singleton_caps = point_caps_from_cache(cache)
    perms = load_perms(Path(files['perms']))
    canonical, canonical_parent = make_canonical_functions(perms)

    errors = []
    elim_checked = 0
    leaf_checked = 0
    frontier_checked = 0
    elim_lines = 0
    leaf_lines = 0
    frontier_lines = 0

    for ln, rec in load_jsonl(elim_path):
        elim_lines += 1
        if args.max_record_check and elim_checked >= args.max_record_check:
            continue
        ms = tuple(int(x) for x in rec['prefix'])
        if canonical(ms) != ms:
            errors.append({'file': str(elim_path), 'line': ln, 'error': 'prefix_not_canonical', 'prefix': list(ms), 'canonical': list(canonical(ms))})
            if len(errors) >= 20: break
        counts = tuple_to_counts(ms)
        if counts_to_tuple(counts) != ms:
            errors.append({'file': str(elim_path), 'line': ln, 'error': 'bad_counts_roundtrip'})
        if np.any(counts[1:] > singleton_caps[1:]):
            errors.append({'file': str(elim_path), 'line': ln, 'error': 'singleton_capacity_exceeded'})
        occ = occupancy(M, ms)
        i = int(rec['subspace_index'])
        if not (0 <= i < len(caps)):
            errors.append({'file': str(elim_path), 'line': ln, 'error': 'bad_subspace_index', 'index': i})
        else:
            expected_occ = int(occ[i])
            expected_excess = expected_occ - int(caps[i])
            if expected_occ != int(rec['occupancy']) or expected_excess != int(rec['excess']) or expected_excess <= 0:
                errors.append({'file': str(elim_path), 'line': ln, 'error': 'violation_mismatch', 'index': i, 'record_occ': rec.get('occupancy'), 'computed_occ': expected_occ, 'record_excess': rec.get('excess'), 'computed_excess': expected_excess, 'cap': int(caps[i])})
        elim_checked += 1
        if len(errors) >= 20:
            break

    if not errors:
        for ln, rec in load_jsonl(leaf_path):
            leaf_lines += 1
            if args.max_record_check and leaf_checked >= args.max_record_check:
                continue
            ms = tuple(int(x) for x in rec['multiset'])
            if len(ms) != int(summary['max_depth']):
                errors.append({'file': str(leaf_path), 'line': ln, 'error': 'wrong_leaf_depth', 'len': len(ms)})
                if len(errors) >= 20: break
            if canonical(ms) != ms:
                errors.append({'file': str(leaf_path), 'line': ln, 'error': 'leaf_not_canonical', 'prefix': list(ms), 'canonical': list(canonical(ms))})
                if len(errors) >= 20: break
            counts = tuple_to_counts(ms)
            if np.any(counts[1:] > singleton_caps[1:]):
                errors.append({'file': str(leaf_path), 'line': ln, 'error': 'leaf_singleton_capacity_exceeded'})
                if len(errors) >= 20: break
            occ = occupancy(M, ms)
            bad = np.flatnonzero(occ > caps)
            if len(bad):
                i = int(bad[0])
                errors.append({'file': str(leaf_path), 'line': ln, 'error': 'leaf_has_wang_violation', 'index': i, 'computed_occ': int(occ[i]), 'cap': int(caps[i]), 'prefix': list(ms)})
                if len(errors) >= 20: break
            leaf_checked += 1

    if not errors:
        for _ln, _rec in load_jsonl(frontier_path):
            frontier_lines += 1
            frontier_checked += 1

    # If max_record_check truncated checking, still compute line counts cheaply by wc-like pass for files not fully iterated.
    def count_lines(path: Path) -> int:
        with path.open('rb') as f:
            return sum(1 for _ in f)

    elim_lines_full = count_lines(elim_path)
    leaf_lines_full = count_lines(leaf_path)
    frontier_lines_full = count_lines(frontier_path)

    expected_pruned = int(summary['pruned_prefix_count'])
    expected_leaves = int(summary['occupation_feasible_leaf_count_at_max_depth'])
    count_ok = (elim_lines_full == expected_pruned and leaf_lines_full == expected_leaves)
    frontier_ok = True
    if bool(summary.get('exhausted_declared_tree')):
        frontier_ok = frontier_lines_full == 0

    result = {
        'purpose': 'replay verification of canonical E11 A-multiset tree record',
        'summary': str(args.summary),
        'summary_sha256': sha256_file(args.summary),
        'eliminated_prefixes': {'path': str(elim_path), 'lines': elim_lines_full, 'sha256': sha256_file(elim_path), 'checked': elim_checked},
        'occupation_feasible_leaves': {'path': str(leaf_path), 'lines': leaf_lines_full, 'sha256': sha256_file(leaf_path), 'checked': leaf_checked},
        'frontier': {'path': str(frontier_path), 'lines': frontier_lines_full, 'sha256': sha256_file(frontier_path), 'checked': frontier_checked},
        'count_ok': bool(count_ok),
        'frontier_ok': bool(frontier_ok),
        'records_checked_completely': bool(args.max_record_check == 0 or (elim_checked == elim_lines_full and leaf_checked == leaf_lines_full)),
        'all_checked_records_valid': not errors,
        'errors_head': errors[:20],
        'meaning': 'For a full depth-19 exhausted tree this replay would check the occupation-level branch record; here it verifies only the stated shallow or node-limited tree.',
        'elapsed_sec': time.time() - t0,
    }
    ok = count_ok and frontier_ok and not errors
    result['all_ok'] = bool(ok)
    out = args.out or args.summary.with_name(args.summary.stem + '_replay_check.json')
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True)[:5000])
    print(f'wrote {out}')
    if not ok:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
