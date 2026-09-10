#!/usr/bin/env python3
"""Verify a fixed-A plain CNF file against the E11 Brent equations.

This script independently reconstructs the sequential-XOR CNF used for a fixed
A-multiset from the tensor core and the A masks.  It does not import the CNF
builder.  It compares the exact clause sequence in the DIMACS file and records
file hashes, variable counts, clause counts, active A-term counts, and the core
hash.  Used with a DRAT-trim verified proof, this binds the proof to the fixed-A
Brent system for that concrete support.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import time
from pathlib import Path

import numpy as np


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def sha256_array(arr: np.ndarray) -> str:
    a = np.ascontiguousarray(arr.astype(np.uint8) & 1)
    return hashlib.sha256(a.tobytes()).hexdigest()


class RebuildCNF:
    def __init__(self):
        self.next_var = 1
        self.clauses: list[list[int]] = []

    def new(self) -> int:
        v = self.next_var
        self.next_var += 1
        return v

    def add(self, cl):
        self.clauses.append([int(x) for x in cl])

    def and_var(self, x: int, y: int) -> int:
        z = self.new()
        # z <-> (x and y)
        self.add([-x, -y, z])
        self.add([x, -z])
        self.add([y, -z])
        return z

    def xor_eq(self, xs, target: int):
        xs = list(xs)
        target = int(target) & 1
        if not xs:
            if target:
                self.add([])
            return
        if len(xs) == 1:
            self.add([xs[0] if target else -xs[0]])
            return
        prev = xs[0]
        for i, curr in enumerate(xs[1:], start=1):
            if i < len(xs) - 1:
                z = self.new()
                # z = prev xor curr
                self.add([-prev, -curr, -z])
                self.add([prev, curr, -z])
                self.add([prev, -curr, z])
                self.add([-prev, curr, z])
                prev = z
            else:
                if target:
                    self.add([-prev, -curr])
                    self.add([prev, curr])
                else:
                    self.add([-prev, curr])
                    self.add([prev, -curr])


def rebuild(core: np.ndarray, us: list[int]):
    T = core.astype(np.uint8) & 1
    m, nv, nw = T.shape
    r = len(us)
    C = RebuildCNF()
    vvar = {}
    wvar = {}
    pvar = {}
    for t in range(r):
        for b in range(nv):
            vvar[(t, b)] = C.new()
        for c in range(nw):
            wvar[(t, c)] = C.new()
    for t in range(r):
        for b in range(nv):
            for c in range(nw):
                pvar[(t, b, c)] = C.and_var(vvar[(t, b)], wvar[(t, c)])
    active_counts = []
    xor_chain_aux = 0
    empty_xor_rhs0 = 0
    empty_xor_rhs1 = 0
    for a in range(m):
        active = [t for t, u in enumerate(us) if (int(u) >> a) & 1]
        active_counts.append(len(active))
        if not active:
            rhs_ones = int(T[a].sum())
            empty_xor_rhs1 += rhs_ones
            empty_xor_rhs0 += nv * nw - rhs_ones
        else:
            xor_chain_aux += max(0, len(active) - 2) * nv * nw
        for b in range(nv):
            for c in range(nw):
                C.xor_eq([pvar[(t, b, c)] for t in active], int(T[a, b, c]))
    return C, {
        'rank': r,
        'core_shape': [int(m), int(nv), int(nw)],
        'active_counts_by_a': active_counts,
        'empty_xor_rhs0': int(empty_xor_rhs0),
        'empty_xor_rhs1': int(empty_xor_rhs1),
        'xor_chain_aux_vars': int(xor_chain_aux),
        'base_vw_p_vars': int(r * (nv + nw + nv * nw)),
    }


def parse_dimacs(path: Path):
    clauses = []
    header = None
    comments = []
    with path.open() as f:
        for ln, line in enumerate(f, 1):
            s = line.strip()
            if not s:
                continue
            if s.startswith('c'):
                comments.append(s)
                continue
            if s.startswith('p '):
                parts = s.split()
                if len(parts) != 4 or parts[1] != 'cnf':
                    raise ValueError(f'bad header line {ln}: {s}')
                header = {'vars': int(parts[2]), 'clauses': int(parts[3]), 'line': ln}
                continue
            vals = [int(x) for x in s.split()]
            if not vals or vals[-1] != 0:
                raise ValueError(f'bad clause line {ln}: {s[:120]}')
            clauses.append(vals[:-1])
    if header is None:
        raise ValueError('missing DIMACS header')
    return header, comments, clauses


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--core', type=Path, default=Path('data/restricted_cores/mask_001_E11_core.npy'))
    ap.add_argument('--u-list', required=True)
    ap.add_argument('--cnf', type=Path, required=True)
    ap.add_argument('--drat', type=Path, default=None)
    ap.add_argument('--drat-trim-log', type=Path, default=None)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    t0 = time.time()
    core = np.load(args.core).astype(np.uint8) & 1
    us = [int(x) for x in args.u_list.split(',') if x.strip()]
    rebuilt, stats = rebuild(core, us)
    header, comments, clauses = parse_dimacs(args.cnf)

    expected_clauses = rebuilt.clauses
    sequence_equal = clauses == expected_clauses
    first_mismatch = None
    if not sequence_equal:
        n = min(len(clauses), len(expected_clauses))
        for i in range(n):
            if clauses[i] != expected_clauses[i]:
                first_mismatch = {'clause_index0': i, 'file': clauses[i], 'expected': expected_clauses[i]}
                break
        if first_mismatch is None and len(clauses) != len(expected_clauses):
            first_mismatch = {'clause_index0': n, 'file_len': len(clauses), 'expected_len': len(expected_clauses)}

    result = {
        'purpose': 'independent translation replay for fixed-A E11 plain CNF',
        'field': 'F2',
        'core': str(args.core),
        'core_sha256_raw_uint8': sha256_array(core),
        'u_masks': us,
        'cnf': str(args.cnf),
        'cnf_sha256': sha256_file(args.cnf),
        'drat': None if args.drat is None else str(args.drat),
        'drat_sha256': None if args.drat is None or not args.drat.exists() else sha256_file(args.drat),
        'drat_trim_log': None if args.drat_trim_log is None else str(args.drat_trim_log),
        'drat_trim_log_sha256': None if args.drat_trim_log is None or not args.drat_trim_log.exists() else sha256_file(args.drat_trim_log),
        'comments_head': comments[:5],
        'header': header,
        'rebuilt': {'vars': rebuilt.next_var - 1, 'clauses': len(expected_clauses), **stats},
        'header_matches_rebuild': bool(header['vars'] == rebuilt.next_var - 1 and header['clauses'] == len(expected_clauses)),
        'file_clause_count_matches_header': bool(len(clauses) == header['clauses']),
        'exact_clause_sequence_matches_rebuild': bool(sequence_equal),
        'first_mismatch': first_mismatch,
        'translation_verified_for_this_cnf': bool(sequence_equal and header['vars'] == rebuilt.next_var - 1 and len(clauses) == header['clauses']),
        'meaning': 'When combined with a verified DRAT proof for this CNF, this binds the proof to the fixed-A Brent equations for this concrete E11 support. It does not cover other supports.',
        'elapsed_sec': time.time() - t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True)[:5000])
    print(f'wrote {args.out}')
    if not result['translation_verified_for_this_cnf']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
