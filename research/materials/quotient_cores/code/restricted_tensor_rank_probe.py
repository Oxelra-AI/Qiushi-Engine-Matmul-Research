#!/usr/bin/env python3
"""Targeted exact rank probes for Wang A-side restricted tensors over F2.

Given a Wang rowspace Phi <= (F2^9)^* (specified by a LUT key or by basis
masks), build the A-restricted tensor T_{<3,3,3>}|_{Phi=0} and encode the
existence of a rank <= r decomposition over F2 as a DIMACS formula.  CaDiCaL
plus drat-trim then gives a proof object when UNSAT; a SAT model is decoded and
checked as an exact upper-bound witness for that restricted tensor.

This is meant to test whether selected Wang table entries L(Phi) can be raised
by one.  For example, if the LUT says L(Phi)=15 and this script proves UNSAT
for r=15, then the entry can be strengthened to 16 (after independent review of
this encoding/proof), which tightens the T-level occupation cap from s-15 to
s-16.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wang_capacity_lazy import (  # noqa: E402
    N,
    in_rowspace,
    matrix_rank_of_mask,
    pack_basis,
    rref_basis,
    subspace_points_from_basis,
    unpack_basis,
)


def sha256(path: Path) -> str | None:
    if not path.exists() or not path.is_file():
        return None
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(4 * 1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def mask_to_vec(mask: int, n: int) -> List[int]:
    return [(mask >> i) & 1 for i in range(n)]


def vec_to_mask(bits: Sequence[int]) -> int:
    out = 0
    for i, b in enumerate(bits):
        if int(b) & 1:
            out |= 1 << i
    return out


def build_matmul_tensor_f2() -> np.ndarray:
    """research convention: A_ij, B_jk, C_ik all row-major."""
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3 * i + j, 3 * j + k, 3 * i + k] = 1
    return T


def apply_a_constraints(T: np.ndarray, basis: Sequence[int]) -> Tuple[np.ndarray, List[int], List[int]]:
    """Apply RREF A-side linear constraints and drop pivot slices.

    The row convention matches core/constraints.h and wang_capacity_lazy: each
    row's leading bit is its pivot and the equation is a_pivot = sum free a_i
    over F2.  Applying constraints to the tensor folds the pivot A-slice into
    every free coordinate named in that row, then zeroes the pivot slice.
    """
    b = rref_basis(basis, n=N)
    result = T.copy()
    pivots: List[int] = []
    for row in b:
        if row == 0:
            continue
        pivot = row.bit_length() - 1
        free = row ^ (1 << pivot)
        for i in range(N):
            if (free >> i) & 1:
                result[i, :, :] ^= result[pivot, :, :]
        result[pivot, :, :] = 0
        pivots.append(pivot)
    pivot_set = set(pivots)
    keep = [i for i in range(N) if i not in pivot_set]
    core = result[keep, :, :].copy()
    return core, keep, pivots


def f2_rank_matrix(M: np.ndarray) -> int:
    A = (M.copy().astype(np.uint8) & 1)
    rows, cols = A.shape
    rank = 0
    for col in range(cols):
        piv = None
        for r in range(rank, rows):
            if A[r, col] & 1:
                piv = r
                break
        if piv is None:
            continue
        if piv != rank:
            A[[rank, piv]] = A[[piv, rank]]
        for r in range(rows):
            if r != rank and (A[r, col] & 1):
                A[r] ^= A[rank]
        rank += 1
        if rank == rows:
            break
    return int(rank)


def flattening_ranks(T: np.ndarray) -> Dict[str, int]:
    na, nb, nc = T.shape
    return {
        'A': f2_rank_matrix(T.reshape(na, nb * nc)),
        'B': f2_rank_matrix(np.transpose(T, (1, 0, 2)).reshape(nb, na * nc)),
        'C': f2_rank_matrix(np.transpose(T, (2, 0, 1)).reshape(nc, na * nb)),
    }


class DimacsWriter:
    def __init__(self, final_path: Path):
        self.final_path = final_path
        self.body_path = final_path.with_suffix(final_path.suffix + '.body.tmp')
        self.final_path.parent.mkdir(parents=True, exist_ok=True)
        self.fh = self.body_path.open('w')
        self.nclauses = 0
        self.empty_clause_count = 0

    def add_clause(self, lits: Sequence[int]) -> None:
        self.fh.write(' '.join(str(x) for x in lits) + ' 0\n')
        self.nclauses += 1
        if not lits:
            self.empty_clause_count += 1

    def close(self, num_vars: int) -> None:
        self.fh.close()
        with self.final_path.open('w') as out:
            out.write(f'p cnf {num_vars} {self.nclauses}\n')
            with self.body_path.open('r') as body:
                shutil.copyfileobj(body, out, length=16 * 1024 * 1024)
        self.body_path.unlink(missing_ok=True)


class RankCNF:
    def __init__(self, T: np.ndarray, rank: int, cnf_path: Path):
        self.T = T.astype(np.uint8) & 1
        self.na, self.nb, self.nc = self.T.shape
        self.rank = rank
        self.writer = DimacsWriter(cnf_path)
        self.next_var = 1
        self.var_map: Dict[Tuple[str, int, int], int] = {}
        self.pair_vars: Dict[Tuple[int, int, int], int] = {}
        self.cube_vars: Dict[Tuple[int, int, int, int], int] = {}

    def new_var(self) -> int:
        v = self.next_var
        self.next_var += 1
        return v

    def base_var(self, kind: str, t: int, i: int) -> int:
        key = (kind, t, i)
        v = self.var_map.get(key)
        if v is None:
            v = self.new_var()
            self.var_map[key] = v
        return v

    def u_var(self, t: int, a: int) -> int:
        return self.base_var('u', t, a)

    def v_var(self, t: int, b: int) -> int:
        return self.base_var('v', t, b)

    def w_var(self, t: int, c: int) -> int:
        return self.base_var('w', t, c)

    def add_clause(self, lits: Sequence[int]) -> None:
        self.writer.add_clause(lits)

    def encode_and(self, x: int, y: int) -> int:
        z = self.new_var()
        # z <-> x AND y
        self.add_clause([-x, -y, z])
        self.add_clause([x, -z])
        self.add_clause([y, -z])
        return z

    def encode_xor_equals(self, lits: List[int], target: int) -> None:
        if not lits:
            if target:
                self.add_clause([])
            return
        if len(lits) == 1:
            self.add_clause([lits[0] if target else -lits[0]])
            return
        prev = lits[0]
        for i in range(1, len(lits)):
            cur = lits[i]
            if i < len(lits) - 1:
                z = self.new_var()
                # z = prev XOR cur
                self.add_clause([-prev, -cur, -z])
                self.add_clause([prev, cur, -z])
                self.add_clause([prev, -cur, z])
                self.add_clause([-prev, cur, z])
                prev = z
            else:
                # prev XOR cur == target
                if target:
                    self.add_clause([-prev, -cur])
                    self.add_clause([prev, cur])
                else:
                    self.add_clause([-prev, cur])
                    self.add_clause([prev, -cur])

    def encode(self) -> dict:
        t0 = time.time()
        r = self.rank
        # Base variables, allocated deterministically for later model decoding.
        for t in range(r):
            for a in range(self.na):
                self.u_var(t, a)
            for b in range(self.nb):
                self.v_var(t, b)
            for c in range(self.nc):
                self.w_var(t, c)
        base_var_count = self.next_var - 1

        for t in range(r):
            for a in range(self.na):
                ua = self.u_var(t, a)
                for b in range(self.nb):
                    self.pair_vars[(t, a, b)] = self.encode_and(ua, self.v_var(t, b))
        pair_var_count = self.next_var - 1 - base_var_count
        pair_clause_count = self.writer.nclauses

        xor_clause_start = self.writer.nclauses
        cube_var_start = self.next_var
        for a in range(self.na):
            for b in range(self.nb):
                for c in range(self.nc):
                    cubes = []
                    for t in range(r):
                        q = self.encode_and(self.pair_vars[(t, a, b)], self.w_var(t, c))
                        self.cube_vars[(t, a, b, c)] = q
                        cubes.append(q)
                    self.encode_xor_equals(cubes, int(self.T[a, b, c]))
        cube_and_xor_clause_count = self.writer.nclauses - xor_clause_start
        cube_var_count = self.na * self.nb * self.nc * r
        xor_aux_count = (self.next_var - cube_var_start) - cube_var_count

        self.writer.close(self.next_var - 1)
        return {
            'num_vars': self.next_var - 1,
            'num_clauses': self.writer.nclauses,
            'empty_clause_count': self.writer.empty_clause_count,
            'base_var_count': base_var_count,
            'pair_var_count': pair_var_count,
            'pair_clause_count': pair_clause_count,
            'cube_var_count': cube_var_count,
            'xor_aux_count': xor_aux_count,
            'cube_and_xor_clause_count': cube_and_xor_clause_count,
            'elapsed_sec': time.time() - t0,
        }

    def decode_assignment(self, true_vars: set[int]) -> List[dict]:
        terms = []
        for t in range(self.rank):
            u = [1 if self.u_var(t, a) in true_vars else 0 for a in range(self.na)]
            v = [1 if self.v_var(t, b) in true_vars else 0 for b in range(self.nb)]
            w = [1 if self.w_var(t, c) in true_vars else 0 for c in range(self.nc)]
            terms.append({'term': t, 'u': u, 'v': v, 'w': w,
                          'u_mask': vec_to_mask(u), 'v_mask': vec_to_mask(v), 'w_mask': vec_to_mask(w),
                          'zero_tensor_term': (not any(u)) or (not any(v)) or (not any(w))})
        return terms


def parse_model_log(path: Path) -> set[int]:
    true_vars: set[int] = set()
    for line in path.read_text(errors='replace').splitlines():
        if not line.startswith('v '):
            continue
        for tok in line.split()[1:]:
            if tok == '0':
                continue
            val = int(tok)
            if val > 0:
                true_vars.add(val)
    return true_vars


def verify_terms(T: np.ndarray, terms: List[dict]) -> dict:
    R = np.zeros_like(T, dtype=np.uint8)
    for term in terms:
        u = np.array(term['u'], dtype=np.uint8)
        v = np.array(term['v'], dtype=np.uint8)
        w = np.array(term['w'], dtype=np.uint8)
        if not any(u) or not any(v) or not any(w):
            continue
        R ^= (u[:, None, None] & v[None, :, None] & w[None, None, :])
    diff = R ^ (T.astype(np.uint8) & 1)
    return {
        'verified': bool(not diff.any()),
        'mismatch_count': int(diff.sum()),
        'nonzero_terms': sum(0 if term['zero_tensor_term'] else 1 for term in terms),
    }


def run_solver(cnf: Path, outdir: Path, time_limit: int, need_model_if_sat: bool) -> dict:
    outdir.mkdir(parents=True, exist_ok=True)
    stem = cnf.stem
    drat = outdir / f'{stem}.drat'
    cad_log = outdir / f'{stem}.cadical.log'
    trim_log = outdir / f'{stem}.drat_trim.log'
    model_log = outdir / f'{stem}.model.log'
    status = {'cnf': str(cnf), 'drat': str(drat), 'cadical_log': str(cad_log), 'drat_trim_log': str(trim_log), 'model_log': str(model_log)}
    cmd = ['cadical', '--unsat', '--binary=false', '-n']
    if time_limit > 0:
        cmd.extend(['-t', str(time_limit)])
    cmd.extend([str(cnf), str(drat)])
    t0 = time.time()
    with cad_log.open('w') as log:
        proc = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, text=True)
    status['cadical_exit'] = proc.returncode
    status['cadical_elapsed_sec'] = time.time() - t0
    status['cadical_result'] = {10: 'SAT', 20: 'UNSAT'}.get(proc.returncode, 'UNKNOWN_OR_ERROR')
    if proc.returncode == 20:
        t1 = time.time()
        with trim_log.open('w') as log:
            trim = subprocess.run(['drat-trim', str(cnf), str(drat)], stdout=log, stderr=subprocess.STDOUT, text=True)
        status['drat_trim_exit'] = trim.returncode
        status['drat_trim_elapsed_sec'] = time.time() - t1
        txt = trim_log.read_text(errors='replace') if trim_log.exists() else ''
        status['drat_trim_verified'] = ('s VERIFIED' in txt)
    else:
        status['drat_trim_exit'] = None
        status['drat_trim_verified'] = False
    if proc.returncode == 10 and need_model_if_sat:
        cmd2 = ['cadical']
        if time_limit > 0:
            cmd2.extend(['-t', str(time_limit)])
        cmd2.append(str(cnf))
        t2 = time.time()
        with model_log.open('w') as log:
            sat2 = subprocess.run(cmd2, stdout=log, stderr=subprocess.STDOUT, text=True)
        status['model_cadical_exit'] = sat2.returncode
        status['model_cadical_elapsed_sec'] = time.time() - t2
        status['model_true_var_count'] = len(parse_model_log(model_log)) if model_log.exists() else 0
    status['hashes'] = {str(p): sha256(p) for p in [cnf, drat, cad_log, trim_log, model_log] if p.exists()}
    status_path = outdir / f'{stem}.status.json'
    status['status_path'] = str(status_path)
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + '\n')
    return status


def parse_basis_arg(s: str) -> Tuple[int, ...]:
    if not s:
        return tuple()
    return tuple(int(x.strip(), 0) for x in s.split(',') if x.strip())


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--key', type=int, default=None, help='packed Wang LUT subspace key')
    ap.add_argument('--basis', default='', help='comma-separated row masks; used if --key absent')
    ap.add_argument('--rank', type=int, required=True, help='target rank r for rank <= r SAT encoding')
    ap.add_argument('--claimed-current-lb', type=int, default=None)
    ap.add_argument('--label', default='restricted_row')
    ap.add_argument('--outdir', type=Path, required=True)
    ap.add_argument('--solve', action='store_true')
    ap.add_argument('--solver-time', type=int, default=300)
    args = ap.parse_args()

    basis = unpack_basis(args.key) if args.key is not None else parse_basis_arg(args.basis)
    basis = rref_basis(basis, n=N)
    key = pack_basis(basis)
    T = build_matmul_tensor_f2()
    core, keep, pivots = apply_a_constraints(T, basis)
    profile = {
        'label': args.label,
        'field': 'F2',
        'session_tensor_convention': 'A_ij, B_jk, C_ik row-major',
        'basis': list(basis),
        'key': key,
        'dim_constraints': len(basis),
        'A_keep_indices': keep,
        'A_pivot_indices': pivots,
        'restricted_tensor_shape': list(core.shape),
        'restricted_tensor_nnz': int(core.sum()),
        'flattening_ranks': flattening_ranks(core),
        'rank_probe': args.rank,
        'claimed_current_lb': args.claimed_current_lb,
        'mathematical_meaning_if_unsat_verified': None,
    }
    if args.claimed_current_lb is not None and args.rank == args.claimed_current_lb:
        profile['mathematical_meaning_if_unsat_verified'] = f'raises this restricted tensor lower bound from {args.claimed_current_lb} to at least {args.claimed_current_lb + 1}'
    args.outdir.mkdir(parents=True, exist_ok=True)
    np.save(args.outdir / f'{args.label}_tensor.npy', core)
    cnf_path = args.outdir / f'{args.label}_rank_le_{args.rank}.cnf'
    meta_path = args.outdir / f'{args.label}_rank_le_{args.rank}.meta.json'
    enc = RankCNF(core, args.rank, cnf_path)
    cnf_meta = enc.encode()
    profile['cnf'] = {'path': str(cnf_path), **cnf_meta}
    profile['tensor_npy'] = str(args.outdir / f'{args.label}_tensor.npy')

    if args.solve:
        status = run_solver(cnf_path, args.outdir, args.solver_time, need_model_if_sat=True)
        profile['solver_status'] = status
        if status.get('cadical_exit') == 10:
            true_vars = parse_model_log(Path(status['model_log'])) if Path(status['model_log']).exists() else set()
            if true_vars:
                terms = enc.decode_assignment(true_vars)
                ver = verify_terms(core, terms)
                profile['sat_decomposition'] = {
                    'terms': terms,
                    'verification': ver,
                    'meaning': 'SAT gives an exact F2 decomposition of the restricted tensor with at most the probed rank; then this Wang entry cannot be raised above the probed rank.',
                }
    profile['hashes'] = {str(p): sha256(p) for p in [cnf_path, meta_path, args.outdir / f'{args.label}_tensor.npy'] if p.exists()}
    meta_path.write_text(json.dumps(profile, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'label': args.label,
        'key': key,
        'basis': list(basis),
        'shape': list(core.shape),
        'nnz': int(core.sum()),
        'flattening_ranks': profile['flattening_ranks'],
        'rank_probe': args.rank,
        'cnf_vars': cnf_meta['num_vars'],
        'cnf_clauses': cnf_meta['num_clauses'],
        'solver': profile.get('solver_status', {}).get('cadical_result'),
        'drat_verified': profile.get('solver_status', {}).get('drat_trim_verified'),
        'sat_verified': profile.get('sat_decomposition', {}).get('verification', {}).get('verified'),
        'meta_path': str(meta_path),
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
