#!/usr/bin/env python3
"""Exact S-level coset-rank test for E11 quotient-lift samples over F2.

Fix a 4-dimensional E11 A-subspace V.  For a quotient CPD pool, collapse each
scheme to S=span{b_j tensor c_j}.  For each distinct S, this script tests the
S-only lift question

    (R_V + V tensor S) intersects sigma_s(V tensor B tensor C),

where s=19-q for a q-term quotient decomposition and R_V is a fixed residual
coset representative determined only by V and the quotient tensor.  This removes
quotient-A and term-order data from the lift test.  It is still only a sampled
S-family unless the S-family itself is certified exhaustive.

The exact test enumerates all residual A-vector multisets satisfying the matrix
rank contraction necessary condition for this S, then runs a fixed-A native-XOR
SAT instance for each multiset.  SAT would give an S-level intersection; if the
S came from a q-term rank-one quotient scheme, rerunning the corresponding
scheme-level lift encoder can decode a full E11 decomposition.  UNSAT for all
valid covers proves no rank<=s residual exists for this particular S.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
import subprocess
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np

SCRIPTS = Path('scripts')
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import e11_quotient_lift_general_sat as glift  # noqa: E402

N_MAT = 81
ROW_MASK = (1 << 9) - 1


def gf2_rank_int(vecs: list[int]) -> int:
    basis: dict[int, int] = {}
    for v in vecs:
        x = int(v)
        while x:
            p = x.bit_length() - 1
            if p in basis:
                x ^= basis[p]
            else:
                basis[p] = x
                break
    return len(basis)


def gf2_rank_rows(rows: list[int]) -> int:
    basis: dict[int, int] = {}
    for r in rows:
        x = int(r)
        while x:
            p = x.bit_length() - 1
            if p in basis:
                x ^= basis[p]
            else:
                basis[p] = x
                break
    return len(basis)


def rref_basis(vecs: list[int], nbits: int = N_MAT) -> tuple[int, ...]:
    basis = [0] * nbits
    for v in vecs:
        x = int(v)
        while x:
            p = x.bit_length() - 1
            if basis[p]:
                x ^= basis[p]
            else:
                basis[p] = x
                break
    for p in range(nbits):
        if not basis[p]:
            continue
        bit = 1 << p
        for q in range(p + 1, nbits):
            if basis[q] & bit:
                basis[q] ^= basis[p]
    return tuple(basis[p] for p in range(nbits - 1, -1, -1) if basis[p])


def basis_hash(basis: tuple[int, ...]) -> str:
    h = hashlib.sha256()
    h.update(len(basis).to_bytes(2, 'little'))
    for x in basis:
        h.update(int(x).to_bytes(11, 'little'))
    return h.hexdigest()


def outer_mask(bmask: int, cmask: int) -> int:
    out = 0
    c = int(cmask)
    for i in range(9):
        if (int(bmask) >> i) & 1:
            out ^= c << (9 * i)
    return out


def rows_from_mask81(mask: int) -> list[int]:
    return [(int(mask) >> (9 * i)) & ROW_MASK for i in range(9)]


def rows_from_matrix(M: np.ndarray) -> list[int]:
    rows = []
    for b in range(9):
        val = 0
        for c in range(9):
            if int(M[b, c]) & 1:
                val |= 1 << c
        rows.append(val)
    return rows


def scheme_s_basis(scheme: np.ndarray) -> tuple[int, ...]:
    q = len(scheme) // 3
    mats = [outer_mask(int(scheme[3 * j + 1]), int(scheme[3 * j + 2])) for j in range(q)]
    return rref_basis(mats)


def quotient_base_residual(prefix: list[int]) -> tuple[np.ndarray, list[int], list[int], np.ndarray]:
    """Return Q slices, ann basis, V-coordinate residual Rcoords, and E11 core."""
    core = glift.build_e11_core()
    ann = glift.annihilator_basis(prefix, 8)
    Q = glift.quotient_core(core, ann)
    duals = glift.solve_linear_duals(ann, 8)  # ann_i(dual_j)=delta_ij
    X0 = np.zeros_like(core)
    for i, d in enumerate(duals):
        for a in range(8):
            if (d >> a) & 1:
                X0[a] ^= Q[i]
    R = core ^ X0
    ann_res_nnz = []
    for l in ann:
        sl = np.zeros((9, 9), dtype=np.uint8)
        for a in range(8):
            if (l >> a) & 1:
                sl ^= R[a]
        ann_res_nnz.append(int(sl.sum()))
    if any(ann_res_nnz):
        raise RuntimeError(f'base residual not in V, ann nnz={ann_res_nnz}')
    phis = glift.find_phi_vectors(prefix, 8)
    Rcoords = np.zeros((4, 9, 9), dtype=np.uint8)
    for k, phi in enumerate(phis):
        for a in range(8):
            if (phi >> a) & 1:
                Rcoords[k] ^= R[a]
    # Check reconstruction.
    recon = np.zeros_like(core)
    for k, u in enumerate(prefix):
        for a in range(8):
            if (u >> a) & 1:
                recon[a] ^= Rcoords[k]
    if int((recon ^ R).sum()):
        raise RuntimeError('V-coordinate residual reconstruction failed')
    return Q, ann, phis, Rcoords


def in_span(vec: int, basis: tuple[int, ...]) -> bool:
    return len(rref_basis(list(basis) + [int(vec)])) == len(basis)


def min_rank_coset(target_rows: list[int], term_rows: list[list[int]]) -> int:
    n = len(term_rows)
    current = list(target_rows)
    best = gf2_rank_rows(current)
    # binary Gray-code traversal; the flipped term at ARTIFACT is ctz(ARTIFACT)
    for step in range(1, 1 << n):
        j = (step & -step).bit_length() - 1
        tr = term_rows[j]
        for b in range(9):
            current[b] ^= tr[b]
        r = gf2_rank_rows(current)
        if r < best:
            best = r
            if best == 0:
                # zero is final for this coset; still cannot early exit safely if callers need a hist
                pass
    return int(best)


def m_profile_for_S(Rcoords: np.ndarray, S_basis: tuple[int, ...]) -> dict[int, int]:
    term_rows = [rows_from_mask81(x) for x in S_basis]
    R_rows = [rows_from_matrix(Rcoords[k]) for k in range(4)]
    out: dict[int, int] = {}
    for phi in range(1, 16):
        target = [0] * 9
        for k in range(4):
            if (phi >> k) & 1:
                for b in range(9):
                    target[b] ^= R_rows[k][b]
        out[phi] = min_rank_coset(target, term_rows)
    return out


def enumerate_covers(m_by_phi_tuple: tuple[int, ...], s: int) -> list[list[int]]:
    m_by_phi = {phi: m_by_phi_tuple[phi - 1] for phi in range(1, 16)}
    vectors = list(range(1, 16))
    covers: list[list[int]] = []
    for k in range(s + 1):
        for tup in itertools.combinations_with_replacement(vectors, k):
            cnt = Counter(tup)
            ok = True
            for phi in range(1, 16):
                cov = sum(n for v, n in cnt.items() if ((phi & v).bit_count() & 1))
                if cov < m_by_phi[phi]:
                    ok = False
                    break
            if ok:
                covers.append([int(x) for x in tup])
    return covers


class XCNF:
    def __init__(self):
        self.next = 1
        self.cnf: list[list[int]] = []
        self.xors: list[tuple[list[int], int]] = []

    def new(self) -> int:
        v = self.next
        self.next += 1
        return v

    def add(self, lits) -> None:
        self.cnf.append([int(x) for x in lits])

    def add_and(self, z: int, a: int, b: int) -> None:
        self.add([-a, -b, z])
        self.add([a, -z])
        self.add([b, -z])

    def add_xor(self, lits, rhs: int) -> None:
        ll = [int(x) for x in lits]
        rhs = int(rhs) & 1
        if not ll:
            if rhs:
                self.add([])
            return
        self.xors.append((ll, rhs))

    def write_native(self, path: Path, comments=None) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('w') as f:
            for c in comments or []:
                f.write('c ' + str(c) + '\n')
            f.write(f'p cnf {self.next - 1} {len(self.cnf) + len(self.xors)}\n')
            for lits, rhs in self.xors:
                ll = list(lits)
                if rhs == 0:
                    ll[0] = -ll[0]
                f.write('x ' + ' '.join(map(str, ll)) + ' 0\n')
            for cl in self.cnf:
                f.write(' '.join(map(str, cl)) + ' 0\n')


class FixedASSubspaceSAT:
    def __init__(self, Rcoords: np.ndarray, S_basis: tuple[int, ...], a_assignment: list[int]):
        self.Rcoords = np.array(Rcoords, dtype=np.uint8) & 1
        self.S_basis = S_basis
        self.S_rows = [rows_from_mask81(x) for x in S_basis]
        self.a_assign = [int(a) for a in a_assignment]
        self.s = len(a_assignment)
        self.d = len(S_basis)
        self.F = XCNF()
        self.corr: dict[tuple[int, int], int] = {}
        self.bvar: dict[tuple[int, int], int] = {}
        self.cvar: dict[tuple[int, int], int] = {}
        self.pvar: dict[tuple[int, int, int], int] = {}
        self._build()

    def _build(self) -> None:
        for k in range(4):
            for j in range(self.d):
                self.corr[(k, j)] = self.F.new()
        for t in range(self.s):
            for b in range(9):
                self.bvar[(t, b)] = self.F.new()
            for c in range(9):
                self.cvar[(t, c)] = self.F.new()
            self.F.add([self.bvar[(t, b)] for b in range(9)])
            self.F.add([self.cvar[(t, c)] for c in range(9)])
        for t in range(self.s):
            for b in range(9):
                for c in range(9):
                    z = self.F.new()
                    self.pvar[(t, b, c)] = z
                    self.F.add_and(z, self.bvar[(t, b)], self.cvar[(t, c)])
        for k in range(4):
            for b in range(9):
                for c in range(9):
                    lits: list[int] = []
                    bit = 1 << c
                    for j, rows in enumerate(self.S_rows):
                        if rows[b] & bit:
                            lits.append(self.corr[(k, j)])
                    for t in range(self.s):
                        if (self.a_assign[t] >> k) & 1:
                            lits.append(self.pvar[(t, b, c)])
                    self.F.add_xor(lits, int(self.Rcoords[k, b, c]))


def solve_native(cnf_path: Path, solver: str, timeout: int, threads: int) -> dict:
    cmd = [solver, '--verb', '0', '-t', str(threads), '--maxtime', str(timeout), str(cnf_path)]
    t0 = time.time()
    try:
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              text=True, timeout=timeout + 20)
        status = 'UNKNOWN'
        if re.search(r'\bUNSATISFIABLE\b', proc.stdout):
            status = 'UNSAT'
        elif re.search(r'\bSATISFIABLE\b', proc.stdout):
            status = 'SAT'
        return {
            'status': status,
            'elapsed_sec': time.time() - t0,
            'returncode': proc.returncode,
            'stdout_tail': proc.stdout[-1000:],
            'stderr_tail': proc.stderr[-500:],
            'command': ' '.join(cmd),
        }
    except subprocess.TimeoutExpired as exc:
        return {
            'status': 'TIMEOUT',
            'elapsed_sec': time.time() - t0,
            'returncode': None,
            'stdout_tail': (exc.stdout or '')[-1000:] if isinstance(exc.stdout, str) else '',
            'stderr_tail': (exc.stderr or '')[-500:] if isinstance(exc.stderr, str) else '',
            'command': ' '.join(cmd),
        }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--prefix', required=True)
    ap.add_argument('--pool', type=Path, required=True)
    ap.add_argument('--rank-res', type=int, default=8)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--workdir', type=Path, required=True)
    ap.add_argument('--solver', default='cryptominisat5')
    ap.add_argument('--threads', type=int, default=4)
    ap.add_argument('--timeout-per-cover', type=int, default=30)
    ap.add_argument('--max-S', type=int, default=0)
    ap.add_argument('--max-covers-per-S', type=int, default=0)
    ap.add_argument('--keep-first-cnf', action='store_true')
    ap.add_argument('--stop-on-first-sat', action='store_true')
    args = ap.parse_args()

    t0 = time.time()
    prefix = [int(x) for x in args.prefix.split(',') if x.strip()]
    if len(prefix) != 4 or gf2_rank_int(prefix) != 4:
        raise ValueError('prefix must be an independent 4-tuple')
    pool = np.load(args.pool)
    q = pool.shape[1] // 3
    Q, ann, phis, Rcoords = quotient_base_residual(prefix)

    # Distinct S subspaces and representative schemes.
    basis_to_schemes: dict[tuple[int, ...], list[int]] = defaultdict(list)
    for i, scheme in enumerate(pool):
        basis_to_schemes[scheme_s_basis(scheme)].append(i)
    S_list = sorted(basis_to_schemes.keys())
    if args.max_S:
        S_list = S_list[:args.max_S]

    args.workdir.mkdir(parents=True, exist_ok=True)
    cover_cache: dict[tuple[int, ...], list[list[int]]] = {}
    records = []
    status_counter = Counter()
    sat_record = None
    cnf_saved = False

    for sidx, S_basis in enumerate(S_list):
        # Verify quotient slice containment.
        q_masks = []
        for i in range(Q.shape[0]):
            q_masks.append(0)
            for b in range(9):
                row = 0
                for c in range(9):
                    if int(Q[i, b, c]) & 1:
                        row |= 1 << c
                q_masks[-1] |= row << (9 * b)
        q_in_S = [in_span(m, S_basis) for m in q_masks]
        rec = {
            'S_index': int(sidx),
            'S_hash': basis_hash(S_basis),
            'S_dim': len(S_basis),
            'scheme_indices': basis_to_schemes[S_basis],
            'scheme_multiplicity': len(basis_to_schemes[S_basis]),
            'quotient_slices_in_S': q_in_S,
        }
        if not all(q_in_S):
            rec['status'] = 'BAD_S_DOES_NOT_CONTAIN_Q'
            records.append(rec)
            status_counter[rec['status']] += 1
            continue

        m_by_phi = m_profile_for_S(Rcoords, S_basis)
        m_tuple = tuple(m_by_phi[phi] for phi in range(1, 16))
        if m_tuple not in cover_cache:
            cover_cache[m_tuple] = enumerate_covers(m_tuple, args.rank_res)
        covers = cover_cache[m_tuple]
        if args.max_covers_per_S:
            test_covers = covers[:args.max_covers_per_S]
        else:
            test_covers = covers
        rec.update({
            'm_by_phi': {str(k): int(v) for k, v in m_by_phi.items()},
            'sum_m_phi': int(sum(m_by_phi.values())),
            'rank_res': int(args.rank_res),
            'eight_s_bound': int(8 * args.rank_res),
            'valid_cover_count': len(covers),
            'valid_covers_head': covers[:20],
            'covers_tested': len(test_covers),
            'cover_status_counts': {},
            'cover_records': [],
        })
        if not covers:
            rec['status'] = 'NO_VALID_COVER'
            records.append(rec)
            status_counter[rec['status']] += 1
            print(f'S {sidx}/{len(S_list)} no valid cover sum_m={rec["sum_m_phi"]}')
            continue

        local_counts = Counter()
        for cidx, cover in enumerate(test_covers):
            enc = FixedASSubspaceSAT(Rcoords, S_basis, cover)
            cnf_path = args.workdir / f'S{sidx:04d}_cover{cidx:03d}.xor.cnf'
            keep = args.keep_first_cnf and not cnf_saved
            enc.F.write_native(cnf_path, [
                'S-level fixed-A coset rank test',
                f'prefix={prefix}',
                f'S_index={sidx} S_hash={basis_hash(S_basis)}',
                f'cover={cover}',
                f'rank_res={args.rank_res}',
            ])
            sol = solve_native(cnf_path, args.solver, args.timeout_per_cover, args.threads)
            if keep:
                cnf_saved = True
                cnf_kept_path = str(cnf_path)
            else:
                cnf_kept_path = None
                if cnf_path.exists() and sol['status'] != 'SAT':
                    cnf_path.unlink()
            crec = {
                'cover_index': int(cidx),
                'cover': cover,
                'vars': enc.F.next - 1,
                'cnf_clauses': len(enc.F.cnf),
                'xor_clauses': len(enc.F.xors),
                'solve': sol,
                'cnf_path': cnf_kept_path,
            }
            rec['cover_records'].append(crec)
            local_counts[sol['status']] += 1
            if sol['status'] == 'SAT':
                sat_record = {'S_record': rec, 'cover_record': crec}
                if args.stop_on_first_sat:
                    break
        rec['cover_status_counts'] = dict(local_counts)
        if local_counts.get('SAT', 0):
            rec['status'] = 'SAT_S_INTERSECTION_FOUND'
        elif local_counts.get('TIMEOUT', 0) or local_counts.get('UNKNOWN', 0):
            rec['status'] = 'UNRESOLVED_COVERS'
        elif len(test_covers) < len(covers):
            rec['status'] = 'PARTIAL_COVERS_TESTED'
        else:
            rec['status'] = 'ALL_COVERS_UNSAT'
        records.append(rec)
        status_counter[rec['status']] += 1
        print(f'S {sidx+1}/{len(S_list)} dim={len(S_basis)} mult={rec["scheme_multiplicity"]} '
              f'sum_m={rec["sum_m_phi"]} covers={len(covers)} status={rec["status"]} counts={dict(local_counts)}')
        if sat_record is not None and args.stop_on_first_sat:
            break

    m_profile_dist = Counter(tuple(r.get('m_by_phi', {}).get(str(phi)) for phi in range(1, 16)) for r in records if 'm_by_phi' in r)
    cover_count_dist = Counter(r.get('valid_cover_count') for r in records if 'valid_cover_count' in r)
    result = {
        'purpose': 'exact S-only lift test for distinct matrix subspaces S obtained from quotient CPD pool',
        'field': 'F2',
        'prefix': prefix,
        'annihilator_basis': ann,
        'phi_vectors': phis,
        'pool': str(args.pool),
        'pool_shape': list(pool.shape),
        'q_terms': int(q),
        'rank_residual_budget': int(args.rank_res),
        'distinct_S_total_in_pool': len(basis_to_schemes),
        'distinct_S_tested': len(records),
        'status_counts': dict(status_counter),
        'm_profile_distribution_count': len(m_profile_dist),
        'm_profile_distribution_head': [
            {'m_tuple': list(k), 'count': int(v)} for k, v in m_profile_dist.most_common(20)
        ],
        'valid_cover_count_distribution': {str(k): int(v) for k, v in sorted(cover_count_dist.items())},
        'cover_cache_profile_count': len(cover_cache),
        'sat_found': sat_record is not None,
        'meaning': 'For each tested S, ALL_COVERS_UNSAT proves the coset R+V tensor S contains no F2 tensor of rank at most rank_residual_budget. This is an exact S-level exclusion, but only for S spaces sampled by the input quotient pool.',
        'elapsed_sec': time.time() - t0,
        'records': records,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True, default=int) + '\n')
    print(json.dumps({
        'distinct_S_total_in_pool': result['distinct_S_total_in_pool'],
        'distinct_S_tested': result['distinct_S_tested'],
        'status_counts': result['status_counts'],
        'm_profile_distribution_count': result['m_profile_distribution_count'],
        'valid_cover_count_distribution': result['valid_cover_count_distribution'],
        'sat_found': result['sat_found'],
        'elapsed_sec': result['elapsed_sec'],
    }, indent=2, sort_keys=True))
    print('wrote', args.out)


if __name__ == '__main__':
    main()
