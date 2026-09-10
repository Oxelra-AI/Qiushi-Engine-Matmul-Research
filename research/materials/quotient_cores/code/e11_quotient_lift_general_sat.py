#!/usr/bin/env python3
"""General lift-back SAT for E11 quotient decompositions over F2.

Given a 4-dimensional A-subspace V (specified by a basis/prefix) and a rank-q
CPD of the A-quotient tensor T mod V, decide whether this quotient CPD lifts to
an E11 CPD of rank <= q+4.

This is the exact coset formulation missing from the fixed-basis lift test:
choose arbitrary lift corrections v_j in V for the q quotient terms, and ask
whether the residual tensor in V tensor B tensor C has tensor rank <= 4 with
arbitrary A-factors in V.  In coordinates relative to the chosen V-basis,

  R_{kbc} = sum_j c_{k,j} M_{j,bc} + sum_{t=1}^4 a_{t,k} b_{t,b} d_{t,c},

where M_j = b_j d_j are fixed rank-one matrices from the quotient scheme.
SAT gives an exact E11 rank <= q+4 CPD after independent decode/verification.
UNSAT excludes only this quotient scheme for this V, unless upgraded to a proof
and combined with an exhaustive quotient-scheme generation/certificate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import time
from pathlib import Path

import numpy as np


def parity(x: int) -> int:
    return int(x).bit_count() & 1


def bits_to_vec(mask: int, n: int) -> np.ndarray:
    return np.array([(int(mask) >> i) & 1 for i in range(n)], dtype=np.uint8)


def vec_to_mask(v) -> int:
    return sum(int(v[i]) << i for i in range(len(v)))


def gf2_basis(vectors: list[int]) -> list[int]:
    basis: dict[int, int] = {}
    for v in vectors:
        x = int(v)
        while x:
            p = x.bit_length() - 1
            if p in basis:
                x ^= basis[p]
            else:
                basis[p] = x
                break
    return sorted(basis.values(), reverse=True)


def gf2_rank_int(vectors: list[int]) -> int:
    return len(gf2_basis(vectors))


def annihilator_basis(prefix: list[int], n: int = 8) -> list[int]:
    d = gf2_rank_int(prefix)
    out: list[int] = []
    for l in range(1, 1 << n):
        if all(parity(l & v) == 0 for v in prefix):
            if gf2_rank_int(out + [l]) > len(out):
                out.append(l)
                if len(out) == n - d:
                    return out
    raise RuntimeError("annihilator basis not found")


def solve_linear_duals(rows_masks: list[int], n: int) -> list[int]:
    """Return x_i with row_k dot x_i = delta_ki for independent rows."""
    d = len(rows_masks)
    M = np.zeros((d, n), dtype=np.uint8)
    for k, m in enumerate(rows_masks):
        for b in range(n):
            M[k, b] = (m >> b) & 1
    duals: list[int] = []
    for i in range(d):
        target = np.zeros(d, dtype=np.uint8)
        target[i] = 1
        aug = np.hstack([M.copy(), target.reshape(-1, 1)])
        row = 0
        pivots: list[tuple[int, int]] = []
        for col in range(n):
            piv = None
            for r in range(row, d):
                if aug[r, col]:
                    piv = r
                    break
            if piv is None:
                continue
            aug[[row, piv]] = aug[[piv, row]]
            for r in range(d):
                if r != row and aug[r, col]:
                    aug[r] ^= aug[row]
            pivots.append((row, col))
            row += 1
        if row != d:
            raise RuntimeError("dependent row masks")
        x = np.zeros(n, dtype=np.uint8)
        for r, c in pivots:
            x[c] = aug[r, n]
        duals.append(vec_to_mask(x))
    return duals


def find_phi_vectors(prefix_masks: list[int], n: int = 8) -> list[int]:
    # phi_i(prefix_j)=delta_ij
    return solve_linear_duals(prefix_masks, n)


def build_t333() -> np.ndarray:
    T = np.zeros((9, 9, 9), dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                T[3 * i + j, 3 * j + k, 3 * i + k] = 1
    return T


def build_e11_core() -> np.ndarray:
    return build_t333()[1:, :, :]


def quotient_core(core: np.ndarray, ann: list[int]) -> np.ndarray:
    q = np.zeros((len(ann), core.shape[1], core.shape[2]), dtype=np.uint8)
    for i, l in enumerate(ann):
        for a in range(core.shape[0]):
            if (l >> a) & 1:
                q[i] ^= core[a]
    return q


def apply_terms(shape, us: list[int], vs: list[int], ws: list[int]) -> np.ndarray:
    out = np.zeros(shape, dtype=np.uint8)
    for u, v, w in zip(us, vs, ws):
        if u == 0 or v == 0 or w == 0:
            continue
        U = bits_to_vec(u, shape[0]).reshape(-1, 1, 1)
        V = bits_to_vec(v, shape[1]).reshape(1, -1, 1)
        W = bits_to_vec(w, shape[2]).reshape(1, 1, -1)
        out ^= (U * V * W).astype(np.uint8)
    return out


def sha256_file(path: Path) -> str | None:
    if not path.exists():
        return None
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


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
        # z <-> a & b
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


def parse_model(stdout: str) -> list[int]:
    vals: list[int] = []
    for line in stdout.splitlines():
        if line.startswith('v'):
            for tok in line.split()[1:]:
                try:
                    z = int(tok)
                except ValueError:
                    continue
                if z:
                    vals.append(z)
    return vals


def solve_native(cnf_path: Path, solver: str, timeout: int, threads: int) -> dict:
    cmd = [solver, '--verb', '0', '-t', str(threads), '--maxtime', str(timeout), str(cnf_path)]
    t0 = time.time()
    try:
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=timeout + 20)
        status = 'UNKNOWN'
        if re.search(r'\bUNSATISFIABLE\b', proc.stdout):
            status = 'UNSAT'
        elif re.search(r'\bSATISFIABLE\b', proc.stdout):
            status = 'SAT'
        return {
            'command': ' '.join(cmd),
            'returncode': proc.returncode,
            'status': status,
            'elapsed_sec': time.time() - t0,
            'stdout_tail': proc.stdout[-3000:],
            'stderr_tail': proc.stderr[-2000:],
            'model': parse_model(proc.stdout) if status == 'SAT' else None,
        }
    except subprocess.TimeoutExpired as exc:
        return {
            'command': ' '.join(cmd),
            'returncode': None,
            'status': 'TIMEOUT',
            'elapsed_sec': time.time() - t0,
            'stdout_tail': (exc.stdout or '')[-3000:] if isinstance(exc.stdout, str) else '',
            'stderr_tail': (exc.stderr or '')[-2000:] if isinstance(exc.stderr, str) else '',
            'model': None,
        }


class GeneralLiftSAT:
    def __init__(self, Rcoords: np.ndarray, M_rows: list[list[int]], rank_res: int = 4, force_nonzero_res_a: bool = False):
        self.Rcoords = Rcoords.astype(np.uint8) & 1  # (4,9,9)
        self.M_rows = M_rows                         # q terms, rows as 9-bit ints
        self.q = len(M_rows)
        self.rank_res = rank_res
        self.F = XCNF()
        self.corr: dict[tuple[int, int], int] = {}
        self.avar: dict[tuple[int, int], int] = {}
        self.bvar: dict[tuple[int, int], int] = {}
        self.wvar: dict[tuple[int, int], int] = {}
        self.pvar: dict[tuple[int, int, int], int] = {}
        self.qvar: dict[tuple[int, int, int, int], int] = {}
        self.force_nonzero_res_a = bool(force_nonzero_res_a)
        self._build()

    def _build(self) -> None:
        # Lift correction variables c_{k,j}
        for k in range(4):
            for j in range(self.q):
                self.corr[(k, j)] = self.F.new()
        # Residual rank <=4 CPD variables in V coordinates.
        for t in range(self.rank_res):
            for k in range(4):
                self.avar[(t, k)] = self.F.new()
            for b in range(9):
                self.bvar[(t, b)] = self.F.new()
            for c in range(9):
                self.wvar[(t, c)] = self.F.new()
            if self.force_nonzero_res_a:
                self.F.add([self.avar[(t, k)] for k in range(4)])
        for t in range(self.rank_res):
            for b in range(9):
                for c in range(9):
                    z = self.F.new()
                    self.pvar[(t, b, c)] = z
                    self.F.add_and(z, self.bvar[(t, b)], self.wvar[(t, c)])
        for t in range(self.rank_res):
            for k in range(4):
                for b in range(9):
                    for c in range(9):
                        z = self.F.new()
                        self.qvar[(t, k, b, c)] = z
                        self.F.add_and(z, self.avar[(t, k)], self.pvar[(t, b, c)])
        for k in range(4):
            for b in range(9):
                for c in range(9):
                    lits: list[int] = []
                    bit = 1 << c
                    for j, rows in enumerate(self.M_rows):
                        if rows[b] & bit:
                            lits.append(self.corr[(k, j)])
                    for t in range(self.rank_res):
                        lits.append(self.qvar[(t, k, b, c)])
                    self.F.add_xor(lits, int(self.Rcoords[k, b, c]))

    def decode(self, model_lits: list[int]) -> tuple[np.ndarray, list[int], list[int], list[int]]:
        pos = {int(x) for x in model_lits if int(x) > 0}
        C = np.zeros((4, self.q), dtype=np.uint8)
        for k in range(4):
            for j in range(self.q):
                if self.corr[(k, j)] in pos:
                    C[k, j] = 1
        res_u: list[int] = []
        res_v: list[int] = []
        res_w: list[int] = []
        for t in range(self.rank_res):
            um = 0
            vm = 0
            wm = 0
            for k in range(4):
                if self.avar[(t, k)] in pos:
                    um |= 1 << k
            for b in range(9):
                if self.bvar[(t, b)] in pos:
                    vm |= 1 << b
            for c in range(9):
                if self.wvar[(t, c)] in pos:
                    wm |= 1 << c
            res_u.append(um)
            res_v.append(vm)
            res_w.append(wm)
        return C, res_u, res_v, res_w


def scheme_to_residual(core: np.ndarray, prefix: list[int], scheme: np.ndarray) -> tuple[dict, np.ndarray, list[int], list[int], list[int], list[int]]:
    ann = annihilator_basis(prefix, 8)
    Q = quotient_core(core, ann)
    qrank = len(scheme) // 3
    q_us = [int(scheme[3 * j]) for j in range(qrank)]
    b_masks = [int(scheme[3 * j + 1]) for j in range(qrank)]
    c_masks = [int(scheme[3 * j + 2]) for j in range(qrank)]
    q_check = apply_terms(Q.shape, q_us, b_masks, c_masks)
    qdiff = int((q_check ^ Q).sum())
    duals = solve_linear_duals(ann, 8)  # ann_i(dual_j)=delta_ij
    lifts: list[int] = []
    for u in q_us:
        a = 0
        for i, d in enumerate(duals):
            if (u >> i) & 1:
                a ^= d
        lifts.append(a)
    R = core ^ apply_terms(core.shape, lifts, b_masks, c_masks)
    # Check R lies in V by applying annihilator: should vanish if qdiff=0.
    ann_res_nnz = []
    for l in ann:
        sl = np.zeros((9, 9), dtype=np.uint8)
        for a in range(8):
            if (l >> a) & 1:
                sl ^= R[a]
        ann_res_nnz.append(int(sl.sum()))
    phis = find_phi_vectors(prefix, 8)
    Rcoords = np.zeros((4, 9, 9), dtype=np.uint8)
    for k, phi in enumerate(phis):
        for a in range(8):
            if (phi >> a) & 1:
                Rcoords[k] ^= R[a]
    # Reconstruct R from V-coordinates.
    recon = np.zeros_like(core)
    for k, u in enumerate(prefix):
        for a in range(8):
            if (u >> a) & 1:
                recon[a] ^= Rcoords[k]
    rdiff = int((recon ^ R).sum())
    M_rows: list[list[int]] = []
    for b, c in zip(b_masks, c_masks):
        rows = []
        for i in range(9):
            rows.append(c if ((b >> i) & 1) else 0)
        M_rows.append(rows)
    meta = {
        'annihilator_basis': ann,
        'phi_vectors': phis,
        'dual_lifts_for_quotient_basis': duals,
        'quotient_diff': qdiff,
        'annihilator_residual_nnz': ann_res_nnz,
        'residual_reconstruction_diff': rdiff,
        'qrank': qrank,
    }
    return meta, Rcoords, lifts, b_masks, c_masks, M_rows


def lift_to_full_e11(core: np.ndarray, prefix: list[int], lifts: list[int], b_masks: list[int], c_masks: list[int], C: np.ndarray, res_u4: list[int], res_v: list[int], res_w: list[int]) -> dict:
    full_u: list[int] = []
    full_v: list[int] = []
    full_w: list[int] = []
    # residual four terms: convert V-coordinate masks into E11 A masks.
    for um4, v, w in zip(res_u4, res_v, res_w):
        u8 = 0
        for k, pk in enumerate(prefix):
            if (um4 >> k) & 1:
                u8 ^= pk
        if u8 and v and w:
            full_u.append(u8); full_v.append(v); full_w.append(w)
    # quotient terms with lift corrections.
    for j, a0 in enumerate(lifts):
        a = a0
        for k, pk in enumerate(prefix):
            if C[k, j] & 1:
                a ^= pk
        if a and b_masks[j] and c_masks[j]:
            full_u.append(a); full_v.append(b_masks[j]); full_w.append(c_masks[j])
    check = apply_terms(core.shape, full_u, full_v, full_w)
    diff = int((check ^ core).sum())
    return {
        'e11_rank_upper_bound': len(full_u),
        'e11_diff': diff,
        'e11_verified': diff == 0,
        'u_masks': full_u,
        'v_masks': full_v,
        'w_masks': full_w,
    }


def lift_e11_to_t333(e11_dec: dict) -> dict:
    T = build_t333()
    u_full = [(int(u) << 1) for u in e11_dec['u_masks']]
    v_full = [int(v) for v in e11_dec['v_masks']]
    w_full = [int(w) for w in e11_dec['w_masks']]
    # Removed a00 slice equals E00*E00 + E00*E11 + E00*E22 in row-major masks.
    u_full.extend([1, 1, 1])
    v_full.extend([1, 2, 4])
    w_full.extend([1, 2, 4])
    check = apply_terms(T.shape, u_full, v_full, w_full)
    diff = int((check ^ T).sum())
    return {
        't333_rank_upper_bound': len(u_full),
        't333_diff': diff,
        't333_verified': diff == 0,
        'u_masks': u_full,
        'v_masks': v_full,
        'w_masks': w_full,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--core', type=Path, default=None)
    ap.add_argument('--pool', type=Path, required=True)
    ap.add_argument('--prefix', required=True, help='comma-separated 4 independent E11 A masks')
    ap.add_argument('--outdir', type=Path, required=True)
    ap.add_argument('--name', default='general_lift')
    ap.add_argument('--scheme-idx', type=int, default=-1, help='-1 tests all schemes')
    ap.add_argument('--max-schemes', type=int, default=0)
    ap.add_argument('--rank-res', type=int, default=4, help='number of residual rank-one terms allowed in the prefix span')
    ap.add_argument('--timeout-per-scheme', type=int, default=60)
    ap.add_argument('--threads', type=int, default=4)
    ap.add_argument('--solver', default='cryptominisat5')
    ap.add_argument('--keep-cnf', action='store_true')
    ap.add_argument('--stop-on-first-sat', action='store_true')
    args = ap.parse_args()

    t0 = time.time()
    args.outdir.mkdir(parents=True, exist_ok=True)
    prefix = [int(x) for x in args.prefix.split(',') if x.strip()]
    if len(prefix) != 4 or gf2_rank_int(prefix) != 4:
        raise ValueError('prefix must be a comma-separated independent 4-tuple')
    core = (np.load(args.core).astype(np.uint8) & 1) if args.core else build_e11_core()
    if core.shape != (8, 9, 9):
        raise ValueError(f'expected E11 core shape (8,9,9), got {core.shape}')
    pool = np.load(args.pool)
    indices = [args.scheme_idx] if args.scheme_idx >= 0 else list(range(pool.shape[0]))
    if args.max_schemes > 0:
        indices = indices[:args.max_schemes]

    records = []
    first_witness = None
    for pos_idx, idx in enumerate(indices):
        scheme = pool[idx]
        meta, Rcoords, lifts, b_masks, c_masks, M_rows = scheme_to_residual(core, prefix, scheme)
        rec = {'scheme_idx': int(idx), **meta}
        if meta['quotient_diff'] or meta['residual_reconstruction_diff'] or any(meta['annihilator_residual_nnz']):
            rec['status'] = 'BAD_QUOTIENT_OR_RESIDUAL'
            records.append(rec)
            continue
        enc = GeneralLiftSAT(Rcoords, M_rows, rank_res=args.rank_res)
        cnf_path = args.outdir / f'{args.name}_scheme{idx}.xor.cnf'
        enc.F.write_native(cnf_path, [
            'general E11 quotient lift SAT',
            f'prefix={prefix}',
            f'pool={args.pool}',
            f'scheme_idx={idx}',
            f'semantics: arbitrary V-lift corrections plus rank<={args.rank_res} residual CPD in V',
        ])
        solve = solve_native(cnf_path, args.solver, args.timeout_per_scheme, args.threads)
        model = solve.pop('model', None)
        rec.update({
            'vars': enc.F.next - 1,
            'cnf_clauses': len(enc.F.cnf),
            'native_xor_clauses': len(enc.F.xors),
            'cnf_path': str(cnf_path) if args.keep_cnf else None,
            'cnf_sha256': sha256_file(cnf_path),
            'solve': solve,
        })
        if solve.get('status') == 'SAT' and model:
            C, res_u4, res_v, res_w = enc.decode(model)
            e11_dec = lift_to_full_e11(core, prefix, lifts, b_masks, c_masks, C, res_u4, res_v, res_w)
            rec['decoded_general_lift'] = {
                'correction_matrix_rows_k_cols_j': C.astype(int).tolist(),
                'residual_u_masks_in_V_coords': res_u4,
                'residual_v_masks': res_v,
                'residual_w_masks': res_w,
                'model_lit_count': len(model),
            }
            rec['e11_decomposition'] = e11_dec
            if e11_dec['e11_verified']:
                rec['t333_decomposition'] = lift_e11_to_t333(e11_dec)
                first_witness = rec
                print(f"SCHEME {idx}: SAT verified E11 rank <= {e11_dec['e11_rank_upper_bound']}")
                if rec['t333_decomposition']['t333_verified']:
                    print(f"SCHEME {idx}: FULL T333 rank <= {rec['t333_decomposition']['t333_rank_upper_bound']} verified")
                if args.stop_on_first_sat:
                    records.append(rec)
                    break
        if not args.keep_cnf and cnf_path.exists() and solve.get('status') != 'SAT':
            cnf_path.unlink()
            rec['cnf_path'] = None
        records.append(rec)
        if pos_idx < 5 or pos_idx % 25 == 0 or solve.get('status') != 'UNSAT':
            print(f"scheme {idx}: {solve.get('status')} elapsed={solve.get('elapsed_sec'):.2f}s vars={rec['vars']} xors={rec['native_xor_clauses']}")

    counts = {}
    for r in records:
        st = r.get('solve', {}).get('status', r.get('status', 'UNKNOWN'))
        counts[st] = counts.get(st, 0) + 1
    summary = {
        'purpose': 'exact general coset lift-back for E11 quotient schemes over F2',
        'field': 'F2',
        'prefix_basis': prefix,
        'pool': str(args.pool),
        'residual_rank_budget': int(args.rank_res),
        'total_rank_budget': int(args.rank_res + (pool.shape[1] // 3)),
        'schemes_requested': len(indices),
        'schemes_recorded': len(records),
        'status_counts': counts,
        'witness_found': first_witness is not None,
        'first_witness_scheme_idx': None if first_witness is None else first_witness['scheme_idx'],
        'elapsed_sec': time.time() - t0,
        'meaning': 'SAT gives a verified E11 rank<=19 lift (and then T333 rank<=22 via +3). UNSAT records exclude only the listed quotient schemes for this prefix span; they do not prove universality without an exhaustive quotient-scheme certificate.',
        'records': records,
    }
    out = args.outdir / f'{args.name}.json'
    out.write_text(json.dumps(summary, indent=2, sort_keys=True, default=int) + '\n')
    print(json.dumps({k: summary[k] for k in ['schemes_recorded', 'status_counts', 'witness_found', 'elapsed_sec']}, indent=2, sort_keys=True))
    print(f'wrote {out}')


if __name__ == '__main__':
    main()
