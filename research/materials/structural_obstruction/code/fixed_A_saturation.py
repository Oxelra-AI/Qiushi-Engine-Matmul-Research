#!/usr/bin/env python3
"""analysis: fixed-A saturated-contraction compatibility over F2.

For a fixed list of A-side projective columns a_s, any decomposition

    T = sum_s a_s \otimes b_s \otimes c_s

has a strong necessary condition beyond A-occupation.  For each linear
functional q on the A-space, the B-by-C contraction is

    L(q) = sum_{i:q(e_i)=1} T_i = sum_{s:q(a_s)=1} b_s c_s^T.

If |I_q| = rank L(q), then this is a rank-minimal matrix decomposition,
so every participating b_s lies in col L(q), and every c_s lies in row L(q).
Intersecting these spaces over all saturated contractions containing s gives
term domains B_s and C_s.  Then a cheap linear necessary test is

    T in sum_s a_s \otimes (B_s \otimes C_s),

before imposing rank-one conditions on each X_s in B_s \otimes C_s.

This script validates the inference on known cn122 full/core decompositions and
then applies it to current full-tensor rep2 supports and E11-core rank-19
A-support candidates from earlier lazy capacity runs.
"""
from __future__ import annotations

import argparse
import json
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np

# ---------------------------------------------------------------------------
# Basic GF(2) linear algebra on bit-vector encoded row vectors
# ---------------------------------------------------------------------------


def vec_to_mask(v: Sequence[int]) -> int:
    out = 0
    for i, x in enumerate(v):
        if int(x) & 1:
            out |= 1 << i
    return out


def mask_to_vec(x: int, n: int) -> List[int]:
    return [(x >> i) & 1 for i in range(n)]


def rref_basis(rows: Iterable[int], n: int) -> Tuple[int, ...]:
    basis = [0] * n
    mask = (1 << n) - 1
    for row in rows:
        v = row & mask
        while v:
            p = v.bit_length() - 1
            if basis[p]:
                v ^= basis[p]
            else:
                basis[p] = v
                break
    for p in range(n):
        if basis[p]:
            for q in range(n):
                if q != p and basis[q] and ((basis[q] >> p) & 1):
                    basis[q] ^= basis[p]
    return tuple(basis[p] for p in range(n - 1, -1, -1) if basis[p])


def in_span(v: int, basis: Sequence[int], n: int) -> bool:
    x = v & ((1 << n) - 1)
    piv = {b.bit_length() - 1: b for b in basis if b}
    while x:
        p = x.bit_length() - 1
        b = piv.get(p)
        if b is None:
            return False
        x ^= b
    return True


def span_vectors(basis: Sequence[int]) -> set[int]:
    vals = [0]
    for b in basis:
        vals += [x ^ b for x in vals]
    return set(vals)


def full_basis(n: int) -> Tuple[int, ...]:
    return rref_basis((1 << i for i in range(n)), n)


def intersection_basis(spaces: Sequence[Sequence[int]], n: int) -> Tuple[int, ...]:
    if not spaces:
        return full_basis(n)
    current: Optional[set[int]] = None
    for basis in spaces:
        vals = span_vectors(basis)
        current = vals if current is None else (current & vals)
        if current == {0}:
            return tuple()
    assert current is not None
    return rref_basis(current, n)


def gf2_rank_rows(rows: Iterable[int], ncols: int) -> int:
    basis: Dict[int, int] = {}
    mask = (1 << ncols) - 1
    for row in rows:
        x = row & mask
        while x:
            p = x.bit_length() - 1
            b = basis.get(p)
            if b is None:
                basis[p] = x
                break
            x ^= b
    return len(basis)


def gf2_linear_consistency(rows_aug: List[int], nvars: int) -> Tuple[bool, int, Optional[int]]:
    """Return (consistent, coefficient_rank, contradiction_combination).

    Coefficient bits are 0..nvars-1; RHS is bit nvars.  If inconsistent,
    contradiction_combination is a bitset of original equation rows whose XOR
    has all-zero coefficients and RHS one.  This is a compact dual certificate
    for failure of the necessary linear membership test.
    """
    coeff_mask = (1 << nvars) - 1
    basis: Dict[int, int] = {}
    basis_comb: Dict[int, int] = {}
    for i, row in enumerate(rows_aug):
        x = row
        comb = 1 << i
        while True:
            coeff = x & coeff_mask
            if coeff == 0:
                if (x >> nvars) & 1:
                    return False, len(basis), comb
                break
            p = coeff.bit_length() - 1
            b = basis.get(p)
            if b is None:
                basis[p] = x
                basis_comb[p] = comb
                break
            x ^= b
            comb ^= basis_comb[p]
    return True, len(basis), None


def mat_rank_f2(M: np.ndarray) -> int:
    rows = []
    m, n = M.shape
    for i in range(m):
        x = 0
        for j in range(n):
            if int(M[i, j]) & 1:
                x |= 1 << j
        rows.append(x)
    return gf2_rank_rows(rows, n)


def col_space_basis(M: np.ndarray) -> Tuple[int, ...]:
    nr, nc = M.shape
    cols = []
    for j in range(nc):
        x = 0
        for i in range(nr):
            if int(M[i, j]) & 1:
                x |= 1 << i
        cols.append(x)
    return rref_basis(cols, nr)


def row_space_basis(M: np.ndarray) -> Tuple[int, ...]:
    nr, nc = M.shape
    rows = []
    for i in range(nr):
        x = 0
        for j in range(nc):
            if int(M[i, j]) & 1:
                x |= 1 << j
        rows.append(x)
    return rref_basis(rows, nc)

# ---------------------------------------------------------------------------
# Tensor/scheme utilities
# ---------------------------------------------------------------------------


def build_matmul_tensor_f2(n0: int = 3, n1: int = 3, n2: int = 3) -> np.ndarray:
    na, nb, nc = n0 * n1, n1 * n2, n0 * n2
    T = np.zeros((na, nb, nc), dtype=np.uint8)
    for i in range(n0):
        for j in range(n1):
            for k in range(n2):
                a = n1 * i + j
                b = n2 * j + k
                c = n2 * i + k
                T[a, b, c] = 1
    return T


def read_qmm_terms(path: Path) -> List[dict]:
    terms: List[dict] = []
    cur: Dict[str, object] = {}
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        if line.startswith('term '):
            if {'u', 'v', 'w'} <= set(cur):
                terms.append(cur)
            cur = {'index': int(line.split()[1])}
        elif line.startswith('u '):
            cur['u'] = [int(x) & 1 for x in line.split()[1:]]
        elif line.startswith('v '):
            cur['v'] = [int(x) & 1 for x in line.split()[1:]]
        elif line.startswith('w '):
            cur['w'] = [int(x) & 1 for x in line.split()[1:]]
    if {'u', 'v', 'w'} <= set(cur):
        terms.append(cur)
    return terms


def restrict_terms_f2(terms: Sequence[dict], mask: int) -> List[dict]:
    pivot = mask.bit_length() - 1
    free_bits = mask ^ (1 << pivot)
    out = []
    for t in terms:
        u = [int(x) & 1 for x in t['u']]
        for i in range(len(u)):
            if (free_bits >> i) & 1:
                u[i] ^= u[pivot]
        u[pivot] = 0
        u_core = [u[i] for i in range(len(u)) if i != pivot]
        if any(u_core):
            out.append({
                'index': int(t['index']),
                'u': u_core,
                'v': [int(x) & 1 for x in t['v']],
                'w': [int(x) & 1 for x in t['w']],
            })
    return out


def verify_terms(T: np.ndarray, terms: Sequence[dict]) -> bool:
    na, nb, nc = T.shape
    R = np.zeros_like(T, dtype=np.uint8)
    for t in terms:
        u = np.array(t['u'], dtype=np.uint8).reshape(na, 1, 1)
        v = np.array(t['v'], dtype=np.uint8).reshape(1, nb, 1)
        w = np.array(t['w'], dtype=np.uint8).reshape(1, 1, nc)
        R ^= (u * v * w).astype(np.uint8)
    return bool(np.array_equal(R % 2, T % 2))


def support_from_solution(sol: Dict[str, int]) -> List[int]:
    cols: List[int] = []
    for k, v in sorted(((int(k), int(v)) for k, v in sol.items())):
        cols.extend([k] * v)
    return cols

# ---------------------------------------------------------------------------
# Saturated contraction domains and linear membership
# ---------------------------------------------------------------------------


def contraction_matrix(T: np.ndarray, q: int) -> np.ndarray:
    na, nb, nc = T.shape
    M = np.zeros((nb, nc), dtype=np.uint8)
    for a in range(na):
        if (q >> a) & 1:
            M ^= T[a]
    return M


def analyze_fixed_A(
    label: str,
    T: np.ndarray,
    A_cols: Sequence[int],
    actual_terms: Optional[Sequence[dict]] = None,
    max_sat_examples: int = 12,
) -> dict:
    t0 = time.time()
    na, nb, nc = T.shape
    nterms = len(A_cols)
    sat_B: List[List[Tuple[int, ...]]] = [[] for _ in range(nterms)]
    sat_C: List[List[Tuple[int, ...]]] = [[] for _ in range(nterms)]
    sat_count_by_term = [0] * nterms
    saturated = []
    undersaturated = []
    q_rank_hist = Counter()
    q_count_hist = Counter()
    count_minus_rank_hist = Counter()
    sat_by_rank_count = Counter()

    for q in range(1, 1 << na):
        I = [s for s, a in enumerate(A_cols) if ((q & a).bit_count() & 1)]
        cnt = len(I)
        M = contraction_matrix(T, q)
        rk = mat_rank_f2(M)
        q_rank_hist[rk] += 1
        q_count_hist[cnt] += 1
        count_minus_rank_hist[cnt - rk] += 1
        if cnt < rk and len(undersaturated) < max_sat_examples:
            undersaturated.append({
                'q': q,
                'q_hex': hex(q),
                'rank': rk,
                'count': cnt,
                'defect': rk - cnt,
                'terms': I[:],
            })
        if cnt == rk and cnt > 0:
            Bb = col_space_basis(M)
            Cb = row_space_basis(M)
            sat_by_rank_count[(rk, cnt)] += 1
            if len(saturated) < max_sat_examples:
                saturated.append({
                    'q': q,
                    'q_hex': hex(q),
                    'rank': rk,
                    'count': cnt,
                    'terms': I[:],
                    'B_dim': len(Bb),
                    'C_dim': len(Cb),
                    'B_basis': list(Bb),
                    'C_basis': list(Cb),
                })
            for s in I:
                sat_B[s].append(Bb)
                sat_C[s].append(Cb)
                sat_count_by_term[s] += 1

    B_domains: List[Tuple[int, ...]] = []
    C_domains: List[Tuple[int, ...]] = []
    for s in range(nterms):
        B_domains.append(intersection_basis(sat_B[s], nb))
        C_domains.append(intersection_basis(sat_C[s], nc))

    term_summaries = []
    for s, a in enumerate(A_cols):
        term_summaries.append({
            'term': s,
            'a': int(a),
            'a_hex': hex(int(a)),
            'a_weight': int(a).bit_count(),
            'saturated_contractions': sat_count_by_term[s],
            'B_dim': len(B_domains[s]),
            'C_dim': len(C_domains[s]),
            'linear_X_dim': len(B_domains[s]) * len(C_domains[s]),
            'B_basis': list(B_domains[s]),
            'C_basis': list(C_domains[s]),
        })

    # Validate actual b/c membership if terms are supplied.
    actual_membership = None
    if actual_terms is not None:
        assert len(actual_terms) == nterms, (len(actual_terms), nterms)
        bad = []
        for s, t in enumerate(actual_terms):
            b = vec_to_mask(t['v'])
            c = vec_to_mask(t['w'])
            b_ok = in_span(b, B_domains[s], nb)
            c_ok = in_span(c, C_domains[s], nc)
            if not (b_ok and c_ok):
                bad.append({
                    'term': s,
                    'original_index': t.get('index'),
                    'a': int(A_cols[s]),
                    'b': b,
                    'c': c,
                    'B_dim': len(B_domains[s]),
                    'C_dim': len(C_domains[s]),
                    'b_ok': b_ok,
                    'c_ok': c_ok,
                })
        actual_membership = {
            'checked_terms': nterms,
            'all_b_c_in_domains': len(bad) == 0,
            'bad_terms': bad[:20],
        }

    lin = linear_membership_test(T, A_cols, B_domains, C_domains)
    return {
        'label': label,
        'A_dim': na,
        'B_dim': nb,
        'C_dim': nc,
        'term_count': nterms,
        'distinct_A_cols': len(set(A_cols)),
        'A_multiplicity_hist': dict(Counter(Counter(A_cols).values())),
        'q_rank_hist': {str(k): v for k, v in sorted(q_rank_hist.items())},
        'q_selected_count_hist': {str(k): v for k, v in sorted(q_count_hist.items())},
        'undersaturated_contraction_count': sum(v for d, v in count_minus_rank_hist.items() if d < 0),
        'count_minus_rank_hist': {str(k): v for k, v in sorted(count_minus_rank_hist.items())},
        'undersaturated_examples': undersaturated,
        'saturated_contraction_count': sum(sat_by_rank_count.values()),
        'saturated_by_rank_count': {f'rank{k[0]}_count{k[1]}': v for k, v in sorted(sat_by_rank_count.items())},
        'saturated_examples': saturated,
        'inactive_terms_no_saturation': sum(1 for x in sat_count_by_term if x == 0),
        'term_domain_dims_hist': {f'B{bc[0]}_C{bc[1]}': cnt for bc, cnt in sorted(Counter((t['B_dim'], t['C_dim']) for t in term_summaries).items())},
        'term_summaries': term_summaries,
        'actual_membership': actual_membership,
        'linear_membership': lin,
        'elapsed_sec': time.time() - t0,
    }


def linear_membership_test(
    T: np.ndarray,
    A_cols: Sequence[int],
    B_domains: Sequence[Sequence[int]],
    C_domains: Sequence[Sequence[int]],
) -> dict:
    na, nb, nc = T.shape
    neq = na * nb * nc
    var_records = []
    nvars = 0
    for s, (Bb, Cb) in enumerate(zip(B_domains, C_domains)):
        for bvec in Bb:
            for cvec in Cb:
                var_records.append((s, bvec, cvec))
                nvars += 1

    rows = [0] * neq
    # RHS bit.
    for a in range(na):
        for b in range(nb):
            for c in range(nc):
                if int(T[a, b, c]) & 1:
                    rows[(a * nb + b) * nc + c] |= 1 << nvars

    for vid, (s, bvec, cvec) in enumerate(var_records):
        acol = A_cols[s]
        aa = acol
        while aa:
            lb_a = aa & -aa
            a = lb_a.bit_length() - 1
            bb = bvec
            while bb:
                lb_b = bb & -bb
                b = lb_b.bit_length() - 1
                cc = cvec
                while cc:
                    lb_c = cc & -cc
                    c = lb_c.bit_length() - 1
                    rows[(a * nb + b) * nc + c] ^= 1 << vid
                    cc ^= lb_c
                bb ^= lb_b
            aa ^= lb_a

    consistent, coeff_rank, contradiction = gf2_linear_consistency(rows, nvars)
    rhs_weight = int(T.sum())
    cert = None
    if contradiction is not None:
        eq_indices = [i for i in range(neq) if (contradiction >> i) & 1]
        coord_examples = []
        for idx in eq_indices[:80]:
            a = idx // (nb * nc)
            rem = idx % (nb * nc)
            b = rem // nc
            c = rem % nc
            coord_examples.append([a, b, c, int(T[a, b, c])])
        # Reconstruct the XOR row to guard against certificate bookkeeping bugs.
        xor_row = 0
        for idx in eq_indices:
            xor_row ^= rows[idx]
        cert = {
            'equation_count': len(eq_indices),
            'equation_indices_head': eq_indices[:200],
            'coordinate_examples_head': coord_examples,
            'xor_coefficients_zero': (xor_row & ((1 << nvars) - 1)) == 0,
            'xor_rhs': (xor_row >> nvars) & 1,
        }
    return {
        'necessary_linear_test_passed': consistent,
        'variables': nvars,
        'equations': neq,
        'coefficient_rank': coeff_rank,
        'rhs_weight': rhs_weight,
        'affine_solution_dimension_if_consistent': (nvars - coeff_rank) if consistent else None,
        'domain_dim_sum': nvars,
        'linear_inconsistency_certificate': cert,
    }

# ---------------------------------------------------------------------------
# Input collection
# ---------------------------------------------------------------------------


def load_targets(max_rep2_rounds: int = 5) -> List[dict]:
    root = Path('research/research_record')
    qmm = root / 'workspace/data/cn122_3x3_r23_repro/scheme.qmm'
    terms = read_qmm_terms(qmm)
    T_full = build_matmul_tensor_f2()
    targets: List[dict] = []

    targets.append({
        'label': 'validation_full_cn122_rank23',
        'tensor_kind': 'full_T333',
        'T': T_full,
        'A_cols': [vec_to_mask(t['u']) for t in terms],
        'actual_terms': terms,
        'known_decomposition_verified': verify_terms(T_full, terms),
        'meaning': 'Known exact rank-23 full decomposition reduced mod 2; saturation domains must contain its B/C factors and linear test must pass.',
    })

    core_specs = {
        'E11_core': {
            'mask': 1,
            'path': root / 'workspace/data/restricted_cores/mask_001_E11_core.npy',
            'validation_label': 'validation_E11_core_cn122_rank21',
            'lazy_path': root / 'workspace/data/core_capacity/core_capacity_E11_s19.json',
            'lazy_iterations': (6, 7),
        },
        'E12_E21_core': {
            'mask': 10,
            'path': root / 'workspace/data/restricted_cores/mask_010_E12_E21_core.npy',
            'validation_label': 'validation_E12_E21_core_cn122_rank23',
            'lazy_path': root / 'workspace/data/core_capacity/core_capacity_E12_E21_s19.json',
            'lazy_iterations': (6, 7),
        },
        'E13_E22_E31_core': {
            'mask': 84,
            'path': root / 'workspace/data/restricted_cores/mask_084_E13_E22_E31_core.npy',
            'validation_label': 'validation_E13_E22_E31_core_cn122_rank23',
            'lazy_path': root / 'workspace/data/core_capacity/core_capacity_E13_E22_E31_s19.json',
            'lazy_iterations': (5, 6),
        },
    }
    core_tensors = {}
    for kind, spec in core_specs.items():
        T_core = np.load(spec['path']).astype(np.uint8) % 2
        core_tensors[kind] = T_core
        core_terms = restrict_terms_f2(terms, int(spec['mask']))
        targets.append({
            'label': spec['validation_label'],
            'tensor_kind': kind,
            'T': T_core,
            'A_cols': [vec_to_mask(t['u']) for t in core_terms],
            'actual_terms': core_terms,
            'known_decomposition_verified': verify_terms(T_core, core_terms),
            'meaning': 'Known exact core decomposition from cn122 restriction; validates quotient/core saturation semantics for this hyperplane representative.',
        })

    # Current full-tensor rep2 supports from analysis rank-aware CP-SAT rounds.
    analysis = root / 'workspace/data/rep2_rankaware/result.json'
    if analysis.exists():
        obj = json.loads(analysis.read_text())
        prefix = [int(x) for x in obj.get('prefix', [1, 2])]
        for entry in obj.get('round_log', [])[:max_rep2_rounds]:
            if 'selected_points' not in entry:
                continue
            support = prefix + [int(x) for x in entry['selected_points']]
            targets.append({
                'label': f"rep2_rankaware_round{entry.get('round')}",
                'tensor_kind': 'full_T333',
                'T': T_full,
                'A_cols': support,
                'actual_terms': None,
                'source': str(analysis),
                'source_status': entry.get('status'),
                'source_new_violations': entry.get('new_violations'),
                'meaning': 'Full-tensor adjacent-pair A-support returned by an A-only CP-SAT relaxation; fixed-A compatibility can rule it out before rank-one solving.',
            })

    # analysis orbit-promotion SAT support.
    analysis = root / 'workspace/data/corrected_strategy/rep2_orbit_promotion_all5/result.json'
    if analysis.exists():
        obj = json.loads(analysis.read_text())
        if obj.get('status') in ('OPTIMAL', 'FEASIBLE') and obj.get('support'):
            targets.append({
                'label': 'rep2_orbit_promotion_all5_support',
                'tensor_kind': 'full_T333',
                'T': T_full,
                'A_cols': [int(x) for x in obj['support']],
                'actual_terms': None,
                'source': str(analysis),
                'source_full_lut_violations': obj.get('full_lut_scan', {}).get('violation_count'),
                'meaning': 'A-support satisfying the all-five recurrent row-orbit promoted relaxation but still violating full Wang rows; tests whether B/C compatibility is already stronger.',
            })

    # analysis contraction-lower rep2 supports, if any have been produced.
    for path in sorted((root / 'workspace/data/rep2_contraction_lower').glob('*/result.json')):
        obj = json.loads(path.read_text())
        if obj.get('status') in ('OPTIMAL', 'FEASIBLE') and obj.get('support'):
            name = path.parent.name
            targets.append({
                'label': f'rep2_contraction_lower_{name}_support',
                'tensor_kind': 'full_T333',
                'T': T_full,
                'A_cols': [int(x) for x in obj['support']],
                'actual_terms': None,
                'source': str(path),
                'source_full_lut_violations': obj.get('full_lut_scan', {}).get('violation_count'),
                'source_saturation_linear': obj.get('saturation_brief', {}).get('linear_membership', {}).get('necessary_linear_test_passed'),
                'meaning': 'A-support satisfying rep2 Wang base constraints plus contraction-rank lower bounds; test full saturated-domain compatibility and rank-one completion.',
            })

    for kind, spec in core_specs.items():
        core_lazy = spec['lazy_path']
        if core_lazy.exists():
            obj = json.loads(core_lazy.read_text())
            for entry in obj.get('iterations', []):
                if 'solution' not in entry:
                    continue
                it = int(entry['iteration'])
                if it not in spec['lazy_iterations']:
                    continue
                support = support_from_solution(entry['solution'])
                targets.append({
                    'label': f'{kind}_lazy_capacity_iter{it}_s19',
                    'tensor_kind': kind,
                    'T': core_tensors[kind],
                    'A_cols': support,
                    'actual_terms': None,
                    'source': str(core_lazy),
                    'source_violation_count': entry.get('check_stats', {}).get('violation_count'),
                    'meaning': 'Rank-19 core A-multiset from lazy Wang occupation search; compatibility tests whether it can be rejected before any rank-one core solve.',
                })
    return targets


def strip_tensor(target: dict) -> dict:
    return {k: v for k, v in target.items() if k not in ('T', 'actual_terms')}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--outdir', type=Path, default=Path('data/fixed_A_saturation'))
    ap.add_argument('--max-rep2-rounds', type=int, default=5)
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)

    targets = load_targets(max_rep2_rounds=args.max_rep2_rounds)
    results = []
    for target in targets:
        print(f"\n=== {target['label']} ({target['tensor_kind']}, terms={len(target['A_cols'])}) ===")
        if 'known_decomposition_verified' in target:
            print(f"known_decomposition_verified={target['known_decomposition_verified']}")
        res = analyze_fixed_A(target['label'], target['T'], target['A_cols'], target.get('actual_terms'))
        meta = strip_tensor(target)
        rec = {'target': meta, 'analysis': res}
        results.append(rec)
        lin = res['linear_membership']
        print(json.dumps({
            'label': target['label'],
            'undersaturated': res['undersaturated_contraction_count'],
            'saturated': res['saturated_contraction_count'],
            'inactive_terms': res['inactive_terms_no_saturation'],
            'domain_hist': res['term_domain_dims_hist'],
            'linear_passed': lin['necessary_linear_test_passed'],
            'linear_vars': lin['variables'],
            'linear_rank': lin['coefficient_rank'],
            'affine_dim': lin['affine_solution_dimension_if_consistent'],
            'actual_ok': None if res['actual_membership'] is None else res['actual_membership']['all_b_c_in_domains'],
        }, sort_keys=True))

    summary = {
        'schema': 'fixed_A_saturation_v1',
        'field': 'F2',
        'principle': 'For fixed A columns, saturated contractions |I_q|=rank L(q) force b_s into col L(q) and c_s into row L(q); the target must lie in the linear space sum_s a_s tensor (B_s tensor C_s).',
        'targets': results,
        'brief': [
            {
                'label': r['target']['label'],
                'tensor_kind': r['target']['tensor_kind'],
                'term_count': r['analysis']['term_count'],
                'undersaturated_contraction_count': r['analysis']['undersaturated_contraction_count'],
                'count_minus_rank_hist': r['analysis']['count_minus_rank_hist'],
                'undersaturated_examples': r['analysis']['undersaturated_examples'],
                'saturated_contraction_count': r['analysis']['saturated_contraction_count'],
                'inactive_terms_no_saturation': r['analysis']['inactive_terms_no_saturation'],
                'term_domain_dims_hist': r['analysis']['term_domain_dims_hist'],
                'linear_membership': r['analysis']['linear_membership'],
                'actual_membership': r['analysis']['actual_membership'],
                'source': r['target'].get('source'),
                'source_violation_count': r['target'].get('source_violation_count'),
                'source_new_violations': r['target'].get('source_new_violations'),
                'source_full_lut_violations': r['target'].get('source_full_lut_violations'),
            }
            for r in results
        ],
    }
    out = args.outdir / 'summary.json'
    out.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(f"\nSaved {out}")


if __name__ == '__main__':
    main()
