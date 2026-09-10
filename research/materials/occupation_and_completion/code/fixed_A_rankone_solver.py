#!/usr/bin/env python3
"""analysis: rank-one completion inside saturated fixed-A domains over F2.

Input is the output of fixed_A_saturation.py.  For a selected fixed
A-support, this script solves the exact quadratic system

    T = sum_s a_s \otimes b_s \otimes c_s,
    b_s in B_s, c_s in C_s, b_s != 0, c_s != 0,

where B_s and C_s are the saturated-contraction domain intersections.  The
quadratic terms are encoded by Boolean products gamma_{s,i,j}=alpha_{s,i} beta_{s,j}
and GF(2) tensor equations are posted as XOR constraints.

A feasible full-tensor rank-20 or E11-core rank-19 result would be a decisive
candidate and is independently reconstructed/verified here.  Infeasible/UNKNOWN
outputs are candidate-specific execution evidence only unless later converted to
a replayable proof format.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np
from ortools.sat.python import cp_model

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from fixed_A_saturation import (  # noqa: E402
    build_matmul_tensor_f2,
    gf2_rank_rows,
    mask_to_vec,
    rref_basis,
    read_qmm_terms,
    restrict_terms_f2,
    vec_to_mask,
    verify_terms,
)


def tensor_for_kind(kind: str) -> np.ndarray:
    if kind == 'full_T333':
        return build_matmul_tensor_f2()
    paths = {
        'E11_core': 'data/restricted_cores/mask_001_E11_core.npy',
        'E12_E21_core': 'data/restricted_cores/mask_010_E12_E21_core.npy',
        'E13_E22_E31_core': 'data/restricted_cores/mask_084_E13_E22_E31_core.npy',
    }
    if kind in paths:
        return np.load(paths[kind]).astype(np.uint8) % 2
    raise ValueError(f'unknown tensor kind {kind}')


def terms_for_known_label(label: str):
    qmm = Path('data/cn122_3x3_r23_repro/scheme.qmm')
    terms = read_qmm_terms(qmm)
    if label == 'validation_full_cn122_rank23':
        return terms
    if label == 'validation_E11_core_cn122_rank21':
        return restrict_terms_f2(terms, 1)
    if label == 'validation_E12_E21_core_cn122_rank23':
        return restrict_terms_f2(terms, 10)
    if label == 'validation_E13_E22_E31_core_cn122_rank23':
        return restrict_terms_f2(terms, 84)
    return None


def add_xor_equals(model: cp_model.CpModel, lits: List[cp_model.IntVar], rhs: int, true_lit: cp_model.IntVar):
    rhs &= 1
    if not lits:
        if rhs:
            model.Add(0 == 1)
        return
    if rhs:
        model.AddBoolXOr(lits)
    else:
        model.AddBoolXOr(lits + [true_lit])


def reconstruct_terms(A_cols: Sequence[int], B_basis: Sequence[Sequence[int]], C_basis: Sequence[Sequence[int]], solver, alpha, beta) -> List[dict]:
    terms = []
    for s, a in enumerate(A_cols):
        bmask = 0
        cmask = 0
        for i, bv in enumerate(B_basis[s]):
            if solver.Value(alpha[(s, i)]):
                bmask ^= int(bv)
        for j, cv in enumerate(C_basis[s]):
            if solver.Value(beta[(s, j)]):
                cmask ^= int(cv)
        terms.append({
            'index': s,
            'u': mask_to_vec(int(a), 64),  # trimmed below by verifier wrapper
            'v': mask_to_vec(bmask, 9),
            'w': mask_to_vec(cmask, 9),
            'a_mask': int(a),
            'b_mask': int(bmask),
            'c_mask': int(cmask),
        })
    return terms


def verify_masks(T: np.ndarray, A_cols: Sequence[int], terms: Sequence[dict]) -> bool:
    na, nb, nc = T.shape
    R = np.zeros_like(T, dtype=np.uint8)
    for a, t in zip(A_cols, terms):
        bmask = int(t['b_mask'])
        cmask = int(t['c_mask'])
        aa = int(a)
        while aa:
            lba = aa & -aa
            ia = lba.bit_length() - 1
            bb = bmask
            while bb:
                lbb = bb & -bb
                ib = lbb.bit_length() - 1
                cc = cmask
                while cc:
                    lbc = cc & -cc
                    ic = lbc.bit_length() - 1
                    R[ia, ib, ic] ^= 1
                    cc ^= lbc
                bb ^= lbb
            aa ^= lba
    return bool(np.array_equal(R, T % 2))


def load_record(summary: dict, label: str) -> dict:
    matches = [r for r in summary['targets'] if r['target']['label'] == label]
    if not matches:
        labels = [r['target']['label'] for r in summary['targets']]
        raise SystemExit(f'label not found: {label}; available={labels}')
    return matches[0]




def solve_fixed_A_completion(
    T: np.ndarray,
    A_cols: Sequence[int],
    timeout_sec: float = 300.0,
    workers: int = 8,
    seed: int = 4242,
    label: str = 'direct_fixed_A',
) -> dict:
    """Solve exact rank-one B/C completion for an arbitrary fixed A multiset.

    This is the programmatic interface needed after analysis.  It computes the
    same saturated-contraction domains used by the batch labels, then solves

        T = sum_s a_s \otimes b_s \otimes c_s,  b_s in B_s, c_s in C_s,

    over F2 with CP-SAT XOR equations.  FEASIBLE is reconstructed and checked;
    INFEASIBLE/UNKNOWN is only candidate-specific evidence.
    """
    from complete_core_and_transversal import saturation_domains  # local import avoids circular load at module import time

    T = np.asarray(T, dtype=np.uint8) % 2
    na, nb, nc = T.shape
    A_cols = [int(x) for x in A_cols]
    analysis = saturation_domains(T, A_cols)
    B_basis = [[int(x) for x in b] for b in analysis['B_domains']]
    C_basis = [[int(x) for x in c] for c in analysis['C_domains']]
    zero_domain_terms = [s for s, (Bb, Cb) in enumerate(zip(B_basis, C_basis)) if len(Bb) == 0 or len(Cb) == 0]
    result = {
        'schema': 'solve_fixed_A_completion_v1',
        'label': label,
        'field': 'F2',
        'term_count': len(A_cols),
        'distinct_A_points': len(set(A_cols)),
        'A_cols': A_cols,
        'saturation_linear_passed': analysis['summary']['linear_membership']['necessary_linear_test_passed'],
        'saturation_linear_variables': analysis['summary']['linear_membership']['variables'],
        'saturation_affine_dim': analysis['summary']['linear_membership']['affine_solution_dimension_if_consistent'],
        'saturated_contraction_count': analysis['summary']['saturated_contraction_count'],
        'zero_domain_terms': zero_domain_terms,
        'term_domain_dims_hist': analysis['summary']['term_domain_dims_hist'],
        'meaning': 'FEASIBLE gives an exact fixed-A decomposition verified by reconstruction. INFEASIBLE/UNKNOWN is candidate-specific unless converted to proof.',
    }
    if zero_domain_terms:
        result.update({
            'status': 'NONZERO_TERM_IMPOSSIBLE_FROM_ZERO_DOMAIN',
            'solve_sec': 0.0,
            'verified_decomposition': False,
            'reason': 'At least one fixed A term has B_s={0} or C_s={0} under saturated-domain intersections.',
        })
        return result
    if not result['saturation_linear_passed']:
        result.update({
            'status': 'LINEAR_MEMBERSHIP_IMPOSSIBLE',
            'solve_sec': 0.0,
            'verified_decomposition': False,
            'reason': 'The tensor is not in the linear span sum_s a_s \otimes (B_s \otimes C_s) for the saturated domains.',
        })
        return result

    model = cp_model.CpModel()
    true_lit = model.NewBoolVar('const_true')
    model.Add(true_lit == 1)
    alpha = {}
    beta = {}
    gamma = {}
    for s, (Bb, Cb) in enumerate(zip(B_basis, C_basis)):
        for i in range(len(Bb)):
            alpha[(s, i)] = model.NewBoolVar(f'a_{s}_{i}')
        for j in range(len(Cb)):
            beta[(s, j)] = model.NewBoolVar(f'c_{s}_{j}')
        model.Add(sum(alpha[(s, i)] for i in range(len(Bb))) >= 1)
        model.Add(sum(beta[(s, j)] for j in range(len(Cb))) >= 1)
        for i in range(len(Bb)):
            for j in range(len(Cb)):
                g = model.NewBoolVar(f'g_{s}_{i}_{j}')
                gamma[(s, i, j)] = g
                ai = alpha[(s, i)]
                bj = beta[(s, j)]
                model.Add(g <= ai)
                model.Add(g <= bj)
                model.Add(g >= ai + bj - 1)

    eq_count = 0
    max_width = 0
    width_hist: Dict[int, int] = {}
    for a in range(na):
        terms_with_a = [s for s, acol in enumerate(A_cols) if (int(acol) >> a) & 1]
        for b in range(nb):
            for c in range(nc):
                lits = []
                for s in terms_with_a:
                    for i, bv in enumerate(B_basis[s]):
                        if ((int(bv) >> b) & 1) == 0:
                            continue
                        for j, cv in enumerate(C_basis[s]):
                            if (int(cv) >> c) & 1:
                                lits.append(gamma[(s, i, j)])
                rhs = int(T[a, b, c]) & 1
                add_xor_equals(model, lits, rhs, true_lit)
                eq_count += 1
                max_width = max(max_width, len(lits))
                width_hist[len(lits)] = width_hist.get(len(lits), 0) + 1

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = float(timeout_sec)
    solver.parameters.num_search_workers = int(workers)
    solver.parameters.random_seed = int(seed)
    t0 = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - t0
    status_name = {
        cp_model.OPTIMAL: 'OPTIMAL',
        cp_model.FEASIBLE: 'FEASIBLE',
        cp_model.INFEASIBLE: 'INFEASIBLE',
        cp_model.MODEL_INVALID: 'MODEL_INVALID',
        cp_model.UNKNOWN: 'UNKNOWN',
    }.get(status, str(status))
    result.update({
        'status': status_name,
        'solve_sec': solve_sec,
        'cp_model_stats': solver.ResponseStats(),
        'variables_alpha': len(alpha),
        'variables_beta': len(beta),
        'variables_gamma': len(gamma),
        'equations': eq_count,
        'max_equation_width': max_width,
        'equation_width_hist': {str(k): v for k, v in sorted(width_hist.items())},
    })
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        terms = reconstruct_terms(A_cols, B_basis, C_basis, solver, alpha, beta)
        verified = verify_masks(T, A_cols, terms)
        result.update({
            'verified_decomposition': verified,
            'terms': [{
                'index': t['index'],
                'a_mask': t['a_mask'],
                'b_mask': t['b_mask'],
                'c_mask': t['c_mask'],
                'b_weight': int(t['b_mask']).bit_count(),
                'c_weight': int(t['c_mask']).bit_count(),
            } for t in terms],
            'B_span_rank_found': gf2_rank_rows((t['b_mask'] for t in terms), nb),
            'C_span_rank_found': gf2_rank_rows((t['c_mask'] for t in terms), nc),
        })
    else:
        result['verified_decomposition'] = False
    return result
def solve_label(label: str, summary_path: Path, outdir: Path, time_limit: float, workers: int, actual_hint: bool) -> dict:
    summary = json.loads(summary_path.read_text())
    rec = load_record(summary, label)
    target = rec['target']
    analysis = rec['analysis']
    T = tensor_for_kind(target['tensor_kind'])
    na, nb, nc = T.shape
    A_cols = [int(x) for x in target['A_cols']]
    term_summaries = analysis['term_summaries']
    B_basis = [[int(x) for x in t['B_basis']] for t in term_summaries]
    C_basis = [[int(x) for x in t['C_basis']] for t in term_summaries]

    zero_domain_terms = [s for s, (Bb, Cb) in enumerate(zip(B_basis, C_basis)) if len(Bb) == 0 or len(Cb) == 0]
    result = {
        'schema': 'fixed_A_rankone_solver_v1',
        'label': label,
        'tensor_kind': target['tensor_kind'],
        'field': 'F2',
        'term_count': len(A_cols),
        'source': target.get('source'),
        'source_status': target.get('source_status'),
        'source_violation_count': target.get('source_violation_count'),
        'source_new_violations': target.get('source_new_violations'),
        'source_full_lut_violations': target.get('source_full_lut_violations'),
        'saturation_linear_passed': analysis['linear_membership']['necessary_linear_test_passed'],
        'saturation_linear_variables': analysis['linear_membership']['variables'],
        'saturation_affine_dim': analysis['linear_membership']['affine_solution_dimension_if_consistent'],
        'zero_domain_terms': zero_domain_terms,
        'meaning': 'FEASIBLE gives an exact fixed-A decomposition verified by reconstruction. INFEASIBLE/UNKNOWN is candidate-specific unless converted to a proof certificate.',
    }
    if zero_domain_terms:
        result.update({
            'status': 'NONZERO_TERM_IMPOSSIBLE_FROM_ZERO_DOMAIN',
            'solve_sec': 0.0,
            'verified_decomposition': False,
            'reason': 'At least one A-column term is forced by saturated contractions to have B_s={0} or C_s={0}; a nonzero rank-one term cannot use this fixed A multiset.',
        })
        return result

    model = cp_model.CpModel()
    true_lit = model.NewBoolVar('const_true')
    model.Add(true_lit == 1)
    alpha = {}
    beta = {}
    gamma = {}
    for s, (Bb, Cb) in enumerate(zip(B_basis, C_basis)):
        for i in range(len(Bb)):
            alpha[(s, i)] = model.NewBoolVar(f'a_{s}_{i}')
        for j in range(len(Cb)):
            beta[(s, j)] = model.NewBoolVar(f'c_{s}_{j}')
        model.Add(sum(alpha[(s, i)] for i in range(len(Bb))) >= 1)
        model.Add(sum(beta[(s, j)] for j in range(len(Cb))) >= 1)
        for i in range(len(Bb)):
            for j in range(len(Cb)):
                g = model.NewBoolVar(f'g_{s}_{i}_{j}')
                gamma[(s, i, j)] = g
                ai = alpha[(s, i)]
                bj = beta[(s, j)]
                model.Add(g <= ai)
                model.Add(g <= bj)
                model.Add(g >= ai + bj - 1)

    # Build tensor-coordinate XOR equations in gamma variables.
    eq_count = 0
    max_width = 0
    width_hist: Dict[int, int] = {}
    for a in range(na):
        terms_with_a = [s for s, acol in enumerate(A_cols) if (int(acol) >> a) & 1]
        for b in range(nb):
            for c in range(nc):
                lits = []
                for s in terms_with_a:
                    for i, bv in enumerate(B_basis[s]):
                        if ((int(bv) >> b) & 1) == 0:
                            continue
                        for j, cv in enumerate(C_basis[s]):
                            if (int(cv) >> c) & 1:
                                lits.append(gamma[(s, i, j)])
                rhs = int(T[a, b, c]) & 1
                add_xor_equals(model, lits, rhs, true_lit)
                eq_count += 1
                max_width = max(max_width, len(lits))
                width_hist[len(lits)] = width_hist.get(len(lits), 0) + 1

    # Optional actual hints for known decompositions; these validate search encoding without constraining it.
    hints_added = False
    if actual_hint:
        known_terms = terms_for_known_label(label)
        if known_terms is not None and len(known_terms) == len(A_cols):
            hints_added = True
            for s, t in enumerate(known_terms):
                bmask = vec_to_mask(t['v'])
                cmask = vec_to_mask(t['w'])
                # Solve coordinate in the domain basis by brute force over tiny dimensions.
                for kind, basis, varmap, mask in [('b', B_basis[s], alpha, bmask), ('c', C_basis[s], beta, cmask)]:
                    found = None
                    d = len(basis)
                    for coeff in range(1 << d):
                        v = 0
                        for i, bv in enumerate(basis):
                            if (coeff >> i) & 1:
                                v ^= int(bv)
                        if v == mask:
                            found = coeff
                            break
                    if found is not None:
                        for i in range(d):
                            model.AddHint(varmap[(s, i)], (found >> i) & 1)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_search_workers = workers
    solver.parameters.random_seed = 4242
    t0 = time.time()
    status = solver.Solve(model)
    solve_sec = time.time() - t0
    status_name = {
        cp_model.OPTIMAL: 'OPTIMAL',
        cp_model.FEASIBLE: 'FEASIBLE',
        cp_model.INFEASIBLE: 'INFEASIBLE',
        cp_model.MODEL_INVALID: 'MODEL_INVALID',
        cp_model.UNKNOWN: 'UNKNOWN',
    }.get(status, str(status))

    result.update({
        'status': status_name,
        'solve_sec': solve_sec,
        'cp_model_stats': solver.ResponseStats(),
        'variables_alpha': len(alpha),
        'variables_beta': len(beta),
        'variables_gamma': len(gamma),
        'equations': eq_count,
        'max_equation_width': max_width,
        'equation_width_hist': {str(k): v for k, v in sorted(width_hist.items())},
        'actual_hint_requested': actual_hint,
        'actual_hints_added': hints_added,
    })

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        terms = reconstruct_terms(A_cols, B_basis, C_basis, solver, alpha, beta)
        verified = verify_masks(T, A_cols, terms)
        result.update({
            'verified_decomposition': verified,
            'A_cols': A_cols,
            'terms': [{
                'index': t['index'],
                'a_mask': t['a_mask'],
                'b_mask': t['b_mask'],
                'c_mask': t['c_mask'],
                'b_weight': int(t['b_mask']).bit_count(),
                'c_weight': int(t['c_mask']).bit_count(),
            } for t in terms],
            'B_span_rank_found': gf2_rank_rows((t['b_mask'] for t in terms), nb),
            'C_span_rank_found': gf2_rank_rows((t['c_mask'] for t in terms), nc),
        })
    else:
        result['verified_decomposition'] = False

    return result


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--summary', type=Path, default=Path('data/fixed_A_saturation/summary.json'))
    ap.add_argument('--outdir', type=Path, default=Path('data/fixed_A_rankone'))
    ap.add_argument('--label', action='append', required=True)
    ap.add_argument('--time-limit', type=float, default=300.0)
    ap.add_argument('--workers', type=int, default=8)
    ap.add_argument('--actual-hint', action='store_true')
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)

    all_results = []
    for label in args.label:
        print(f"\n=== rank-one fixed-A solve: {label} ===")
        res = solve_label(label, args.summary, args.outdir, args.time_limit, args.workers, args.actual_hint)
        all_results.append(res)
        out = args.outdir / f"{label}.json"
        out.write_text(json.dumps(res, indent=2, sort_keys=True) + '\n')
        brief = {k: res.get(k) for k in ['label', 'status', 'verified_decomposition', 'solve_sec', 'variables_alpha', 'variables_beta', 'variables_gamma', 'saturation_linear_passed', 'saturation_affine_dim', 'zero_domain_terms']}
        print(json.dumps(brief, indent=2, sort_keys=True))
        print(f"Saved {out}")

    (args.outdir / 'summary.json').write_text(json.dumps({'schema': 'fixed_A_rankone_batch_v1', 'results': all_results}, indent=2, sort_keys=True) + '\n')


if __name__ == '__main__':
    main()
