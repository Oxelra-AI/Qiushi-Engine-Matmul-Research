#!/usr/bin/env python3
"""analysis: rank-one lattice of a matrix-multiplication decomposition span.

Reformulation used here (exact, and verified by explicit Brent checks):

  For A-masks a_t and B-masks b_t, the linear system K C^T = D with
  K[(alpha,beta),t] = a_t[alpha] b_t[beta] and D[(alpha,beta),gamma]
  = T[alpha,beta,gamma] IS the complete set of 729 Brent equations.
  Hence a rank-n exact decomposition over F2 exists iff there are n rank-one
  9x9 matrices s_t = a_t b_t^T whose F2-span contains the 9-dimensional space
  W = col(D).  A minimal family may be taken linearly independent, so

      R_{F2}(T) = min { dim U : W subset U, U = span of the rank-one
                        matrices that U contains }.

This script computes, for a verified rank-23 decomposition with span U,
  (1) S(U) = every nonzero rank-one 9x9 matrix contained in U,
  (2) a complete search over all subspaces U' of U with W subset U' and
      dim U' = 22 (equivalently hyperplanes of U through W) asking whether
      S(U) cap U' spans U'.

Part (2) is a complete decision for "is there a rank-22 decomposition whose
column span lies inside this particular rank-23 span".  A positive answer
yields explicit A/B, then C is solved and all Brent equations are checked.
"""
from __future__ import annotations
import argparse, json, sys, time
from collections import Counter
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
import residual_repair_geometry as rg  # type: ignore
from linear_completion import (  # type: ignore
    build_t333_f2, tensor_to_D, gf2_solve_multi, vec_to_mask,
    verify_decomposition_f2,
)

OUTDIR = Path('data/rankone_lattice')


def popcnt(x: int) -> int:
    try:
        return x.bit_count()
    except AttributeError:
        return bin(x).count('1')


# --------------------------------------------------------------------------
# tagged echelon basis with FULL pivot elimination (so reduction is linear)

def echelon_add(basis: Dict[int, Tuple[int, int]], v: int, tag: int) -> bool:
    x, tg = int(v), int(tag)
    for p in sorted(basis.keys(), reverse=True):
        if (x >> p) & 1:
            bv, bt = basis[p]
            x ^= bv
            tg ^= bt
    if x == 0:
        return False
    p = x.bit_length() - 1
    # reduce existing rows by the new pivot row to keep the basis reduced
    for q in list(basis.keys()):
        bv, bt = basis[q]
        if (bv >> p) & 1:
            basis[q] = (bv ^ x, bt ^ tg)
    basis[p] = (x, tg)
    return True


def echelon_reduce(basis: Dict[int, Tuple[int, int]], v: int) -> Tuple[int, int]:
    x, tg = int(v), 0
    for p in sorted(basis.keys(), reverse=True):
        if (x >> p) & 1:
            bv, bt = basis[p]
            x ^= bv
            tg ^= bt
    return x, tg


def rank_of_int_list(vals: Sequence[int]) -> int:
    piv: Dict[int, int] = {}
    r = 0
    for v in vals:
        x = int(v)
        while x:
            p = x.bit_length() - 1
            if p in piv:
                x ^= piv[p]
            else:
                piv[p] = x
                r += 1
                break
    return r


def independent_subset(items: Sequence[Tuple[int, object]], target: int) -> List[object]:
    """Greedily pick items (coord, payload) with independent coords."""
    piv: Dict[int, int] = {}
    out: List[object] = []
    for coord, payload in items:
        x = int(coord)
        while x:
            p = x.bit_length() - 1
            if p in piv:
                x ^= piv[p]
            else:
                piv[p] = x
                out.append(payload)
                break
        if len(out) == target:
            break
    return out


def kernel_basis(cols: Sequence[int]) -> List[int]:
    """Kernel (as subset masks) of the map F2^m -> ambient given by cols."""
    piv: Dict[int, Tuple[int, int]] = {}
    ker: List[int] = []
    for j, c in enumerate(cols):
        x, e = int(c), 1 << j
        while x:
            p = x.bit_length() - 1
            if p in piv:
                bv, be = piv[p]
                x ^= bv
                e ^= be
            else:
                piv[p] = (x, e)
                break
        if x == 0:
            ker.append(e)
    return ker


def span_masks(basis: Sequence[int]) -> List[int]:
    out = [0]
    for b in basis:
        out += [x ^ b for x in out]
    return [x for x in out if x]


# --------------------------------------------------------------------------

def elementary_reductions(basis: Dict[int, Tuple[int, int]]) -> List[List[Tuple[int, int]]]:
    """R[s][beta] = reduction of e_s (x) e_beta."""
    R = []
    for s in range(9):
        row = []
        for beta in range(9):
            v = rg.vec_mask9_to_outer81(1 << s, 1 << beta)
            row.append(echelon_reduce(basis, v))
        R.append(row)
    return R


def rank_ones_in_span(basis: Dict[int, Tuple[int, int]]) -> List[Tuple[int, int, int]]:
    """All nonzero rank-one matrices a (x) b whose reduction remainder is 0.

    Returns (a, b, coord) where coord is the tag (coordinates in the tagged
    generating set).  Uses linearity: for fixed a, the admissible b form the
    kernel of a linear map, so only 511 kernel computations are needed.
    """
    R = elementary_reductions(basis)
    out: List[Tuple[int, int, int]] = []
    for a in range(1, 512):
        supp_a = [s for s in range(9) if (a >> s) & 1]
        colrem = [0] * 9
        coltag = [0] * 9
        for beta in range(9):
            rr = 0
            tt = 0
            for s in supp_a:
                r1, t1 = R[s][beta]
                rr ^= r1
                tt ^= t1
            colrem[beta] = rr
            coltag[beta] = tt
        ker = kernel_basis(colrem)
        if not ker:
            continue
        for bmask in span_masks(ker):
            tag = 0
            for beta in range(9):
                if (bmask >> beta) & 1:
                    tag ^= coltag[beta]
            out.append((a, int(bmask), int(tag)))
    return out


def solve_and_verify(A: Sequence[int], B: Sequence[int]) -> dict:
    cols = [rg.vec_mask9_to_outer81(a, b) for a, b in zip(A, B)]
    K = rg.build_K_np_from_int_cols(cols)
    D_np = tensor_to_D(build_t333_f2())
    CT = gf2_solve_multi(K, D_np)
    if CT is None:
        return {'status': 'K_C_SOLVE_FAILED'}
    C = [vec_to_mask(CT[i]) for i in range(len(A))]
    diff = verify_decomposition_f2(list(A), list(B), C)
    return {'status': 'VERIFIED' if diff == 0 else 'BRENT_DIFF',
            'brent_diff': int(diff), 'A': list(map(int, A)),
            'B': list(map(int, B)), 'C': list(map(int, C))}


def analyze_source(name: str, terms: Sequence[Tuple[int, int, int]],
                   W_cols: Sequence[int], target_dim: int,
                   max_functionals: int) -> dict:
    n = len(terms)
    basis: Dict[int, Tuple[int, int]] = {}
    for i, (a, b, _c) in enumerate(terms):
        if not echelon_add(basis, rg.vec_mask9_to_outer81(a, b), 1 << i):
            raise RuntimeError(f'{name}: column {i} dependent; span dim < {n}')
    dimU = len(basis)
    # W coordinates inside U.
    Wcoord: List[int] = []
    for w in W_cols:
        rem, tag = echelon_reduce(basis, w)
        if rem != 0:
            raise RuntimeError(f'{name}: W not contained in the decomposition span')
        Wcoord.append(tag)
    if rank_of_int_list(Wcoord) != 9:
        raise RuntimeError(f'{name}: W coordinates have rank != 9')

    t0 = time.time()
    S = rank_ones_in_span(basis)
    t_enum = time.time() - t0
    a_hist = Counter()
    for a, _b, _t in S:
        a_hist[a] += 1
    orig_coords = {1 << i for i in range(n)}
    S_coords = {t for _a, _b, t in S}
    res = {
        'source': name,
        'n_terms': n,
        'dim_U': dimU,
        'rank_one_count_in_U': len(S),
        'rank_one_enum_sec': t_enum,
        'distinct_A_values_used': len(a_hist),
        'A_multiplicity_hist': dict(sorted(Counter(a_hist.values()).items())),
        'contains_all_original_columns': orig_coords.issubset(S_coords),
        'extra_rank_ones_beyond_original': len(S) - n,
        'W_coord_rank': rank_of_int_list(Wcoord),
        'target_dim': target_dim,
    }

    # Functionals on U (n-bit masks) vanishing on W: kernel of the 9 x n system.
    # phi . Wcoord[j] = 0 for all j.
    rows = []
    for j in range(9):
        rows.append(Wcoord[j])
    # Solve for phi: treat as linear system over F2 with unknown n bits.
    # Build echelon on the rows (each row is an n-bit mask acting by parity).
    piv: Dict[int, int] = {}
    for r in rows:
        x = int(r)
        while x:
            p = x.bit_length() - 1
            if p in piv:
                x ^= piv[p]
            else:
                piv[p] = x
                break
    pivots = sorted(piv.keys())
    free = [i for i in range(n) if i not in piv]
    # Back-substitution: for each free-variable assignment, determine pivots.
    phi_basis: List[int] = []
    for f in free:
        phi = 1 << f
        for p in sorted(pivots):
            row = piv[p]
            # parity of row & phi restricted to non-pivot p bits, then set bit p
            if popcnt(row & phi) & 1:
                phi ^= 1 << p
        phi_basis.append(phi)
    # sanity: every phi in span must annihilate all Wcoord
    for phi in phi_basis:
        for w in Wcoord:
            if popcnt(phi & w) & 1:
                raise RuntimeError('functional basis does not annihilate W')
    res['functional_space_dim'] = len(phi_basis)

    codim = dimU - target_dim
    res['codim'] = codim
    witness = None
    tested = 0
    best = 0
    t1 = time.time()
    if codim == 1:
        for phi in span_masks(phi_basis):
            tested += 1
            if tested > max_functionals:
                break
            keep = [(t, (a, b)) for a, b, t in S if not (popcnt(phi & t) & 1)]
            if len(keep) < target_dim:
                continue
            r = rank_of_int_list([t for t, _ in keep])
            if r > best:
                best = r
            if r >= target_dim:
                picks = independent_subset(keep, target_dim)
                A = [a for a, _b in picks]
                B = [b for _a, b in picks]
                vr = solve_and_verify(A, B)
                if vr['status'] == 'VERIFIED':
                    witness = {'phi': int(phi), **vr}
                    break
    res['functionals_tested'] = tested
    res['best_rank_one_rank_in_hyperplane'] = best
    res['search_sec'] = time.time() - t1
    res['witness'] = witness
    res['rank_one_list_head'] = [[a, b, t] for a, b, t in S[:80]]
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--sources', default='cn122_qmm,flip_rank23_text,pivot17_transformed_rank23')
    ap.add_argument('--target-dim', type=int, default=22)
    ap.add_argument('--max-functionals', type=int, default=1 << 22)
    ap.add_argument('--outdir', type=Path, default=OUTDIR)
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    sources = rg.load_sources()
    W_cols = rg.D_columns_as_ints()
    out = {
        'schema': 's0908_rankone_lattice_v1',
        'meaning': ('Complete enumeration of rank-one matrices inside verified rank-23 '
                    'spans, and a complete search over subspaces of those spans of the '
                    'target dimension containing W=col(D).  A witness is a full exact '
                    'decomposition verified on all 729 Brent equations; absence excludes '
                    'only decompositions whose span lies inside the given rank-23 span.'),
        'target_dim': args.target_dim,
        'results': {},
        'witnesses': [],
    }
    for name in [x.strip() for x in args.sources.split(',') if x.strip()]:
        if name not in sources:
            print(f'missing source {name}', flush=True)
            continue
        r = analyze_source(name, sources[name], W_cols, args.target_dim, args.max_functionals)
        out['results'][name] = r
        if r['witness'] is not None:
            wp = args.outdir / f'rank{args.target_dim}_witness_{name}.json'
            wp.write_text(json.dumps(r['witness'], indent=2, sort_keys=True) + '\n')
            out['witnesses'].append(str(wp))
        print(json.dumps({k: v for k, v in r.items()
                          if k not in ('rank_one_list_head', 'witness')},
                         indent=2, sort_keys=True), flush=True)
        if r['witness'] is not None:
            print('WITNESS FOUND', wp, flush=True)
    out['elapsed_sec'] = time.time() - t0
    op = args.outdir / f'rankone_lattice_dim{args.target_dim}.json'
    op.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'ok', 'out': str(op), 'witnesses': out['witnesses'],
                      'elapsed_sec': out['elapsed_sec']}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
