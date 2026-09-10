#!/usr/bin/env python3
"""analysis: residual-space exact tests for local A/B repairs near rank-23 schemes.

For a rank-23 scheme, delete one term to get 22 slots.  Retain most old
columns k_t=a_t\otimes b_t and allow a chosen repair block J to choose new
B-factors for fixed A-factors a'_t.  Let L be the span of the retained old
columns and let E be the image of col(D) in V/L, where D is the (A,B)|C
flattening of T_333.  For slot t, U_t is the image of a'_t\otimes F_2^9 in
V/L, restricted to E by H_t=U_t\cap E.

If dim(E)=d>k=|J|, the repair block cannot complete C.  If d=k, completion is
equivalent to choosing one vector from each H_t so that the chosen k vectors
form a basis of E (a subspace independent-transversal condition).  This script
checks that condition exactly and, when it succeeds, lifts representatives back
to B and verifies the full Brent identities.

The point is not to prove rank 23 optimal; it is to replace brute-force
512^k B searches in the minimal-defect case by exact small linear algebra and
to understand which A-swaps preserve or destroy the residual coverage.
"""
from __future__ import annotations
import argparse, itertools, json, os, re, sys, time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
from linear_completion import (  # type: ignore
    parse_qmm_scheme_f2, verify_decomposition_f2, gf2_solve_multi,
    build_t333_f2, tensor_to_D, vec_to_mask,
)

CN122 = Path('data/cn122_3x3_r23_repro/scheme.qmm')
FLIP_TXT = Path('data/flip_cpd_inspect/src/khoruzhii-flip-cpd-9eeb17f/data/schemes_paper/gg-333-rank23-rec-0-0-0-z.txt')
PIVOT17_JSON = Path('data/pivot_fixed/pivot17_rank23_transformed_control.json')
PIPELINE_SUMMARY = Path('data/pipeline_results/pipeline_summary.json')
OUTDIR = Path('data/residual_repair')

# ---------------------------------------------------------------------------
# GF(2) bit-vector linear algebra on 81-bit ambient vectors, plus small d-bit
# coordinate vectors inside E.


def vec_mask9_to_outer81(a: int, b: int) -> int:
    """Return 81-bit integer for a\otimes b with row index s*9+beta."""
    out = 0
    aa = int(a); bb = int(b)
    s = 0
    while aa:
        if aa & 1:
            # place b in block s
            out ^= bb << (9 * s)
        aa >>= 1
        s += 1
    return out


def D_columns_as_ints() -> List[int]:
    T = build_t333_f2(); D = tensor_to_D(T)
    cols = []
    for c in range(9):
        v = 0
        for i in range(81):
            if D[i, c] & 1:
                v |= 1 << i
        cols.append(v)
    return cols


def add_to_basis(basis: Dict[int, Tuple[int, int]], v: int, tag: int = 0) -> bool:
    """Add vector v with auxiliary tag to a high-pivot echelon basis.

    basis maps pivot bit -> (vector, tag).  Existing vectors carry tags such
    that every reduction preserves the tag of the represented combination.
    Returns True iff v was independent.
    """
    x = int(v); tg = int(tag)
    while x:
        p = x.bit_length() - 1
        if p in basis:
            bv, bt = basis[p]
            x ^= bv
            tg ^= bt
        else:
            basis[p] = (x, tg)
            return True
    return False


def reduce_by_basis(basis: Dict[int, Tuple[int, int]], v: int) -> Tuple[int, int]:
    """Reduce v by basis.  Return (remainder, accumulated tag)."""
    x = int(v); tg = 0
    while x:
        p = x.bit_length() - 1
        if p not in basis:
            break
        bv, bt = basis[p]
        x ^= bv
        tg ^= bt
    return x, tg


def rank_ints(vecs: Iterable[int]) -> int:
    basis: Dict[int, Tuple[int, int]] = {}
    r = 0
    for v in vecs:
        if int(v) and add_to_basis(basis, int(v), 0):
            r += 1
    return r


def independent_rank_small(vecs: Iterable[int]) -> int:
    return rank_ints(vecs)


def build_quotient_basis(retained_cols: Sequence[int], D_cols: Sequence[int]) -> Tuple[Dict[int, Tuple[int, int]], List[int], int, int]:
    """Build a tagged basis for L + E, where E is D modulo L.

    Retained columns enter with tag 0.  D columns that extend L get tags
    1,2,4,... and form representatives of an E basis.
    """
    # First find independent D representatives modulo L, preserving actual reps.
    plain_basis: Dict[int, Tuple[int, int]] = {}
    rank_L = 0
    for c in retained_cols:
        if c and add_to_basis(plain_basis, c, 0):
            rank_L += 1
    E_reps: List[int] = []
    for dcol in D_cols:
        rem, _ = reduce_by_basis(plain_basis, dcol)
        if rem:
            # This D column adds a new quotient direction.
            E_reps.append(dcol)
            add_to_basis(plain_basis, dcol, 0)
    d = len(E_reps)

    tagged: Dict[int, Tuple[int, int]] = {}
    for c in retained_cols:
        if c:
            add_to_basis(tagged, c, 0)
    for i, e in enumerate(E_reps):
        ok = add_to_basis(tagged, e, 1 << i)
        if not ok:
            raise RuntimeError('E representative unexpectedly dependent modulo retained columns')
    return tagged, E_reps, rank_L, d


def tags_rank(tags: Iterable[int]) -> int:
    return rank_ints([int(t) for t in tags if int(t)])


def span_tags(basis_tags: Sequence[int], d: int) -> List[int]:
    """Enumerate all tags in the span of a small basis, including 0."""
    basis = []
    for t in basis_tags:
        if t and tags_rank(basis + [t]) > len(basis):
            basis.append(t)
    out = []
    for mask in range(1 << len(basis)):
        x = 0
        for i, b in enumerate(basis):
            if (mask >> i) & 1:
                x ^= b
        out.append(x)
    return sorted(set(out))


def hall_condition(H_bases: Sequence[Sequence[int]], d: int) -> Tuple[bool, Optional[dict]]:
    """Check dim(sum_{t in J} H_t) >= |J| for every nonempty J."""
    k = len(H_bases)
    for r in range(1, k + 1):
        for J in itertools.combinations(range(k), r):
            vecs: List[int] = []
            for j in J:
                vecs.extend(H_bases[j])
            rr = tags_rank(vecs)
            if rr < r:
                return False, {'subset': list(J), 'rank': rr, 'size': r}
    # Also require total span E when d=k.  Hall implies this for J=all, but keep explicit.
    total = tags_rank([v for H in H_bases for v in H])
    if total < d:
        return False, {'subset': list(range(k)), 'rank': total, 'size': d, 'reason': 'total_span_lt_E'}
    return True, None


def choose_independent_representatives(tag_to_b: Sequence[Dict[int, int]], d: int) -> Optional[List[Tuple[int, int]]]:
    """Choose nonzero tag, b for each slot so chosen tags have rank d."""
    k = len(tag_to_b)
    candidates = []
    for mp in tag_to_b:
        tags = sorted(t for t in mp if t)
        if not tags:
            return None
        candidates.append(tags)
    order = sorted(range(k), key=lambda i: len(candidates[i]))
    chosen: List[Optional[Tuple[int, int]]] = [None] * k

    def rec(pos: int, basis_tags: List[int]) -> bool:
        if pos == len(order):
            return tags_rank([t for t, _b in chosen if t is not None]) == d
        i = order[pos]
        for tg in candidates[i]:
            new_rank = tags_rank(basis_tags + [tg])
            if new_rank == tags_rank(basis_tags):
                continue
            chosen[i] = (tg, tag_to_b[i][tg])
            if rec(pos + 1, basis_tags + [tg]):
                return True
            chosen[i] = None
        return False

    if rec(0, []):
        return [x for x in chosen if x is not None]
    return None


def build_K_np_from_int_cols(cols: Sequence[int]) -> np.ndarray:
    K = np.zeros((81, len(cols)), dtype=np.uint8)
    for j, col in enumerate(cols):
        x = int(col)
        i = 0
        while x:
            if x & 1:
                K[i, j] = 1
            x >>= 1; i += 1
    return K

# ---------------------------------------------------------------------------
# Source loading.


def parse_linear_form(expr: str, prefix: str) -> int:
    mask = 0
    for m in re.finditer(rf"{prefix}(\d+)", expr):
        idx = int(m.group(1)) - 1
        mask ^= 1 << idx
    return mask


def parse_rank23_text(path: Path) -> List[Tuple[int, int, int]]:
    text = path.read_text()
    prod_re = re.compile(r"m(\d+)\s*=\s*\((.*?)\)\((.*?)\)")
    prods = {}
    for m in prod_re.finditer(text):
        t = int(m.group(1))
        prods[t] = {'u': parse_linear_form(m.group(2), 'a'), 'v': parse_linear_form(m.group(3), 'b')}
    c_re = re.compile(r"c(\d+)\s*=\s*(.*)")
    w_masks = {t: 0 for t in prods}
    for m in c_re.finditer(text):
        cidx = int(m.group(1)) - 1
        rhs = m.group(2)
        for mt in re.finditer(r"m(\d+)", rhs):
            t = int(mt.group(1))
            if t in w_masks:
                w_masks[t] ^= 1 << cidx
    return [(prods[t]['u'], prods[t]['v'], w_masks[t]) for t in sorted(prods)]


def load_sources() -> Dict[str, List[Tuple[int, int, int]]]:
    sources: Dict[str, List[Tuple[int, int, int]]] = {}
    if CN122.exists():
        A, B, C = parse_qmm_scheme_f2(CN122)
        sources['cn122_qmm'] = list(zip(A, B, C))
    if FLIP_TXT.exists():
        sources['flip_rank23_text'] = parse_rank23_text(FLIP_TXT)
    if PIVOT17_JSON.exists():
        data = json.load(open(PIVOT17_JSON))
        sources['pivot17_transformed_rank23'] = [tuple(map(int, t)) for t in data['terms']]
    # Verify every source that claims to be a decomposition.
    for name, terms in sources.items():
        A = [a for a, _b, _c in terms]; B = [b for _a, b, _c in terms]; C = [c for _a, _b, c in terms]
        diff = verify_decomposition_f2(A, B, C)
        if diff != 0:
            raise RuntimeError(f'source {name} does not verify over F2: diff={diff}')
    return sources


def deletion_matches(terms: Sequence[Tuple[int, int, int]], seed_A: Sequence[int]) -> List[int]:
    A = [a for a, _b, _c in terms]
    hits = []
    for i in range(len(A)):
        if A[:i] + A[i+1:] == list(seed_A):
            hits.append(i)
    return hits

# ---------------------------------------------------------------------------
# Residual repair tests.


def repair_test_from_slots(seed_terms: Sequence[Tuple[int, int, int]], final_A: Sequence[int], changed_slots: Sequence[int], D_cols: Sequence[int], domain_maps: Optional[Sequence[Sequence[int]]] = None) -> dict:
    """Test a repair block.  Unchanged slots retain original A,B columns.

    changed_slots are indices in the 22-slot seed_terms/final_A lists whose
    B may be selected from a'_t\otimes domain.  final_A supplies a'_t.
    """
    k = len(changed_slots)
    changed_set = set(changed_slots)
    retained_cols = [vec_mask9_to_outer81(a, b) for i, (a, b, _c) in enumerate(seed_terms) if i not in changed_set]
    tagged_basis, E_reps, rank_L, d = build_quotient_basis(retained_cols, D_cols)
    result = {
        'k': k,
        'd': d,
        'rank_L': rank_L,
        'changed_slots': list(map(int, changed_slots)),
        'changed_A': [int(final_A[i]) for i in changed_slots],
        'status': None,
        'reason': None,
    }
    if d > k:
        result['status'] = 'IMPOSSIBLE_D_GT_K'
        result['reason'] = f'd={d} exceeds k={k}'
        return result

    # Build H_t = pi(a'_t \otimes domain_t) \cap E by enumerating the small B-domain.
    H_bases: List[List[int]] = []
    H_dims: List[int] = []
    H_tag_counts: List[int] = []
    tag_to_b_all: List[Dict[int, int]] = []
    for local_i, slot in enumerate(changed_slots):
        a = int(final_A[slot])
        if domain_maps is None:
            domain = range(512)  # include zero for linear span/intersection; representatives use nonzero tags.
        else:
            domain = domain_maps[local_i]
        tag_to_b: Dict[int, int] = {}
        tags: List[int] = []
        for b in domain:
            v = vec_mask9_to_outer81(a, int(b))
            rem, tag = reduce_by_basis(tagged_basis, v)
            if rem == 0:  # v lies in L + E; tag is its coordinate in E.
                if tag not in tag_to_b:
                    tag_to_b[tag] = int(b)
                    tags.append(tag)
        H_basis: List[int] = []
        for tg in tags:
            if tg and tags_rank(H_basis + [tg]) > len(H_basis):
                H_basis.append(tg)
        H_bases.append(H_basis)
        H_dims.append(tags_rank(H_basis))
        H_tag_counts.append(len(set(tags)))
        tag_to_b_all.append(tag_to_b)
    result['H_dims'] = H_dims
    result['H_tag_counts'] = H_tag_counts
    result['H_total_rank'] = tags_rank([v for H in H_bases for v in H])

    if d < k:
        result['status'] = 'UNDERDETERMINED_D_LT_K'
        result['reason'] = 'd<k: basis-transversal test is only sufficient, not complete'
        # Still record whether a simple independent d-cover exists.
        reps = choose_independent_representatives(tag_to_b_all, d) if d > 0 else []
        result['basis_cover_found'] = reps is not None
        return result

    # d == k: Hall/transversal condition is exact.
    ok, fail = hall_condition(H_bases, d)
    result['hall_ok'] = bool(ok)
    result['hall_failure'] = fail
    if not ok:
        result['status'] = 'NO_REPAIR_HALL_FAIL'
        return result

    reps = choose_independent_representatives(tag_to_b_all, d)
    if reps is None:
        result['status'] = 'NO_REPAIR_REP_SEARCH_FAIL'
        return result

    # Build full A/B using chosen reps, solve C, and verify.
    B_new = [int(b) for _a, b, _c in seed_terms]
    A_new = [int(a) for a in final_A]
    chosen_detail = []
    for slot, (tg, b) in zip(changed_slots, reps):
        B_new[slot] = int(b)
        chosen_detail.append({'slot': int(slot), 'tag': int(tg), 'B': int(b)})
    cols = [vec_mask9_to_outer81(a, b) for a, b in zip(A_new, B_new)]
    K = build_K_np_from_int_cols(cols)
    D_np = tensor_to_D(build_t333_f2())
    CT = gf2_solve_multi(K, D_np)
    if CT is None:
        result['status'] = 'HALL_OK_BUT_GLOBAL_SOLVE_FAILED'
        result['chosen'] = chosen_detail
        return result
    C_new = [vec_to_mask(CT[i]) for i in range(len(A_new))]
    diff = verify_decomposition_f2(A_new, B_new, C_new)
    result['chosen'] = chosen_detail
    result['status'] = 'REPAIR_FOUND' if diff == 0 else 'HALL_OK_BUT_BRENT_DIFF'
    result['brent_diff'] = int(diff)
    if diff == 0:
        result['A'] = A_new; result['B'] = B_new; result['C'] = C_new
    return result


def scan_b_only_blocks(terms: Sequence[Tuple[int, int, int]], source_name: str, D_cols: Sequence[int], max_k: int = 3, max_exact_records: int = 20) -> dict:
    """Classify B-only repair blocks after each deletion of a rank-23 scheme."""
    source_out = {
        'source': source_name,
        'max_k': max_k,
        'deleted': [],
        'aggregate': {},
        'successful_repairs': [],
    }
    agg = defaultdict(Counter)
    for del_idx in range(len(terms)):
        seed_terms = list(terms[:del_idx] + terms[del_idx+1:])
        seed_A = [a for a, _b, _c in seed_terms]
        del_rec = {'delete_index': del_idx, 'deleted_A': int(terms[del_idx][0]), 'by_k': {}}
        for k in range(1, max_k + 1):
            hist = Counter(); examples = []
            total = 0
            for block in itertools.combinations(range(len(seed_terms)), k):
                retained_cols = [vec_mask9_to_outer81(a, b) for i, (a, b, _c) in enumerate(seed_terms) if i not in block]
                _basis, _E, rank_L, d = build_quotient_basis(retained_cols, D_cols)
                total += 1
                if d > k:
                    cls = 'd_gt_k'
                elif d < k:
                    cls = 'd_lt_k'
                else:
                    # Exact minimal-defect case: run Hall test.
                    res = repair_test_from_slots(seed_terms, seed_A, block, D_cols)
                    cls = 'd_eq_k_hall_ok' if res.get('hall_ok') else 'd_eq_k_hall_fail'
                    if res.get('status') == 'REPAIR_FOUND':
                        source_out['successful_repairs'].append({'delete_index': del_idx, 'block': list(block), 'result': res})
                    if len(examples) < max_exact_records:
                        examples.append({'block': list(block), 'd': d, 'rank_L': rank_L, 'class': cls, 'H_dims': res.get('H_dims'), 'H_total_rank': res.get('H_total_rank'), 'hall_failure': res.get('hall_failure')})
                hist[cls] += 1
            del_rec['by_k'][str(k)] = {'total': total, 'hist': dict(hist), 'examples': examples}
            agg[f'k{k}'].update(hist)
        source_out['deleted'].append(del_rec)
    source_out['aggregate'] = {k: dict(v) for k, v in agg.items()}
    return source_out


def analyze_pipeline_candidates(sources: Dict[str, List[Tuple[int, int, int]]], D_cols: Sequence[int]) -> dict:
    if not PIPELINE_SUMMARY.exists():
        return {'status': 'no_pipeline_summary'}
    data = json.load(open(PIPELINE_SUMMARY))
    out = {'status': 'ok', 'pipeline_path': str(PIPELINE_SUMMARY), 'candidate_results': [], 'repair_found': []}
    for rec in data.get('results', []):
        if 'seed' not in rec or 'final_multiset' not in rec:
            continue
        name = rec.get('name', '')
        # Focus first on candidates that became Wang-admissible and reached independent-verification-record
        if rec.get('violations', 999) != 0 and rec.get('status') not in ('BRENT_UNSAT', 'TRACE_REJECTED'):
            continue
        seed_A = [int(x) for x in rec['seed']]
        final_A = [int(x) for x in rec['final_multiset']]
        changed = [i for i, (s, f) in enumerate(zip(seed_A, final_A)) if int(s) != int(f)]
        cand_out = {
            'name': name,
            'peer_status': rec.get('status'),
            'violations': rec.get('violations'),
            'trace_consistent': rec.get('trace_consistent'),
            'brent_sat': rec.get('brent_sat'),
            'changed_count': len(changed),
            'changed_slots': changed,
            'changed_pairs': [{'slot': i, 'old_A': seed_A[i], 'new_A': final_A[i]} for i in changed],
            'source_matches': [],
        }
        for sname, terms in sources.items():
            matches = deletion_matches(terms, seed_A)
            for del_idx in matches:
                seed_terms = list(terms[:del_idx] + terms[del_idx+1:])
                res = repair_test_from_slots(seed_terms, final_A, changed, D_cols)
                mrec = {'source': sname, 'delete_index': del_idx, 'deleted_A': int(terms[del_idx][0]), 'residual_test': {k: v for k, v in res.items() if k not in ('A','B','C')}}
                cand_out['source_matches'].append(mrec)
                if res.get('status') == 'REPAIR_FOUND':
                    wit_path = OUTDIR / f"rank22_from_{name}_{sname}_del{del_idx}.json"
                    wit_path.write_text(json.dumps(res, indent=2, sort_keys=True) + '\n')
                    out['repair_found'].append(str(wit_path))
        out['candidate_results'].append(cand_out)
    return out


def main():
    global OUTDIR
    ap = argparse.ArgumentParser()
    ap.add_argument('--outdir', type=Path, default=OUTDIR)
    ap.add_argument('--scan-b-only', action='store_true')
    ap.add_argument('--max-k', type=int, default=3)
    ap.add_argument('--b-only-sources', default='cn122_qmm', help='comma list or all')
    ap.add_argument('--pipeline', action='store_true')
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    OUTDIR = args.outdir
    t0 = time.time()
    D_cols = D_columns_as_ints()
    sources = load_sources()
    src_summary = {name: {'rank': len(terms), 'A': [int(a) for a,_b,_c in terms]} for name, terms in sources.items()}
    print('loaded sources:', ', '.join(sources))

    out = {
        'schema': 's0908_residual_repair_geometry_v1',
        'meaning': 'Exact quotient residual-space tests for local repairs near verified rank-23 decompositions; failures apply only to the specified retained-column neighborhood.',
        'sources': src_summary,
        'started_at': time.time(),
        'pipeline_analysis': None,
        'b_only_scans': {},
    }

    if args.pipeline:
        print('Analyzing peer pipeline A-swap candidates...', flush=True)
        out['pipeline_analysis'] = analyze_pipeline_candidates(sources, D_cols)
        print(json.dumps({'pipeline_candidates': len(out['pipeline_analysis'].get('candidate_results', [])), 'repair_found': out['pipeline_analysis'].get('repair_found', [])}, indent=2), flush=True)

    if args.scan_b_only:
        if args.b_only_sources.strip() == 'all':
            names = list(sources)
        else:
            names = [x.strip() for x in args.b_only_sources.split(',') if x.strip()]
        for name in names:
            if name not in sources:
                print(f'warning: source {name} missing', flush=True)
                continue
            print(f'Scanning B-only blocks for {name}, k<= {args.max_k}...', flush=True)
            out['b_only_scans'][name] = scan_b_only_blocks(sources[name], name, D_cols, args.max_k)
            print(json.dumps({'source': name, 'aggregate': out['b_only_scans'][name]['aggregate'], 'successful_repairs': len(out['b_only_scans'][name]['successful_repairs'])}, indent=2), flush=True)

    out['elapsed_sec'] = time.time() - t0
    opath = args.outdir / 'residual_repair_geometry.json'
    opath.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(f'Saved {opath}')
    print(json.dumps({'status':'ok','out':str(opath),'elapsed_sec':out['elapsed_sec']}, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
