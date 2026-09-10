#!/usr/bin/env python3
r"""analysis: symmetry reduction and proof-producing CNF for repeated E11-core A-directions.

Purpose
-------
The E11 core rank-19 search has six projective A-directions with one-dimensional
Wang capacity 2.  Any repeated-direction support must repeat one of them.  This
script (i) computes the induced action of the T-level stabilizer of E11 on the
quotient core F2^9/<E11>, verifies the geometric orbit statement for these six
points, and (ii) builds a compact CNF for one fixed repeated point using only
valid necessary constraints:

  * total multiplicity = 19 with the chosen point fixed with multiplicity 2;
  * selected compact Wang rows from the stored repeated-branch separator;
  * all nonzero contraction lower bounds for the E11 core;
  * unconditional quotient-rank inequalities converted from the stored cuts.

An UNSAT+DRAT result for the fixed point, together with the checked induced
symmetry, proves that no repeated-direction rank-19 E11-core decomposition can
satisfy these necessary constraints.  It does not settle the distinct-A branch
and does not by itself produce or exclude a full 3x3 rank-22 algorithm.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient
from fixed_A_saturation import mat_rank_f2
from complete_core_and_transversal import ROOT, build_core_constraints
from quotient_rank_cuts import build_contractions, point_mask_for_q
from wang_capacity_lazy import (
    basis_image_for_action,
    generate_gl3,
    rref_basis,
    subspace_points_from_basis,
    transform_mask,
    unpack_basis,
)

OUTDIR = ROOT / "workspace/data/repeat_branch_certificate"
ALLMASK = (1 << 255) - 1
BIT_LABELS = [
    "E11", "E12", "E13",
    "E21", "E22", "E23",
    "E31", "E32", "E33",
]


def sha256(path: Path) -> str | None:
    if not path.exists() or not path.is_file():
        return None
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(4 * 1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def load_lut(path: Path):
    with path.open('rb') as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload['lut'].items()}, payload.get('meta', {})


def label9(mask: int) -> str:
    if mask == 0:
        return "0"
    return "+".join(BIT_LABELS[i] for i in range(9) if (mask >> i) & 1)


def label8(core: CoreQuotient, p: int) -> str:
    return label9(core.lift8(p))


def build_action_images_with_flag():
    """Return unique T-level A-side action images with their transpose flag."""
    gl = generate_gl3()
    out = []
    seen = set()
    for L in gl:
        for R in gl:
            for tr in (False, True):
                img = basis_image_for_action(L, R, tr)
                if img not in seen:
                    seen.add(img)
                    out.append((img, tr))
    assert len(out) == 2 * 168 * 168
    return out


def induced_core_permutation(core: CoreQuotient, img: Sequence[int]) -> Tuple[int, ...]:
    """Permutation of the 255 nonzero quotient directions induced by img."""
    perm = []
    for p in range(1, 256):
        im9 = transform_mask(core.lift8(p), img)
        q = core.project9(im9)
        if q == 0:
            raise AssertionError(f"nonzero quotient point {p} mapped to zero")
        perm.append(q)
    if sorted(perm) != list(range(1, 256)):
        raise AssertionError("induced map is not a permutation")
    return tuple(perm)


def orbit_partition(points: Iterable[int], perms: Sequence[Tuple[int, ...]]) -> List[List[int]]:
    pts = set(int(p) for p in points)
    orbits = []
    while pts:
        seed = min(pts)
        orb = {seed}
        changed = True
        while changed:
            changed = False
            for p in list(orb):
                for g in perms:
                    q = g[p - 1]
                    if q not in orb:
                        orb.add(q)
                        changed = True
        orbits.append(sorted(orb))
        pts -= orb
    return sorted(orbits, key=lambda z: (len(z), z))


def analyze_symmetry(core: CoreQuotient, point_cap: Dict[int, int]) -> dict:
    t0 = time.time()
    actions = build_action_images_with_flag()
    stab_all = [(img, tr) for img, tr in actions if transform_mask(core.pivot, img) == core.pivot]
    stab_no_tr = [(img, tr) for img, tr in stab_all if not tr]
    stab_tr = [(img, tr) for img, tr in stab_all if tr]

    def unique_core_perms(items):
        seen = {}
        for img, tr in items:
            perm = induced_core_permutation(core, img)
            seen.setdefault(perm, tr)
        return list(seen.keys())

    perms_all = unique_core_perms(stab_all)
    perms_no_tr = unique_core_perms(stab_no_tr)
    perms_tr = unique_core_perms(stab_tr)

    cap2 = sorted(p for p, c in point_cap.items() if c >= 2)
    expected = [1, 2, 3, 4, 32, 36]
    no_tr_orbits = orbit_partition(cap2, perms_no_tr)
    full_orbits = orbit_partition(cap2, perms_all)

    # Find explicit maps from each cap2 point to 1 for the symmetry certificate.
    maps_to_one = {}
    for p in cap2:
        witness = None
        for idx, g in enumerate(perms_all):
            if g[p - 1] == 1:
                witness = {'perm_index': idx, 'image_of_p': 1}
                break
        maps_to_one[str(p)] = witness

    # Check quotient linearity on basis bits.
    basis8 = [1 << i for i in range(8)]
    linearity_ok = True
    for g in perms_all[: min(100, len(perms_all))]:
        for mask in range(1, 256):
            accum = 0
            for i, b in enumerate(basis8):
                if mask & b:
                    accum ^= g[b - 1]
            if accum != g[mask - 1]:
                linearity_ok = False
                break
        if not linearity_ok:
            break

    return {
        'schema': 'induced_core_symmetry_v1',
        'pivot': core.pivot,
        'pivot_label': label9(core.pivot),
        'full_T_action_count': len(actions),
        'T_stabilizer_count_fixing_pivot': len(stab_all),
        'T_stabilizer_no_transpose_count': len(stab_no_tr),
        'T_stabilizer_transpose_count': len(stab_tr),
        'unique_induced_core_stabilizer_count': len(perms_all),
        'unique_induced_no_transpose_count': len(perms_no_tr),
        'unique_induced_transpose_count': len(perms_tr),
        'linearity_spotcheck_ok': linearity_ok,
        'capacity_two_points': cap2,
        'capacity_two_labels': {str(p): label8(core, p) for p in cap2},
        'expected_two_rulings_through_deleted_direction': {
            'row_ruling': [1, 2, 3],
            'row_ruling_labels': {str(p): label8(core, p) for p in [1, 2, 3]},
            'column_ruling': [4, 32, 36],
            'column_ruling_labels': {str(p): label8(core, p) for p in [4, 32, 36]},
        },
        'capacity_two_matches_expected': cap2 == expected,
        'no_transpose_orbits_on_capacity_two': no_tr_orbits,
        'full_stabilizer_orbits_on_capacity_two': full_orbits,
        'transpose_exchanges_rulings': any(g[1 - 1] in {4, 32, 36} for g in perms_tr),
        'maps_each_capacity_two_point_to_1': maps_to_one,
        'elapsed_sec': round(time.time() - t0, 3),
    }


def extract_compact_constraints(source: Path, records: list, core: CoreQuotient, lut: Dict[int, int]) -> Tuple[set, list]:
    src = json.loads(source.read_text())
    wang_keys = set()
    qcuts = []
    for r in records:
        if int(r['dim8']) in (1, 2):
            wang_keys.add(int(r['key8']))
    for rnd in src.get('rounds', []):
        for w in rnd.get('learned_wang_rows', []):
            wang_keys.add(int(w['key8']))
        for c in rnd.get('learned_quotient_cuts', []):
            q1, q2 = sorted([int(c['sources'][0]), int(c['sources'][1])])
            qcuts.append({
                'side': str(c['side']),
                'sources': [q1, q2],
                'target': int(c['target']),
                'requirement': int(c['requirement']),
                'W_dim': int(c.get('W_dim', -1)),
                'outside_point_count': int(c.get('outside_point_count', -1)),
            })
    # Unique quotient cuts by their mathematical key.
    uniq = {}
    for c in qcuts:
        uniq[(c['side'], c['sources'][0], c['sources'][1], c['target'])] = c
    return wang_keys, list(uniq.values())


def build_fixed_repeat_cnf(
    outdir: Path,
    source: Path,
    fixed_repeat: int,
    card_encoding: str = 'seqcounter',
    pb_encoding: str = 'best',
) -> dict:
    from pysat.card import CardEnc, EncType as CardEncType
    from pysat.formula import CNF
    from pysat.pb import PBEnc, EncType as PBEncType

    card_enc_map = {
        'seqcounter': CardEncType.seqcounter,
        'totalizer': CardEncType.totalizer,
        'cardnetwrk': CardEncType.cardnetwrk,
        'sortnetwrk': CardEncType.sortnetwrk,
    }
    pb_enc_map = {
        'best': PBEncType.best,
        'bdd': PBEncType.bdd,
        'seqcounter': PBEncType.seqcounter,
        'sortnetwrk': PBEncType.sortnetwrk,
        'adder': PBEncType.adder,
        'binmerge': PBEncType.binmerge,
    }
    if card_encoding not in card_enc_map:
        raise ValueError(f'unknown card encoding {card_encoding}')
    if pb_encoding not in pb_enc_map:
        raise ValueError(f'unknown pb encoding {pb_encoding}')

    t0 = time.time()
    outdir.mkdir(parents=True, exist_ok=True)
    s = 19
    core = CoreQuotient(1)
    lut, lut_meta = load_lut(ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
    records, core_meta = build_core_constraints(core, lut)
    record_by_key = {int(r['key8']): r for r in records}
    T_core = np.load(ROOT / 'workspace/data/restricted_cores/mask_001_E11_core.npy').astype(np.uint8) % 2
    contractions = build_contractions(T_core)
    masks = {q: point_mask_for_q(q) for q in contractions}
    points = list(range(1, 256))

    point_cap = {}
    for p in points:
        key8 = core.key8_from_rows([p])
        key9 = core.key9_from_key8(key8)
        point_cap[p] = max(0, min(s, s - int(lut[key9])))
    if point_cap.get(fixed_repeat, 0) < 2:
        raise ValueError(f'fixed point {fixed_repeat} does not have capacity two')

    sym = analyze_symmetry(core, point_cap)
    wang_keys, qcuts = extract_compact_constraints(source, records, core, lut)

    # Binary token expansion of multiplicities.  A cap-2 point has two possible
    # copy variables.  The fixed repeated point contributes two constant copies.
    fixed_counts = {fixed_repeat: 2}
    token_point: Dict[int, int] = {}
    tokens_by_point: Dict[int, List[int]] = defaultdict(list)
    next_var = 0
    for p in points:
        for _ in range(point_cap[p] - fixed_counts.get(p, 0)):
            next_var += 1
            token_point[next_var] = p
            tokens_by_point[p].append(next_var)

    cnf = CNF()
    top = next_var
    enc_stats = Counter()
    constraint_stats = Counter()
    skipped_stats = Counter()
    impossible_constraints = []

    def add_raw_clause(clause: List[int], reason: str):
        cnf.append(clause)
        enc_stats[f'{reason}_clauses'] += 1

    def add_card_atmost(lits: List[int], bound: int, label: str):
        nonlocal top
        constraint_stats[f'{label}_constraints'] += 1
        if bound < 0:
            add_raw_clause([], f'{label}_impossible')
            impossible_constraints.append({'type': label, 'sense': '<=', 'bound': bound})
            return
        if bound >= len(lits):
            skipped_stats[f'{label}_skipped_tautological'] += 1
            return
        if bound == 0:
            for lit in lits:
                add_raw_clause([-lit], f'{label}_unit_atmost0')
            return
        enc = CardEnc.atmost(lits=lits, bound=bound, top_id=top, encoding=card_enc_map[card_encoding])
        cnf.extend(enc.clauses)
        enc_stats[f'{label}_clauses'] += len(enc.clauses)
        top = max(top, enc.nv)

    def add_card_atleast(lits: List[int], bound: int, label: str):
        nonlocal top
        constraint_stats[f'{label}_constraints'] += 1
        if bound <= 0:
            skipped_stats[f'{label}_skipped_tautological'] += 1
            return
        if bound > len(lits):
            add_raw_clause([], f'{label}_impossible')
            impossible_constraints.append({'type': label, 'sense': '>=', 'bound': bound, 'available': len(lits)})
            return
        if bound == len(lits):
            for lit in lits:
                add_raw_clause([lit], f'{label}_unit_all')
            return
        enc = CardEnc.atleast(lits=lits, bound=bound, top_id=top, encoding=card_enc_map[card_encoding])
        cnf.extend(enc.clauses)
        enc_stats[f'{label}_clauses'] += len(enc.clauses)
        top = max(top, enc.nv)

    def add_pb_atleast(lits: List[int], weights: List[int], bound: int, label: str, meta_head: dict | None = None):
        nonlocal top
        constraint_stats[f'{label}_constraints'] += 1
        max_weight = sum(weights)
        if bound <= 0:
            skipped_stats[f'{label}_skipped_tautological'] += 1
            return
        if bound > max_weight:
            add_raw_clause([], f'{label}_impossible')
            impossible_constraints.append({'type': label, 'sense': '>=', 'bound': bound, 'available_weight': max_weight, 'meta': meta_head})
            return
        if all(w == 1 for w in weights):
            add_card_atleast(lits, bound, label + '_card')
            return
        enc = PBEnc.atleast(lits=lits, weights=weights, bound=bound, top_id=top, encoding=pb_enc_map[pb_encoding])
        cnf.extend(enc.clauses)
        enc_stats[f'{label}_clauses'] += len(enc.clauses)
        top = max(top, enc.nv)

    def fixed_contribution_points(pts: Iterable[int], coeff: int = 1) -> int:
        pset = set(pts)
        return sum(coeff * c for p, c in fixed_counts.items() if p in pset)

    # Total multiplicity: fixed point already contributes 2.
    all_token_lits = sorted(token_point)
    add_card_atmost(all_token_lits, s - 2, 'total')
    add_card_atleast(all_token_lits, s - 2, 'total')

    # Wang rows: sum_{p in subspace} x_p <= s-L.
    wang_by_dim = Counter()
    for key8 in sorted(wang_keys):
        rec = record_by_key[int(key8)]
        cap = s - int(rec['L'])
        pts = subspace_points_from_basis(unpack_basis(int(key8)))
        rhs = cap - fixed_contribution_points(pts)
        lits = []
        for p in pts:
            lits.extend(tokens_by_point.get(p, []))
        add_card_atmost(lits, rhs, 'wang')
        wang_by_dim[int(rec['dim8'])] += 1

    # Contraction lower bounds: sum_{q(p)=1} x_p >= rank L(q).
    contraction_rank_dist = Counter()
    contraction_added = 0
    for q, c in contractions.items():
        rk = int(c['rank'])
        contraction_rank_dist[rk] += 1
        if rk <= 0:
            continue
        fixed = 2 if ((q & fixed_repeat).bit_count() & 1) else 0
        rhs = rk - fixed
        lits = []
        for p in points:
            if ((q & p).bit_count() & 1):
                lits.extend(tokens_by_point.get(p, []))
        add_card_atleast(lits, rhs, 'contraction_lower')
        contraction_added += 1

    # Unconditional quotient-rank cuts.
    qcut_side_dist = Counter()
    qcut_req_dist = Counter()
    for c in qcuts:
        q1, q2 = int(c['sources'][0]), int(c['sources'][1])
        target = int(c['target'])
        req = int(c['requirement'])
        rq1 = int(contractions[q1]['rank'])
        rq2 = int(contractions[q2]['rank'])
        source_union = masks[q1] | masks[q2]
        outside_mask = masks[target] & (~source_union) & ALLMASK
        rhs = req + rq1 + rq2
        lits = []
        weights = []
        fixed_coeff_sum = 0
        for p in points:
            coeff = 0
            if (outside_mask >> (p - 1)) & 1:
                coeff += 1
            if ((q1 & p).bit_count() & 1):
                coeff += 1
            if ((q2 & p).bit_count() & 1):
                coeff += 1
            if coeff == 0:
                continue
            if p in fixed_counts:
                fixed_coeff_sum += coeff * fixed_counts[p]
            for lit in tokens_by_point.get(p, []):
                lits.append(lit)
                weights.append(coeff)
        add_pb_atleast(lits, weights, rhs - fixed_coeff_sum, 'unconditional_qcut',
                       meta_head={'side': c['side'], 'sources': c['sources'], 'target': target})
        qcut_side_dist[str(c['side'])] += 1
        qcut_req_dist[int(req)] += 1

    # Write CNF and metadata.
    cnf_path = outdir / f'fixed_repeat_p{fixed_repeat}.cnf'
    meta_path = outdir / f'fixed_repeat_p{fixed_repeat}.meta.json'
    cnf.to_file(str(cnf_path))

    meta = {
        'schema': 'fixed_repeat_compact_cnf_v1',
        'field': 'F2',
        'core': 'E11',
        'rank_s': s,
        'fixed_repeat_point': fixed_repeat,
        'fixed_repeat_label': label8(core, fixed_repeat),
        'fixed_multiplicity': 2,
        'meaning': (
            'CNF encodes compact necessary conditions for a rank-19 E11-core A-multiset '
            'with the chosen projected A-direction repeated twice. UNSAT+DRAT proves this '
            'fixed-repeat instance impossible under valid Wang, contraction, and unconditional '
            'quotient-rank constraints. The stored symmetry analysis supplies coverage of all '
            'six capacity-two repeated directions. Distinct-A supports remain outside this CNF.'
        ),
        'source_separator': str(source),
        'source_sha256': sha256(source),
        'lut_meta_coverage_ok': lut_meta.get('coverage_ok'),
        'complete_core_table_meta': core_meta,
        'point_cap_distribution': {str(k): int(v) for k, v in sorted(Counter(point_cap.values()).items())},
        'symmetry': sym,
        'token_encoding': {
            'description': 'Binary token expansion of integer multiplicities. Each cap-1 point has one token; each nonfixed cap-2 point has two tokens; the fixed point contributes two constant tokens.',
            'base_token_variables': next_var,
            'final_cnf_variables': top,
            'fixed_counts': {str(k): int(v) for k, v in fixed_counts.items()},
            'tokens_by_point_nonempty': {str(p): lits for p, lits in sorted(tokens_by_point.items()) if lits},
        },
        'constraint_input_counts': {
            'unique_compact_wang_rows': len(wang_keys),
            'unique_compact_wang_rows_by_dim8': {str(k): int(v) for k, v in sorted(wang_by_dim.items())},
            'contraction_lower_bounds': contraction_added,
            'contraction_rank_distribution': {str(k): int(v) for k, v in sorted(contraction_rank_dist.items())},
            'unconditional_quotient_cuts': len(qcuts),
            'unconditional_quotient_cuts_by_side': dict(qcut_side_dist),
            'unconditional_quotient_requirement_distribution': {str(k): int(v) for k, v in sorted(qcut_req_dist.items())},
        },
        'cnf_summary': {
            'card_encoding': card_encoding,
            'pb_encoding': pb_encoding,
            'variables': top,
            'clauses': len(cnf.clauses),
            'build_elapsed_sec': round(time.time() - t0, 3),
            'constraint_stats': dict(constraint_stats),
            'encoding_clause_stats': dict(enc_stats),
            'skipped_stats': dict(skipped_stats),
            'impossible_constraints': impossible_constraints[:20],
            'impossible_constraint_count': len(impossible_constraints),
        },
        'files': {
            'cnf': str(cnf_path),
            'meta': str(meta_path),
        },
    }
    meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True) + '\n')
    # Compute hashes after writing meta.
    meta['files']['cnf_sha256'] = sha256(cnf_path)
    meta['files']['meta_sha256_before_hash_insertion'] = sha256(meta_path)
    meta_path.write_text(json.dumps(meta, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'cnf': str(cnf_path),
        'meta': str(meta_path),
        'vars': top,
        'clauses': len(cnf.clauses),
        'fixed_repeat': fixed_repeat,
        'fixed_label': label8(core, fixed_repeat),
        'wang_rows': len(wang_keys),
        'qcuts': len(qcuts),
        'sym_full_orbits': sym['full_stabilizer_orbits_on_capacity_two'],
        'sym_no_transpose_orbits': sym['no_transpose_orbits_on_capacity_two'],
        'build_sec': round(time.time() - t0, 3),
    }, sort_keys=True))
    return meta


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--source', type=Path,
                    default=ROOT / 'workspace/data/quotient_rank_cuts/core_e11_multiset_quotient_sep_24r_fullstored.json')
    ap.add_argument('--fixed-repeat', type=int, default=1)
    ap.add_argument('--outdir', type=Path, default=OUTDIR)
    ap.add_argument('--card-encoding', choices=['seqcounter', 'totalizer', 'cardnetwrk', 'sortnetwrk'], default='seqcounter')
    ap.add_argument('--pb-encoding', choices=['best', 'bdd', 'seqcounter', 'sortnetwrk', 'adder', 'binmerge'], default='best')
    ap.add_argument('--symmetry-only', action='store_true')
    args = ap.parse_args()

    if args.symmetry_only:
        s = 19
        core = CoreQuotient(1)
        lut, _ = load_lut(ROOT / 'workspace/data/wang_f2_lb20/wang_subspace_lut.pkl')
        point_cap = {}
        for p in range(1, 256):
            key8 = core.key8_from_rows([p])
            key9 = core.key9_from_key8(key8)
            point_cap[p] = max(0, min(s, s - int(lut[key9])))
        sym = analyze_symmetry(core, point_cap)
        args.outdir.mkdir(parents=True, exist_ok=True)
        path = args.outdir / 'induced_core_symmetry.json'
        path.write_text(json.dumps(sym, indent=2, sort_keys=True) + '\n')
        print(json.dumps(sym, indent=2, sort_keys=True))
        print(f'Saved {path}')
        return

    build_fixed_repeat_cnf(args.outdir, args.source, args.fixed_repeat, args.card_encoding, args.pb_encoding)


if __name__ == '__main__':
    main()
