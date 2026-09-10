#!/usr/bin/env python3
"""Anchor the proof-used Wang transport witnesses directly in the verified certificate.

research exposed transports from cached orbit representatives to the subspaces
used in the shortened rank>=21 proof.  The cache itself was derived from the
certificate, but a theorem-facing proof should not treat cache position labels
as mathematical facts.  This script therefore reads the pinned text-format
certificate directly, decodes the constrained-tensor records, and verifies that
all source nodes actually used by the proof have:

  * a matching certificate record index,
  * the decoded constraint subspace claimed in the witness,
  * the stated rank lower bound and proof type,
  * an explicit GL(3,2)xGL(3,2) or transpose action taking that decoded
    certificate subspace to the target subspace.

It also checks the forbidden high-rank pair endpoint without relying solely on
`key_to_orbit` labels: the eight directly decoded certificate representatives
484--491 are expanded under the same explicit actions, and every high-rank pair
with non-rank-one sum has its two-dimensional span in one of those expanded
orbits.  The transparent unary CNF/DRAT and clause-lifting manifests are linked
for the same eight representatives.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import json
import pickle
import re
import sys
import time
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

S04 = Path('assets/quotients/scripts')
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
import wang_capacity_lazy as wc  # type: ignore

S08 = Path('assets/structural/scripts')
if str(S08) not in sys.path:
    sys.path.insert(0, str(S08))
import transport_witness_layer as stw  # type: ignore

CERT = Path('assets/quotients/data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt')
VERIFY_RECEIPT = Path('assets/quotients/data/wang_f2_lb20/verify_receipt.json')
LUT_PATH = Path('assets/quotients/data/wang_f2_lb20/wang_subspace_lut.pkl')
CACHE_PATH = Path('assets/quotients/data/wang_f2_lb20/wang_orbit_closed_cache.pkl')
TRANSPARENT_BATCH = Path('assets/structural/data/transparent_unary_certs_484_491/batch_transparent_unary_dim2_certs_manifest.json')
LIFTING_BATCH = Path('assets/structural/data/transparent_lifting_batch/batch_transparent_lifting_verifier_manifest.json')
OUT = Path('assets/structural/data/anchored_transport/certificate_anchored_transport.json')
JSONL = Path('assets/structural/data/anchored_transport/dim2_core_row_anchored_witnesses.jsonl')


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def decode_textproto_bytes(quoted: str) -> bytes:
    return ast.literal_eval(quoted).encode('latin1')


def decode_constraints(quoted: str | None) -> List[int]:
    if not quoted:
        return []
    b = decode_textproto_bytes(quoted)
    if len(b) % 2:
        raise ValueError(f'constraint byte length not divisible by 2: {len(b)}')
    return [b[i] | (b[i + 1] << 8) for i in range(0, len(b), 2)]


def parse_certificate_records(path: Path) -> Tuple[Dict[str, object], List[Dict]]:
    text = path.read_text(errors='replace')
    top: Dict[str, object] = {}
    for key in ['problem_name', 'characteristic', 'extension_degree', 'na', 'nb', 'nc']:
        m = re.search(rf'^\s*{key}:\s*(.+)$', text, flags=re.M)
        if m:
            raw = m.group(1).strip()
            top[key] = ast.literal_eval(raw) if raw.startswith('"') else int(raw)
    records = []
    for block in text.split('constrained_tensors {')[1:]:
        # We only need fields that appear before or inside the first proof block;
        # this conservative slice is the same robust strategy used in the earlier
        # profiler and avoids depending on generated protobuf bindings.
        block0 = block.split('\n}\n', 1)[0]
        rec = {
            'index': None,
            'index_field_omitted': False,
            'rank_lower_bound': None,
            'proof_type': 'none',
            'projection_type': None,
            'extra_constraint': None,
            'backtracking_proof_size': None,
            'constraint_values': [],
        }
        m = re.search(r'\n\s*index:\s*(\d+)', '\n' + block0)
        if m:
            rec['index'] = int(m.group(1))
        else:
            rec['index_field_omitted'] = True
        m = re.search(r'\n\s*rank_lower_bound:\s*(-?\d+)', '\n' + block0)
        if m:
            rec['rank_lower_bound'] = int(m.group(1))
        m = re.search(r'\n\s*constraints:\s*(".*")', '\n' + block0)
        if m:
            rec['constraint_values'] = decode_constraints(m.group(1))
        for ptype, tag in [('flatten', 'flatten_matrix_proof'), ('forced_product', 'forced_product_proof'), ('degenerate', 'degenerate_proof'), ('backtracking', 'backtracking_proof')]:
            if tag in block0:
                rec['proof_type'] = ptype
                break
        m = re.search(r'projection_type:\s*(\d+)', block0)
        if m:
            rec['projection_type'] = int(m.group(1))
        m = re.search(r'extra_constraint:\s*(\d+)', block0)
        if m:
            rec['extra_constraint'] = int(m.group(1))
        m = re.search(r'proof_size:\s*(\d+)', block0)
        if m:
            rec['backtracking_proof_size'] = int(m.group(1))
        constraints = wc.rref_basis([int(x) for x in rec['constraint_values']], n=9)
        rec['constraint_count'] = len(rec['constraint_values'])
        rec['constraints_rref'] = list(constraints)
        rec['constraints_key'] = wc.pack_basis(constraints)
        records.append(rec)
    # In protobuf text format scalar fields equal to the default value are often
    # omitted.  The matrix certificate omits `index: 0` for the first record;
    # verifier code reads rt.index() and therefore sees the protobuf default 0.
    missing = [r for r in records if r['index'] is None]
    if len(missing) == 1:
        missing[0]['index'] = 0
    return top, records


def action_map(actions: Sequence[Dict]) -> Dict[int, Dict]:
    return {int(a['action_id']): a for a in actions}


def transform_key_with_witness(cert_basis: Sequence[int], witness: Dict, actions_by_id: Dict[int, Dict]) -> int:
    a = actions_by_id[int(witness['action_id'])]
    return wc.transform_key(tuple(int(x) for x in cert_basis), tuple(int(y) for y in a['basis_image']))


def anchor_one(target_key: int, witness: Dict | None, expected_lb: int | None, expected_proof_type: str | None, cert_by_index: Dict[int, Dict], actions_by_id: Dict[int, Dict]) -> Dict:
    if witness is None:
        return {'ok': False, 'reason': 'missing_transport_witness'}
    idx = int(witness['cert_index'])
    crecord = cert_by_index.get(idx)
    if crecord is None:
        return {'ok': False, 'reason': 'missing_certificate_record', 'cert_index': idx}
    cert_basis = [int(x) for x in crecord['constraints_rref']]
    image_key = transform_key_with_witness(cert_basis, witness, actions_by_id)
    expected_basis = [int(x) for x in witness['cert_basis']]
    checks = {
        'cert_record_found': True,
        'cert_basis_matches_witness': cert_basis == expected_basis,
        'image_key_matches_target': image_key == int(target_key),
        'lb_matches_expected': True if expected_lb is None else int(crecord['rank_lower_bound']) == int(expected_lb),
        'proof_type_matches_expected': True if expected_proof_type is None else str(crecord['proof_type']) == str(expected_proof_type),
    }
    return {
        'ok': all(checks.values()),
        'cert_index': idx,
        'certificate_record': {
            'constraints_rref': cert_basis,
            'constraint_count': int(crecord['constraint_count']),
            'rank_lower_bound': int(crecord['rank_lower_bound']),
            'proof_type': crecord['proof_type'],
            'backtracking_proof_size': crecord.get('backtracking_proof_size'),
            'projection_type': crecord.get('projection_type'),
            'extra_constraint': crecord.get('extra_constraint'),
        },
        'transport': witness,
        'image_key': image_key,
        'target_key': int(target_key),
        'checks': checks,
    }


def load_lut_and_cache():
    lut_obj = pickle.load(open(LUT_PATH, 'rb'))
    lut = {int(k): int(v) for k, v in (lut_obj['lut'] if isinstance(lut_obj, dict) and 'lut' in lut_obj else lut_obj).items()}
    cache = pickle.load(open(CACHE_PATH, 'rb'))
    return lut, cache


def build_finder_for_needed(dim2_rows: Sequence[Dict], line_rows: Sequence[Dict], plane_rows: Sequence[Dict], cache) -> stw.TransportFinder:
    finder = stw.TransportFinder(cache)
    for r in dim2_rows:
        finder.add_need(int(r['U_key']))
    for r in line_rows:
        finder.add_need(int(r['key']))
    for r in plane_rows:
        finder.add_need(int(r['U_key']))
    finder.solve()
    return finder


def direct_orbit_images(cert_basis: Sequence[int], actions: Sequence[Dict]) -> Dict[int, Dict]:
    out: Dict[int, Dict] = {}
    for a in actions:
        key = wc.transform_key(tuple(int(x) for x in cert_basis), tuple(int(y) for y in a['basis_image']))
        if key not in out:
            out[key] = {'action_id': int(a['action_id']), 'transpose_branch': bool(a['transpose_branch']), 'left_mask': int(a['left_mask']), 'right_mask': int(a['right_mask']), 'left_rows': a['left_rows'], 'right_rows': a['right_rows']}
    return out


def verify_forbidden_pair_endpoint(cert_by_index: Dict[int, Dict], actions: Sequence[Dict], transparent_by_index: Dict[int, Dict], lifting_by_index: Dict[int, Dict]) -> Dict:
    forbidden_indices = list(range(484, 492))
    orbit_image_map: Dict[int, int] = {}
    orbit_sizes = {}
    conflicts = []
    for idx in forbidden_indices:
        basis = [int(x) for x in cert_by_index[idx]['constraints_rref']]
        imgs = direct_orbit_images(basis, actions)
        orbit_sizes[str(idx)] = len(imgs)
        for key in imgs:
            old = orbit_image_map.get(key)
            if old is not None and old != idx:
                conflicts.append({'key': key, 'old_index': old, 'new_index': idx})
            orbit_image_map[key] = idx
    high = [a for a in range(1, 512) if wc.matrix_rank_of_mask(a) >= 2]
    bad_pair_count = 0
    bad_pair_key_set = set()
    bad_pair_index_hist = Counter()
    missing = []
    rankone_inside_forbidden = 0
    all_pair_index_hist = Counter()
    for a, b in combinations(high, 2):
        key = wc.pack_basis(wc.rref_basis([a, b], n=9))
        idx = orbit_image_map.get(key)
        if idx is not None:
            all_pair_index_hist[idx] += 1
        rsum = wc.matrix_rank_of_mask(a ^ b)
        if rsum != 1:
            bad_pair_count += 1
            bad_pair_key_set.add(key)
            if idx is None:
                if len(missing) < 20:
                    missing.append({'a': a, 'b': b, 'key': key, 'ranks': [wc.matrix_rank_of_mask(a), wc.matrix_rank_of_mask(b), rsum]})
            else:
                bad_pair_index_hist[idx] += 1
        elif idx is not None:
            rankone_inside_forbidden += 1
    per_index_certified = {}
    for idx in forbidden_indices:
        tr = transparent_by_index.get(idx, {})
        lf = lifting_by_index.get(idx, {})
        crecord = cert_by_index[idx]
        core_json = tr.get('core_json')
        core_basis_match = None
        if core_json and Path(core_json).exists():
            core = json.loads(Path(core_json).read_text())
            core_basis_match = wc.rref_basis(core['basis'], 9) == tuple(crecord['constraints_rref'])
        per_index_certified[str(idx)] = {
            'direct_certificate_basis': crecord['constraints_rref'],
            'direct_certificate_lb': crecord['rank_lower_bound'],
            'direct_certificate_proof_type': crecord['proof_type'],
            'transparent_cnf_verified': bool(tr.get('verified')) and int(tr.get('cadical_returncode', -1)) == 20 and int(tr.get('drat_returncode', -1)) == 0,
            'transparent_cnf_sha256': tr.get('cnf_sha256'),
            'transparent_drat_sha256': tr.get('drat_sha256'),
            'lifting_forward_established': bool(lf.get('forward_lifting_established_for_file')),
            'lifting_clauses_match': bool(lf.get('clauses_match_actual_file')),
            'core_basis_matches_direct_certificate': core_basis_match,
            'direct_orbit_image_size': orbit_sizes[str(idx)],
        }
    return {
        'meaning': 'The set of directly expanded certificate orbits 484--491 contains every high-rank dim-2 span whose two nonzero high-rank generators have non-rank-one sum; these are precisely the pair types excluded by the transparent integer occupation certificates.',
        'forbidden_indices': forbidden_indices,
        'direct_orbit_image_sizes': orbit_sizes,
        'direct_orbit_conflict_count': len(conflicts),
        'direct_orbit_conflicts_head': conflicts[:20],
        'high_rank_vertex_count': len(high),
        'bad_pair_non_rankone_sum_count': bad_pair_count,
        'bad_pair_unique_subspace_count': len(bad_pair_key_set),
        'bad_pair_missing_direct_forbidden_orbit_count': len(missing),
        'bad_pair_missing_head': missing,
        'bad_pair_index_hist': {str(k): int(v) for k, v in sorted(bad_pair_index_hist.items())},
        'all_pairs_in_forbidden_index_hist': {str(k): int(v) for k, v in sorted(all_pair_index_hist.items())},
        'rankone_sum_pairs_inside_forbidden_direct_orbits': rankone_inside_forbidden,
        'per_index_certificate_and_cnf': per_index_certified,
        'all_forbidden_pair_endpoint_ok': (not conflicts and not missing and all(v['transparent_cnf_verified'] and v['lifting_forward_established'] and v['core_basis_matches_direct_certificate'] for v in per_index_certified.values())),
    }


def summarize_anchors(records: Sequence[Dict], kind: str) -> Dict:
    failures = [r for r in records if not r['anchor'].get('ok')]
    cert_hist = Counter(r['anchor'].get('cert_index') for r in records if r['anchor'].get('ok'))
    lb_hist = Counter(r['anchor'].get('certificate_record', {}).get('rank_lower_bound') for r in records if r['anchor'].get('ok'))
    proof_hist = Counter(r['anchor'].get('certificate_record', {}).get('proof_type') for r in records if r['anchor'].get('ok'))
    return {
        'kind': kind,
        'total_instances': len(records),
        'failure_count': len(failures),
        'failures_head': failures[:10],
        'certificate_index_hist': {str(k): int(v) for k, v in sorted(cert_hist.items(), key=lambda kv: (str(kv[0])) )},
        'lb_hist': {str(k): int(v) for k, v in sorted(lb_hist.items(), key=lambda kv: (str(kv[0])) )},
        'proof_type_hist': {str(k): int(v) for k, v in sorted(proof_hist.items(), key=lambda kv: (str(kv[0])) )},
        'all_ok': len(failures) == 0,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', type=Path, default=OUT)
    ap.add_argument('--jsonl', type=Path, default=JSONL)
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    top, cert_records = parse_certificate_records(CERT)
    cert_by_index = {int(r['index']): r for r in cert_records if r['index'] is not None}
    verify_receipt = json.loads(VERIFY_RECEIPT.read_text()) if VERIFY_RECEIPT.exists() else {}
    cert_hash = sha256(CERT)
    lut, cache = load_lut_and_cache()
    dim2_rows, dim2_summary = stw.collect_dim2_core_rows(lut, cache)
    line_rows = stw.collect_line_keys(cache)
    plane_rows, plane_summary = stw.collect_affine_plane_keys(lut, cache)
    finder = build_finder_for_needed(dim2_rows, line_rows, plane_rows, cache)
    actions = stw.make_actions_with_witnesses()
    actions_by_id = action_map(actions)
    transparent = json.loads(TRANSPARENT_BATCH.read_text())
    transparent_by_index = {int(r['index']): r for r in transparent['records']}
    lifting = json.loads(LIFTING_BATCH.read_text())
    lifting_by_index = {int(r['index']): r for r in lifting['records']}

    anchored_dim2 = []
    args.jsonl.parent.mkdir(parents=True, exist_ok=True)
    with args.jsonl.open('wt') as jf:
        for r in dim2_rows:
            w = finder.witness_by_key.get(int(r['U_key']))
            anchor = anchor_one(int(r['U_key']), w, int(r['source_lb']), str(r['source_proof_type']), cert_by_index, actions_by_id)
            cap_check = (int(r['cap']) == int(r['outer_orbit'] and (18 - int(r['source_lb']))))
            rec = {**r, 'anchor': anchor, 'cap_equals_18_minus_source_lb': cap_check}
            anchored_dim2.append(rec)
            jf.write(json.dumps(rec, sort_keys=True) + '\n')

    anchored_lines = []
    for r in line_rows:
        w = finder.witness_by_key.get(int(r['key']))
        anchor = anchor_one(int(r['key']), w, int(r['lb']), None, cert_by_index, actions_by_id)
        anchored_lines.append({**r, 'anchor': anchor})

    anchored_planes = []
    for r in plane_rows:
        w = finder.witness_by_key.get(int(r['U_key']))
        anchor = anchor_one(int(r['U_key']), w, int(r['lb']), None, cert_by_index, actions_by_id)
        anchored_planes.append({**r, 'anchor': anchor})

    forbidden_pair_endpoint = verify_forbidden_pair_endpoint(cert_by_index, actions, transparent_by_index, lifting_by_index)

    # Direct coverage of the three one-dimensional source records; this avoids
    # using key_to_orbit labels to assert line coverage.
    line_source_indices = sorted({int(r['anchor']['cert_index']) for r in anchored_lines if r['anchor'].get('ok')})
    direct_line_union = {}
    for idx in line_source_indices:
        for key in direct_orbit_images(cert_by_index[idx]['constraints_rref'], actions):
            direct_line_union[key] = idx
    expected_line_keys = {wc.pack_basis(wc.rref_basis([a], n=9)) for a in range(1, 512)}
    direct_line_coverage = {
        'source_indices': line_source_indices,
        'direct_union_size': len(direct_line_union),
        'expected_nonzero_line_count': len(expected_line_keys),
        'missing_count': len(expected_line_keys - set(direct_line_union)),
        'extra_count': len(set(direct_line_union) - expected_line_keys),
        'all_direct_lines_covered': set(direct_line_union) == expected_line_keys,
    }

    source_nodes = {}
    for recs, label in [(anchored_dim2, 'dim2_core_rows'), (anchored_lines, 'line_bounds'), (anchored_planes, 'affine_plane_bounds')]:
        for r in recs:
            a = r['anchor']
            if not a.get('ok'):
                continue
            idx = str(a['cert_index'])
            node = source_nodes.setdefault(idx, {
                'cert_index': int(a['cert_index']),
                'constraints_rref': a['certificate_record']['constraints_rref'],
                'constraint_count': a['certificate_record']['constraint_count'],
                'rank_lower_bound': a['certificate_record']['rank_lower_bound'],
                'proof_type': a['certificate_record']['proof_type'],
                'uses': Counter(),
            })
            node['uses'][label] += 1
    for node in source_nodes.values():
        node['uses'] = {str(k): int(v) for k, v in sorted(node['uses'].items())}

    summaries = {
        'dim2_core_rows': summarize_anchors(anchored_dim2, 'dim2_core_rows'),
        'line_bounds': summarize_anchors(anchored_lines, 'line_bounds'),
        'affine_plane_bounds': summarize_anchors(anchored_planes, 'affine_plane_bounds'),
    }
    out = {
        'schema': 's0908_certificate_anchored_transport_v1',
        'meaning': 'Directly anchors all proof-used Wang transport witnesses in the pinned verified certificate, rather than accepting cache labels as facts. Also anchors the forbidden high-rank pair endpoint to the eight directly decoded representatives 484--491 and their transparent CNF/DRAT proofs.',
        'certificate': {
            'path': str(CERT),
            'sha256': cert_hash,
            'top_fields': top,
            'record_count': len(cert_records),
            'indices_are_0_to_record_count_minus_1_after_textproto_default': sorted(cert_by_index) == list(range(len(cert_records))),
            'omitted_index_fields_interpreted_as_protobuf_default_zero': sum(1 for r in cert_records if r.get('index_field_omitted')),
            'verify_receipt_path': str(VERIFY_RECEIPT),
            'verify_receipt_status': verify_receipt.get('status'),
            'verify_receipt_claimed_lower_bound': verify_receipt.get('claimed_lower_bound'),
            'verify_receipt_certificate_sha256': verify_receipt.get('certificate_sha256'),
            'verify_receipt_hash_matches_certificate': verify_receipt.get('certificate_sha256') == cert_hash,
        },
        'source_files': {
            'lut': str(LUT_PATH),
            'cache': str(CACHE_PATH),
            'transparent_batch_manifest': str(TRANSPARENT_BATCH),
            'lifting_batch_manifest': str(LIFTING_BATCH),
            'dim2_row_jsonl': str(args.jsonl),
        },
        'source_hashes': {
            'lut': sha256(LUT_PATH),
            'cache': sha256(CACHE_PATH),
            'transparent_batch_manifest': sha256(TRANSPARENT_BATCH),
            'lifting_batch_manifest': sha256(LIFTING_BATCH),
        },
        'transport_action_count': len(actions),
        'transport_witness_key_count': len(finder.witness_by_key),
        'transport_missing_by_orbit_head': {str(k): v for k, v in sorted(finder.missing_by_orbit.items())[:20]},
        'summaries': summaries,
        'dim2_core_source_summary': dim2_summary,
        'affine_plane_source_summary': plane_summary,
        'dim2_row_jsonl_sha256': sha256(args.jsonl),
        'line_direct_coverage': direct_line_coverage,
        'forbidden_pair_endpoint': forbidden_pair_endpoint,
        'source_certificate_nodes_actually_used': {str(k): v for k, v in sorted(source_nodes.items(), key=lambda kv: int(kv[0]))},
        'all_anchor_checks_ok': (
            verify_receipt.get('status') == 'verified'
            and verify_receipt.get('certificate_sha256') == cert_hash
            and all(s['all_ok'] for s in summaries.values())
            and direct_line_coverage['all_direct_lines_covered']
            and forbidden_pair_endpoint['all_forbidden_pair_endpoint_ok']
        ),
        'elapsed_sec': time.time() - t0,
    }
    args.out.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'ok', 'out': str(args.out), 'all_anchor_checks_ok': out['all_anchor_checks_ok'], 'summaries': {k: {'total': v['total_instances'], 'failures': v['failure_count']} for k, v in summaries.items()}, 'forbidden_pair_endpoint_ok': forbidden_pair_endpoint['all_forbidden_pair_endpoint_ok'], 'elapsed_sec': out['elapsed_sec']}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
