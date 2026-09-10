#!/usr/bin/env python3
"""analysis independent review of the analysis repeated-direction E11-core certificate.

This is not a new proof generator.  It checks that the files named in the
certificate manifest carry the semantics this investigation intends to use:
  * the primary CNF is UNSAT and has a DRAT-trim VERIFIED log;
  * the small proof uses only total length, token capacities, fixed p=1 copies,
    and selected Wang rows, not quotient-rank or fixed-A constraints;
  * deterministic re-encoding reproduces the proof CNF hash;
  * the induced E11 quotient stabilizer transports all six capacity-two repeated
    directions to p=1 and preserves selected Wang-row lower-bound values;
  * the manifest scope does not claim a full E11-core lower bound or a full
    tensor-rank result.
"""
from __future__ import annotations
import hashlib, json
from pathlib import Path
from collections import Counter

ROOT = Path('research/research_record')
BASE = ROOT / 'workspace/data/repeat_branch_certificate'
OUT = ROOT / 'workspace/data/review/repeated_certificate_review.json'


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def load(path: Path):
    return json.loads(path.read_text())


def main():
    manifest_path = BASE / 'certificate_manifest.json'
    status_path = BASE / 'iis_shrink_p1/drat/fixed_repeat_p1_iis.status.json'
    meta_path = BASE / 'iis_shrink_p1/fixed_repeat_p1_iis.meta.json'
    reencode_path = BASE / 'iis_shrink_p1/reencode_check/reencode_verify.json'
    transport_path = BASE / 'symmetry_row_transport_check.json'
    symmetry_path = BASE / 'induced_core_symmetry.json'
    shrink_path = BASE / 'iis_shrink_p1/shrink_summary.json'

    manifest = load(manifest_path)
    status = load(status_path)
    meta = load(meta_path)
    reenc = load(reencode_path)
    transport = load(transport_path)
    sym = load(symmetry_path)
    shrink = load(shrink_path)

    primary = manifest['primary_certificate']
    file_checks = {}
    for label, rec in primary['files'].items():
        p = Path(rec['path'])
        file_checks[label] = {
            'path': str(p),
            'exists': p.exists(),
            'expected_sha256': rec.get('sha256'),
            'actual_sha256': sha256(p) if p.exists() and rec.get('sha256') else None,
            'hash_match': (sha256(p) == rec.get('sha256')) if p.exists() and rec.get('sha256') else None,
            'size': p.stat().st_size if p.exists() else None,
        }

    selected_records = shrink.get('selected_constraint_records', [])
    selected_kind = Counter(r.get('kind') for r in selected_records)
    selected_dims = Counter(int(r.get('dim8')) for r in selected_records if 'dim8' in r)
    selected_L = Counter(int(r.get('L')) for r in selected_records if 'L' in r)

    scope_text = ' '.join(manifest.get('scope_limits', []))
    review = {
        'schema': 'repeat_certificate_review_v1',
        'field': 'F2',
        'core': 'E11',
        'manifest': str(manifest_path),
        'statement_reviewed': manifest.get('mathematical_statement'),
        'file_hash_checks': file_checks,
        'sat_proof_status': {
            'cadical_exit_is_unsat_20': status.get('cadical_exit') == 20,
            'cadical_log_status': status.get('cadical_log_parse', {}).get('sat_status'),
            'drat_trim_exit_zero': status.get('drat_trim_exit') == 0,
            'drat_trim_verified': bool(status.get('drat_trim_log_parse', {}).get('verified')),
            'drat_trim_status': status.get('drat_trim_log_parse', {}).get('sat_status'),
            'cnf_header': status.get('drat_trim_log_parse', {}).get('trim_parsed_header'),
            'status_self_file_info_note': 'status JSON was written after its file_info snapshot, so its internal self exists=false entry is a harmless bookkeeping artifact' if not status.get('file_info', {}).get(str(status_path), {}).get('exists', True) else 'self file_info present',
        },
        'small_formula_semantics': {
            'meta_schema': meta.get('schema'),
            'fixed_repeat_point': meta.get('fixed_repeat_point'),
            'fixed_repeat_label': meta.get('fixed_repeat_label'),
            'fixed_multiplicity': meta.get('fixed_multiplicity'),
            'rank_s': meta.get('rank_s'),
            'token_variables_before_aux': meta.get('token_variables_before_aux'),
            'core_constraint_count': meta.get('core_constraint_count'),
            'core_constraints_by_kind': meta.get('core_constraints_by_kind'),
            'encoding_stats': meta.get('encoding_stats'),
            'selected_records_count': len(selected_records),
            'selected_kind': {str(k): int(v) for k, v in sorted(selected_kind.items())},
            'selected_dims': {str(k): int(v) for k, v in sorted(selected_dims.items())},
            'selected_L': {str(k): int(v) for k, v in sorted(selected_L.items())},
            'uses_only_wang_rows_beyond_total_and_token_bounds': meta.get('core_constraints_by_kind') == {'wang': 262} and selected_kind == Counter({'wang': 262}),
            'quotient_rank_or_contraction_rows_used': any(k in selected_kind for k in ('unconditional_qcut', 'contraction_lower')),
            'hard_total_constraints': meta.get('encoding_stats', {}).get('hard_total_constraints'),
        },
        'reencoding': {
            'hash_match': bool(reenc.get('hash_match')),
            'original_cnf_sha256': reenc.get('original_cnf_sha256'),
            'reencoded_cnf_sha256': reenc.get('reencoded_cnf_sha256'),
            'selected_indices_count': reenc.get('selected_indices_count'),
        },
        'symmetry_transport': {
            'capacity_two_points': sym.get('capacity_two_points'),
            'capacity_two_matches_expected': bool(sym.get('capacity_two_matches_expected')),
            'full_stabilizer_orbits': sym.get('full_stabilizer_orbits_on_capacity_two'),
            'no_transpose_orbits': sym.get('no_transpose_orbits_on_capacity_two'),
            'transpose_exchanges_rulings': bool(sym.get('transpose_exchanges_rulings')),
            'maps_each_capacity_two_point_to_1_all_present': all(v is not None and v.get('image_of_p') == 1 for v in sym.get('maps_each_capacity_two_point_to_1', {}).values()),
            'selected_rows_preserve_L_under_all_stabilizer_perms': bool(transport.get('all_selected_rows_preserve_L_under_all_stabilizer_perms')),
            'transported_pairs_checked': transport.get('transported_dim_counter_total'),
            'witness_maps_all_preimage_image_preserve_L': all(v.get('selected_rows_image_and_preimage_preserve_L') for v in transport.get('witness_maps_to_p1', {}).values()),
            'complete_core_table_constraint_count': transport.get('complete_core_table_meta', {}).get('constraint_count'),
        },
        'scope_guard': {
            'manifest_explicitly_says_distinct_branch_not_excluded': 'distinct projected-A branch' in scope_text,
            'manifest_explicitly_says_no_core_lb20': 'E11-core rank >=20' in scope_text,
            'manifest_explicitly_says_no_rank22_algorithm': 'rank<=22' in scope_text,
            'manifest_explicitly_says_no_char0_rank23': 'characteristic zero' in scope_text,
        },
    }
    review['all_load_bearing_checks_pass'] = (
        all(v['exists'] and (v['hash_match'] is not False) for v in file_checks.values())
        and review['sat_proof_status']['cadical_exit_is_unsat_20']
        and review['sat_proof_status']['drat_trim_exit_zero']
        and review['sat_proof_status']['drat_trim_verified']
        and review['small_formula_semantics']['uses_only_wang_rows_beyond_total_and_token_bounds']
        and not review['small_formula_semantics']['quotient_rank_or_contraction_rows_used']
        and review['reencoding']['hash_match']
        and review['symmetry_transport']['capacity_two_matches_expected']
        and review['symmetry_transport']['maps_each_capacity_two_point_to_1_all_present']
        and review['symmetry_transport']['selected_rows_preserve_L_under_all_stabilizer_perms']
        and review['symmetry_transport']['witness_maps_all_preimage_image_preserve_L']
        and all(review['scope_guard'].values())
    )
    review['review_conclusion'] = (
        'Accept the repeated projected-A exclusion for the E11 core over F2 as a settled reduction for subsequent work.'
        if review['all_load_bearing_checks_pass'] else
        'Do not rely on the certificate until failed checks are repaired.'
    )
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(review, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'out': str(OUT), 'all_load_bearing_checks_pass': review['all_load_bearing_checks_pass'], 'conclusion': review['review_conclusion']}, sort_keys=True))


if __name__ == '__main__':
    main()
