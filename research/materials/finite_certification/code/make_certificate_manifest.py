#!/usr/bin/env python3
"""Assemble analysis repeated-direction E11-core proof manifest."""
from __future__ import annotations
import hashlib, json
from pathlib import Path

ROOT = Path('research/research_record')
BASE = ROOT / 'workspace/data/repeat_branch_certificate'

def sha256(path: Path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(4*1024*1024), b''):
            h.update(chunk)
    return h.hexdigest()

def info(path: Path):
    return {'path': str(path), 'exists': path.exists(), 'size': path.stat().st_size if path.exists() else None, 'sha256': sha256(path) if path.exists() and path.is_file() else None}

sym = json.loads((BASE/'induced_core_symmetry.json').read_text())
transport = json.loads((BASE/'symmetry_row_transport_check.json').read_text())
small_meta = json.loads((BASE/'iis_shrink_p1/fixed_repeat_p1_iis.meta.json').read_text())
small_status = json.loads((BASE/'iis_shrink_p1/drat/fixed_repeat_p1_iis.status.json').read_text())
large_meta = json.loads((BASE/'fixed_repeat_p1.meta.json').read_text())
large_status = json.loads((BASE/'drat_p1/fixed_repeat_p1.status.json').read_text())
reenc = json.loads((BASE/'iis_shrink_p1/reencode_check/reencode_verify.json').read_text())
expansion = json.loads((BASE/'cnf_expansion_assessment.json').read_text())
manifest = {
    'schema': 'repeated_e11_core_certificate_manifest_v1',
    'field': 'F2',
    'tensor_object': 'E11 codimension-one quotient core of T_<3,3,3>',
    'rank_length': 19,
    'mathematical_statement': (
        'There is no length-19 nonzero projected A-direction multiset for the E11 core over F2 '
        'that satisfies the complete Wang occupation consequences and contains a repeated projected direction. '
        'Equivalently, any actual rank-19 E11-core decomposition over F2 must have 19 distinct projected A-directions.'
    ),
    'scope_limits': [
        'Does not exclude the distinct projected-A branch.',
        'Does not prove E11-core rank >=20 over F2.',
        'Does not construct a rank<=22 algorithm.',
        'Does not prove rank 23 optimality for T_<3,3,3> over characteristic zero or any general field.'
    ],
    'capacity_distribution': {'1': 249, '2': 6},
    'capacity_two_points': sym['capacity_two_points'],
    'capacity_two_labels': sym['capacity_two_labels'],
    'symmetry_summary': {
        'standard_GL3xGL3_transpose_action_count': sym['full_T_action_count'],
        'E11_stabilizer_count': sym['T_stabilizer_count_fixing_pivot'],
        'no_transpose_orbits': sym['no_transpose_orbits_on_capacity_two'],
        'full_orbits': sym['full_stabilizer_orbits_on_capacity_two'],
        'transpose_exchanges_rulings': sym['transpose_exchanges_rulings'],
        'row_transport_preserves_selected_L_values': transport['all_selected_rows_preserve_L_under_all_stabilizer_perms'],
        'row_transport_checked_pairs': transport['transported_dim_counter_total'],
    },
    'primary_certificate': {
        'description': 'Small Wang-only fixed representative p=1 (E12) CNF/DRAT certificate plus symmetry transport.',
        'fixed_repeat_point': small_meta['fixed_repeat_point'],
        'fixed_repeat_label': small_meta['fixed_repeat_label'],
        'fixed_copies': 2,
        'constraints': {
            'selected_wang_rows': small_meta['core_constraint_count'],
            'selected_wang_rows_by_dim': transport['selected_rows_by_dim'],
            'selected_wang_rows_by_L': transport['selected_rows_by_L'],
            'hard_total_length': 19,
            'one_dimensional_capacities_encoded_as_tokens': True,
            'contraction_lower_bounds_used': 0,
            'quotient_rank_cuts_used': 0,
        },
        'cnf_variables': small_meta['cnf_variables'],
        'cnf_clauses': small_meta['cnf_clauses'],
        'cadical_exit': small_status['cadical_exit'],
        'cadical_elapsed_sec': small_status['cadical_elapsed_sec'],
        'drat_trim_verified': small_status['drat_trim_log_parse']['verified'],
        'drat_trim_elapsed_sec': small_status['drat_trim_elapsed_sec'],
        'files': {
            'cnf': info(Path(small_status['cnf'])),
            'meta': info(Path(small_status['meta'])),
            'drat': info(Path(small_status['drat'])),
            'cadical_log': info(Path(small_status['cadical_log'])),
            'drat_trim_log': info(Path(small_status['drat_trim_log'])),
            'shrink_summary': info(BASE/'iis_shrink_p1/shrink_summary.json'),
            'reencode_verify': info(BASE/'iis_shrink_p1/reencode_check/reencode_verify.json'),
        },
        'deterministic_reencode_hash_match': reenc['hash_match'],
    },
    'larger_crosscheck_certificate': {
        'description': 'Full compact fixed p=1 CNF using 12165 Wang rows, contractions, and unconditional quotient-rank cuts.',
        'cnf_variables': large_meta['cnf_summary']['variables'],
        'cnf_clauses': large_meta['cnf_summary']['clauses'],
        'cadical_exit': large_status['cadical_exit'],
        'drat_trim_verified': large_status['drat_trim_log_parse']['verified'],
        'files': {
            'cnf': info(Path(large_status['cnf'])),
            'meta': info(Path(large_status['meta'])),
            'drat': info(Path(large_status['drat'])),
            'drat_trim_log': info(Path(large_status['drat_trim_log'])),
        }
    },
    'full_table_sat_expansion_assessment': {
        'path': str(BASE/'cnf_expansion_assessment.json'),
        'sequential_counter_scenarios': [
            {'name': s['name'], 'wang_rows': s['wang_rows'], 'estimated_wang_clauses': s['estimated_wang_clauses'], 'estimated_wang_aux_variables': s['estimated_wang_aux_variables_if_expanded_independently']}
            for s in expansion['scenarios']
        ]
    },
    'supporting_records': {
        'symmetry': str(BASE/'induced_core_symmetry.json'),
        'row_transport': str(BASE/'symmetry_row_transport_check.json'),
        'milp_all_six_crosscheck': str(BASE/'fixed_repeat_milp_replay.json'),
        'verification_review': 'independent-verification-record',
            'explanatory_note': str(ROOT/'workspace/notes/repeated_core_certificate.md'),
    }
}
out = BASE / 'certificate_manifest.json'
out.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
print(json.dumps({'out': str(out), 'primary_verified': manifest['primary_certificate']['drat_trim_verified'], 'reencode_match': reenc['hash_match'], 'statement': manifest['mathematical_statement']}, sort_keys=True))
