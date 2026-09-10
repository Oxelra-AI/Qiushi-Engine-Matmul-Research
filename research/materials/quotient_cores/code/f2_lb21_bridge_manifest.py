#!/usr/bin/env python3
"""analysis dependency manifest for the E11-core route to an F2 rank-21 lower bound.

This script does not prove the missing distinct-core theorem.  It records and
checks the already verified proof objects that make the E11-core branch a global
rank-20 obstruction route:
  (A) no full length-20 decomposition can have all A-factors rank >= 2, by the
      existing rank-3 and rank-2/3 Wang-occupation DRAT certificates;
  (B) any full length-20 decomposition with a rank-one A-factor can be normalized
      to E11 and quotiented to a length-19 E11-core decomposition;
  (C) analysis has certified that such a core decomposition cannot repeat a
      projected A-direction, leaving only the distinct E11-core branch open.
"""
from __future__ import annotations
import hashlib, json, re
from pathlib import Path

ROOT = Path('research/research_record')
OUT = ROOT / 'workspace/data/review/f2_lb21_bridge_manifest.json'


def sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def read(path: Path) -> str:
    return path.read_text(errors='replace') if path.exists() else ''


def parse_trim(path: Path) -> dict:
    txt = read(path)
    m = re.search(r'parsing input formula with (\d+) variables and (\d+) clauses', txt)
    return {
        'path': str(path),
        'exists': path.exists(),
        'sha256': sha256(path),
        'verified': 's VERIFIED' in txt,
        'vars': int(m.group(1)) if m else None,
        'clauses': int(m.group(2)) if m else None,
        'verification_time_sec': float(re.search(r'verification time: ([0-9.]+) seconds', txt).group(1)) if re.search(r'verification time: ([0-9.]+) seconds', txt) else None,
    }


def parse_cadical_exit(path: Path) -> dict:
    txt = read(path)
    return {
        'path': str(path),
        'exists': path.exists(),
        'sha256': sha256(path),
        'contains_unsat': ('UNSATISFIABLE' in txt or '\ns UNSATISFIABLE' in txt or '\n20\n' in txt),
        'exit_line_20': bool(re.search(r'(^|\n)(s )?UNSATISFIABLE', txt)) or bool(re.search(r'(^|\n)20(\n|$)', txt)),
    }


def main():
    rank3_dir = ROOT / 'workspace/data/wang_capacity_cnf'
    rank2_dir = ROOT / 'workspace/data/wang_capacity_cnf_rank2'
    repeat_manifest_path = ROOT / 'workspace/data/repeat_branch_certificate/certificate_manifest.json'
    repeat_review_path = ROOT / 'workspace/data/review/repeated_certificate_review.json'

    rank3_meta = json.loads((rank3_dir / 't_s20_dim123_branch_rank3.meta.json').read_text())
    rank2_meta = json.loads((rank2_dir / 't_s20_dim123_branch_rank2.meta.json').read_text())
    rank2_status = json.loads((rank2_dir / 't_s20_dim123_branch_rank2.status.json').read_text())
    repeat_manifest = json.loads(repeat_manifest_path.read_text())
    repeat_review = json.loads(repeat_review_path.read_text())

    no_rank1 = {
        'rank3_only_branch': {
            'meaning': 'After excluding rank-1 and rank-2 A directions and fixing one rank-3 representative, no length-20 Wang-admissible A-support exists in this rank class.',
            'meta': rank3_meta,
            'cnf_sha256': sha256(rank3_dir / 't_s20_dim123_branch_rank3.cnf'),
            'drat_sha256': sha256(rank3_dir / 't_s20_dim123_branch_rank3.drat'),
            'cadical_log': parse_cadical_exit(rank3_dir / 't_s20_dim123_branch_rank3.cadical2.log'),
            'drat_trim': parse_trim(rank3_dir / 't_s20_dim123_branch_rank3.drat_trim.log'),
        },
        'rank2_or_rank3_no_rank1_branch': {
            'meaning': 'After excluding rank-1 A directions and fixing one rank-2 representative, no length-20 Wang-admissible A-support exists with rank-2/3 directions.',
            'meta': rank2_meta,
            'status': rank2_status,
            'cnf_sha256': sha256(rank2_dir / 't_s20_dim123_branch_rank2.cnf'),
            'drat_sha256': sha256(rank2_dir / 't_s20_dim123_branch_rank2.drat'),
            'cadical_log': parse_cadical_exit(rank2_dir / 't_s20_dim123_branch_rank2.cadical.log'),
            'drat_trim': parse_trim(rank2_dir / 't_s20_dim123_branch_rank2.drat_trim.log'),
        },
    }

    checks = {
        'rank3_drat_verified': no_rank1['rank3_only_branch']['drat_trim']['verified'],
        'rank2_drat_verified': no_rank1['rank2_or_rank3_no_rank1_branch']['drat_trim']['verified'],
        'rank3_branch_rank': rank3_meta.get('branch_rank'),
        'rank2_branch_rank': rank2_meta.get('branch_rank'),
        'rank3_fixed_point': rank3_meta.get('fixed_point'),
        'rank2_fixed_point': rank2_meta.get('fixed_point'),
        'repeat_certificate_review_passed': bool(repeat_review.get('all_load_bearing_checks_pass')),
        'repeat_certificate_statement': repeat_manifest.get('mathematical_statement'),
    }
    checks['all_existing_dependencies_checked'] = (
        checks['rank3_drat_verified'] and checks['rank2_drat_verified'] and checks['repeat_certificate_review_passed']
        and rank3_meta.get('rank_s') == 20 and rank2_meta.get('rank_s') == 20
        and rank3_meta.get('allowed_rank_hist') == {'3': 168}
        and rank2_meta.get('allowed_rank_hist') == {'2': 294, '3': 168}
    )

    manifest = {
        'schema': 'f2_lb21_bridge_manifest_v1',
        'field': 'F2',
        'tensor': 'T_<3,3,3>',
        'purpose': 'Record the exact remaining dependency for proving R_F2(T)>=21 via the E11 core.',
        'already_checked_dependencies': {
            'no_rank1_full_support_certificates': no_rank1,
            'repeated_projected_A_E11_certificate': {
                'manifest': str(repeat_manifest_path),
                'review': str(repeat_review_path),
                'primary_cnf_sha256': repeat_manifest['primary_certificate']['files']['cnf']['sha256'],
                'primary_drat_sha256': repeat_manifest['primary_certificate']['files']['drat']['sha256'],
                'primary_drat_trim_verified': repeat_manifest['primary_certificate']['drat_trim_verified'],
            },
        },
        'logical_bridge': [
            'Any length-20 full decomposition over F2 has nonzero A-factors whose projective A-support satisfies Wang occupation constraints.',
            'The rank-3-only and rank-2/3 no-rank1 DRAT certificates exclude all length-20 Wang-admissible A-supports with no rank-one A-factor; hence a hypothetical length-20 full decomposition has a rank-one A-factor.',
            'The standard matrix-multiplication tensor action is transitive on rank-one A directions, so choose coordinates with that factor at E11.',
            'The one-dimensional Wang rows have capacity one at length 20, so there is no second E11 A-factor; quotienting by <E11> leaves exactly 19 nonzero projected A-factors for the E11 core.',
            'analysis excludes repeated projected A-directions in any length-19 E11-core support satisfying complete Wang occupation, so only the distinct projected-A E11-core branch remains.',
            'A proof excluding that distinct branch would prove R_F2(T_<3,3,3>) >= 21.  A rank-19 E11-core decomposition would instead lift to a full rank <=22 decomposition by adding the three rank-one terms for the deleted E11 slice.',
        ],
        'missing_dependency': {
            'name': 'distinct_projected_A_E11_core_length19_resolution',
            'needed_for_lower_bound': 'Show that no 19-element subset of nonzero E11 quotient directions satisfies the complete core Wang table and fixed-A consequences strongly enough to be an exact E11-core decomposition; a Wang-only UNSAT proof would be enough, but a B/C compatibility proof may be needed.',
            'needed_for_upper_bound': 'If such a 19-point support is found, solve exact B/C rank-one completion and verify the E11-core tensor identity; then add the deleted E11 slice terms to obtain a full rank <=22 decomposition over F2.',
        },
        'checks': checks,
        'scope_limits': [
            'This manifest is not a proof of R_F2(T)>=21 because the distinct E11-core branch is still open.',
            'Even a future F2 rank>=21 lower bound would not prove characteristic-zero rank 23 optimality.',
            'The repeated-branch proof is Wang-only; quotient-rank cuts are not evidence for that particular contradiction, though they remain useful for the distinct branch and candidate completion.',
        ],
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'out': str(OUT), 'all_existing_dependencies_checked': checks['all_existing_dependencies_checked'], 'missing': manifest['missing_dependency']['name']}, sort_keys=True))


if __name__ == '__main__':
    main()
