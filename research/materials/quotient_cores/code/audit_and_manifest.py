#!/usr/bin/env python3
"""Audit analysis hierarchy outputs and write a coverage/proof-target manifest.

The scientific purpose is to prevent proof drift: CP-SAT singleton/pair exclusions
may guide a branch split, but proof-producing reductions must either certify the
eliminated cases or keep the original branch variables.  This script records which
files are only CP-SAT evidence, which surveys had survivor bookkeeping issues, and
which branch/k levels still need formal proof objects.
"""
from __future__ import annotations

import json
from pathlib import Path
from collections import Counter

ROOT = Path('research/research_record')
DATA24 = ROOT / 'workspace/data/singleton_survey'
DATA25 = ROOT / 'workspace/data/coverage'


def read_json(path: Path):
    if not path.exists() or path.stat().st_size == 0:
        return None
    return json.loads(path.read_text())


def classify_phase1(payload: dict):
    true = {'INFEASIBLE': [], 'FEASIBLE_OR_OPTIMAL': [], 'UNKNOWN_OR_OTHER': []}
    for r in payload.get('phase1_results', []):
        st = r.get('status')
        rep = int(r.get('orbit_rep'))
        if st == 'INFEASIBLE':
            true['INFEASIBLE'].append(rep)
        elif st in ('OPTIMAL', 'FEASIBLE'):
            true['FEASIBLE_OR_OPTIMAL'].append(rep)
        else:
            true['UNKNOWN_OR_OTHER'].append(rep)
    for k in true:
        true[k].sort()
    ph = payload.get('phase1_summary') or payload.get('singleton_summary') or {}
    recorded = {
        'infeasible_reps': sorted(int(x) for x in ph.get('infeasible_reps', [])),
        'feasible_reps': sorted(int(x) for x in ph.get('feasible_reps', [])),
        'unknown_reps': sorted(int(x) for x in ph.get('unknown_reps', [])),
        'survivor_reps': sorted(int(x) for x in (ph.get('surviving_reps') or ph.get('survivor_reps') or [])),
    }
    computed_survivors = sorted(true['FEASIBLE_OR_OPTIMAL'] + true['UNKNOWN_OR_OTHER'])
    return {
        'true_from_rows': true,
        'recorded_summary': recorded,
        'computed_survivors_feasible_plus_unknown': computed_survivors,
        'infeasible_mismatch': recorded['infeasible_reps'] != true['INFEASIBLE'],
        'feasible_mismatch_ignoring_unknowns': recorded['feasible_reps'] != true['FEASIBLE_OR_OPTIMAL'],
        'has_explicit_survivors': bool(recorded['survivor_reps']),
    }


def pair_summary(path: Path):
    d = read_json(path)
    if d is None:
        return {'path': str(path), 'exists_nonempty': False}
    statuses = Counter(r.get('status') for r in d.get('pair_results', []))
    return {
        'path': str(path),
        'exists_nonempty': True,
        'branch_rep': d.get('branch_rep'),
        'k': d.get('k'),
        'canonical_pair_count': d.get('canonical_pair_count'),
        'all_pairs_infeasible': d.get('all_pairs_infeasible'),
        'status_hist': dict(sorted(statuses.items())),
        'elapsed_sec': d.get('elapsed_sec'),
    }


def main():
    DATA25.mkdir(parents=True, exist_ok=True)
    audits = {}
    for name in ['rep2_singleton_only.json', 'rep2_k17_survivors.json',
                 'rep16_singleton_only.json', 'rep16_k16_survivors.json',
                 'rep10_k17_survey.json']:
        p = DATA24 / name
        d = read_json(p)
        if d is None:
            audits[name] = {'path': str(p), 'exists_nonempty': False}
            continue
        entry = {'path': str(p), 'exists_nonempty': True}
        if 'phase1_results' in d:
            entry.update(classify_phase1(d))
        if 'singleton_results' in d:
            statuses = Counter(r.get('status') for r in d.get('singleton_results', []))
            entry['singleton_status_hist'] = dict(sorted(statuses.items()))
            entry['singleton_summary_recorded'] = d.get('singleton_summary')
        audits[name] = entry

    corrected_rep2_k17 = None
    d = read_json(DATA24 / 'rep2_singleton_only.json')
    if d:
        c = classify_phase1(d)
        corrected_rep2_k17 = dict(d)
        corrected_rep2_k17['phase1_summary'] = {
            'infeasible_reps': c['true_from_rows']['INFEASIBLE'],
            'feasible_reps': c['true_from_rows']['FEASIBLE_OR_OPTIMAL'],
            'unknown_reps': c['true_from_rows']['UNKNOWN_OR_OTHER'],
            'surviving_reps': c['computed_survivors_feasible_plus_unknown'],
            'meaning': 'Corrected analysis bookkeeping: UNKNOWN orbits remain in survivors; only INFEASIBLE orbits are eliminated.'
        }
        out = DATA25 / 'rep2_k17_survivors_corrected.json'
        out.write_text(json.dumps(corrected_rep2_k17, indent=2, sort_keys=True) + '\n')

    manifest = {
        'problem': 'analysis Wang fixed-E11 branch coverage and proof-target manifest',
        'field': 'F2',
        'rank_s': 20,
        'status_statement': 'No new lower bound is proved here.  The verified global finite-field bound remains R_F2 >= 20.  CP-SAT infeasibility guides proof targets only.',
        'branch_split': {
            'fixed_rank1_point': 'E11 mask 1 after the DRAT-verified no-rank1 branch',
            'second_point_orbits': [2, 10, 16, 17, 20, 84, 160, 161],
            'already_DRAT_closed_second_reps': [17, 20, 84, 160, 161],
            'open_second_reps_for_current_work': [2, 10, 16],
            'rank1_count_k': 'total number of rank-1 A-side projective directions in a length-20 support',
            'rep2_rep16_k_range': 'k=2..17 remain after exact-k=18 closure; the second point is rank 1 so k>=2',
            'rep10_k_range': 'k=1..17 remain after exact-k=18 closure; the second point is rank 2 so k=1 must be handled separately',
        },
        'script_repairs_this_step': {
            'singleton_hr_feasibility_survey.py': 'patched to classify UNKNOWN separately and list survivors = feasible + unknown',
            'general_singleton_pair_survey.py': 'patched so UNKNOWN singleton orbits remain in the pair survivor set',
            'exhaustive_canonical_pairs.py': 'patched to prefer explicit surviving/survivor reps or feasible+unknown, not only FEASIBLE',
            'pair_and_triple_survey.py': 'same survivor handling patch',
            'rep10_exactk_row_core_cp.py': 'new row-core extractor with exact rank-1 count and original branch variables',
            'fixed_branch_rowcore_cnf.py': 'new CNF replay wrapper for explicit row-core keys without CP-SAT variable removal',
        },
        'audits': audits,
        'pair_level_evidence': {
            'rep16_k17': pair_summary(DATA24 / 'rep16_k17_exhaustive_pairs.json'),
            'rep16_k16': pair_summary(DATA24 / 'rep16_k16_exhaustive_pairs.json'),
            'rep2_k17_pending_file': pair_summary(DATA24 / 'rep2_k17_exhaustive_pairs.json'),
        },
        'rep10_k1_new_evidence': {
            'small_family_probe': 'data/rep10_k1/rep10_exact_k1_dim1_through46_no_rank1proj.json',
            'small_family_result': 'CP-SAT INFEASIBLE using dim1 plus through-fixed dim4,6 Wang rows, exact k=1, no rank-1 projection, 14478 rows, 30.4 s solve',
            'fullthrough_probe': 'data/rep10_k1/rep10_exact_k1_fullthroughE11_dim123_t48_rank1proj.json',
            'fullthrough_result': 'CP-SAT INFEASIBLE using 1,234,292 Wang rows plus 38,756 rank-1 projected rows, 282.5 s solve',
            'proof_status': 'not proof-checked; exact-k=1 CNF/DRAT proof task submitted separately',
        },
        'certification_principle': {
            'invalid_shortcut': 'A CNF over only surviving variables certifies only the conditional reduced problem unless eliminated singleton/pair cases are separately certified.',
            'acceptable_options': [
                'certify each singleton and pair exclusion used by a survivor reduction, including all orbit images or a checked orbit-lifting argument',
                'build a full original-branch CNF for the exact k level with all branch variables and enough Wang rows to be UNSAT',
                'build a CNF from an explicit row-core that was extracted from the full original-branch formula, keeping all branch variables and exact k'
            ],
        },
        'running_or_unresolved_tasks_known_at_manifest_time': [
            's24_t20_tool1 rep2 k=17 exhaustive canonical pairs',
            's24_t30_tool1 rep10 full k-descent k=16..2',
            's25_t11_tool2 rep16 k=15 exhaustive pairs with max-pairs 5000',
            's25_t21_tool1 rep10 exact k=1 CNF/DRAT proof attempt',
            's25_t25_tool1 rep10 k=1 row-core shrink',
            's25_t25_tool2 rep10 k=17 row-core shrink'
        ],
        'meaning': 'This manifest is an execution control object for the finite-field Wang route.  It records sound coverage requirements and prevents CP-SAT hierarchy results from being mistaken for certified lower-bound proofs.',
    }
    out = DATA25 / 'coverage_and_proof_targets.json'
    out.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'manifest': str(out),
        'corrected_rep2_k17': None if corrected_rep2_k17 is None else str(DATA25 / 'rep2_k17_survivors_corrected.json'),
        'audited_files': len(audits),
        'rep2_singleton_true': audits.get('rep2_singleton_only.json', {}).get('true_from_rows'),
        'rep2_survivor_infeasible_mismatch': audits.get('rep2_k17_survivors.json', {}).get('infeasible_mismatch'),
        'rep16_k16_pair_summary': manifest['pair_level_evidence']['rep16_k16'],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
