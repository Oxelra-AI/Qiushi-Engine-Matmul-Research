#!/usr/bin/env python3
"""analysis progress ledger for the Wang-F2 support-exclusion route.

This records two new certified facts from analysis:
  * matching stratum k=5 idx15 is closed by a fair seed solve with exact
    regeneration and DRAT replay;
  * the adjacent-pair rep2 marked subbranch with prefix [1,2,3] is closed by
    witness learning plus 80 promoted complete Wang rows, exact regeneration,
    disjoint auxiliary intervals, and DRAT replay.

Scope: these are A-support exclusions under Wang's F2 occupation inequalities.
They are not a tensor decomposition result and not a characteristic-zero lower
bound.
"""
from __future__ import annotations
import json
import pathlib
from typing import Optional

WS = pathlib.Path('workspace')


def read_json(path: pathlib.Path) -> Optional[dict]:
    if not path.exists():
        return None
    return json.loads(path.read_text())


def summarize_json(path: pathlib.Path) -> dict:
    d = read_json(path)
    out = {'path': str(path), 'exists': path.exists()}
    if not d:
        return out
    out.update({
        'status': d.get('status'),
        'summary_status': d.get('summary_status'),
        'branch': d.get('branch'),
        'idx': d.get('idx'),
        'k': d.get('k'),
        'fixed_prefix': d.get('fixed_prefix'),
        'target': d.get('target'),
        'survivor_count': d.get('survivor_count'),
    })
    # Common local proof/provenance fields.
    if 'cnf_check' in d:
        out['cnf_clauses'] = d['cnf_check'].get('cnf_clauses')
        out['cnf_variables'] = d['cnf_check'].get('cnf_variables')
        out['exact_sequence_match'] = d['cnf_check'].get('exact_sequence_match')
    if 'structure_check' in d:
        out['structure_ok'] = d['structure_check'].get('structure_ok')
    if 'learned_check' in d:
        out['learned_checked'] = d['learned_check'].get('learned_checked')
        out['learned_bad_count'] = d['learned_check'].get('learned_bad_count')
    if 'learned_meta' in d:
        out['learned_checked'] = d['learned_meta'].get('learned_records_checked')
        out['learned_distinct_row_keys'] = d['learned_meta'].get('learned_distinct_row_keys')
    if 'promotion_check' in d:
        out['promotion_count'] = d['promotion_check'].get('promotion_count')
        out['promotion_clause_count'] = d['promotion_check'].get('promotion_clause_count_regenerated')
        out['promotion_aux_intervals'] = d['promotion_check'].get('promotion_aux_interval_count')
        out['promotion_problem_count'] = d['promotion_check'].get('promotion_problem_count')
    if 'drat_trim' in d:
        out['drat_verified'] = d['drat_trim'].get('verified')
        out['drat_sha256'] = d.get('drat_sha256')
    if 'drat_replay' in d:
        out['drat_verified'] = None if d['drat_replay'] is None else d['drat_replay'].get('verified')
    if 'full_lut_violations' in d:
        out['full_lut_violation_count'] = d['full_lut_violations'].get('count')
        out['max_excess'] = d['full_lut_violations'].get('max_excess')
    if 'initial_solve' in d:
        out['initial_cadical_exit'] = d['initial_solve'].get('cadical_exit')
        out['initial_cadical_sec'] = d['initial_solve'].get('cadical_sec')
    if 'final_clauses' in d:
        out['final_clauses'] = d.get('final_clauses')
        out['final_variables'] = d.get('final_variables')
    return out


def load_strata() -> list[dict]:
    raw = json.loads((WS / 'data/matching_strata/anchored_matching_strata.json').read_text())
    strata = []
    idx = 0
    for k_str in sorted(raw['representatives_by_k'].keys(), key=int):
        for st in raw['representatives_by_k'][k_str]:
            strata.append({
                'idx': idx,
                'k': int(k_str),
                'canonical': [int(x) for x in st['canonical']],
                'orbit_size': st.get('orbit_image_count', st.get('enumerated_members', 0)),
            })
            idx += 1
    return strata


def main() -> None:
    strata = load_strata()
    closed = {
        **{i: {'method': 'k7_row_clique_or_graph_certificate',
               'evidence': 'workspace/data/graph_cert/k7_rerun/verification_k7_certified.json'} for i in range(32, 38)},
        **{i: {'method': 'k6_clique_cover_certificate',
               'evidence': 'workspace/data/graph_cert/k6_color_pilot/verification_k6_color_certs.json'} for i in [22, 23, 24, 28]},
        25: {'method': 'witness_subset_drat',
             'evidence': 'workspace/data/smoke/idx25/idx025/strict_verification.json'},
        12: {'method': 'witness_subset_drat',
             'evidence': 'workspace/data/matching/k5_batch/idx012/strict_verification.json'},
        13: {'method': 'fair_seed_solve_drat',
             'evidence': 'workspace/data/promotion/k5_idx13_model_lowres_3w5/seed_formula_verification_drat.json'},
        14: {'method': 'witness_subset_drat',
             'evidence': 'workspace/data/matching/k5_batch/idx014/strict_verification.json'},
        15: {'method': 'fair_seed_solve_drat_delivered',
             'evidence': 'workspace/data/fair_seed/k5_idx15_copy/summary.json'},
    }

    entries = {}
    for st in strata:
        e = dict(st)
        c = closed.get(st['idx'])
        e['closed'] = bool(c)
        e['closure'] = c
        entries[str(st['idx'])] = e

    by_k = {}
    for k in range(1, 8):
        group = [e for e in entries.values() if e['k'] == k]
        by_k[str(k)] = {
            'total': len(group),
            'closed': sum(1 for e in group if e['closed']),
            'open': sum(1 for e in group if not e['closed']),
            'closed_indices': [e['idx'] for e in group if e['closed']],
            'open_indices': [e['idx'] for e in group if not e['closed']],
        }

    fair_seed_paths = {
        'k1_idx00': WS / 'data/fair_seed/k1_idx00_copy/summary.json',
        'k2_idx01': WS / 'data/fair_seed/k2_idx01_regen/summary.json',
        'k4_idx05': WS / 'data/fair_seed/k4_idx05_copy/summary.json',
        'k4_idx06': WS / 'data/fair_seed/k4_idx06_regen/summary.json',
        'k5_idx15': WS / 'data/fair_seed/k5_idx15_copy/summary.json',
        'k5_idx16': WS / 'data/fair_seed/k5_idx16_regen/summary.json',
        'k6_idx27': WS / 'data/fair_seed/k6_idx27_regen/summary.json',
        'rep2_rep003_seed': WS / 'data/fair_seed/rep2_rep003_witness20/summary.json',
    }
    fair_seed = {label: summarize_json(path) for label, path in fair_seed_paths.items()}

    profile = read_json(WS / 'data/rep2_marked_profile/summary.json') or {'records': []}
    rep_records = profile.get('records', [])
    all_reps = [int(r['rep']) for r in rep_records]
    rep2_marked = {
        'coverage_semantics': 'After fixing adjacent pair [1,2], branching on one additional selected point by its Stab([1,2]) orbit covers rep2; each closed prefix [1,2,rep] excludes supports containing a point in that orbit.',
        'total_orbits': len(rep_records),
        'closed_reps': [3],
        'open_reps': [r for r in all_reps if r != 3],
        'closed_orbit_size_sum': sum(int(r['orbit_size']) for r in rep_records if int(r['rep']) == 3),
        'total_candidate_orbit_size_sum': sum(int(r['orbit_size']) for r in rep_records),
        'profile_summary': 'workspace/data/rep2_marked_profile/summary.json',
        'closed_prefix_1_2_3': {
            'seed_verification': summarize_json(WS / 'data/rep2_marked_witness/rep003/strict_verification.json'),
            'fair_seed': fair_seed['rep2_rep003_seed'],
            'promotion_summary': summarize_json(WS / 'data/rep2_rep003_promotion/lowres_12w8/summary.json'),
            'promotion_verification': summarize_json(WS / 'data/rep2_rep003_promotion/lowres_12w8/strict_verification.json'),
        },
        'nonclosing_comparison': {
            'cheap_selector_summary': summarize_json(WS / 'data/rep2_rep003_promotion/cheap_12w8/summary.json'),
        },
        'rep2_closed': False,
    }

    summary = {
        'schema': 'wang_f2_progress_v1',
        'matching_strata_total': len(entries),
        'matching_strata_closed': sum(1 for e in entries.values() if e['closed']),
        'matching_strata_open': sum(1 for e in entries.values() if not e['closed']),
        'by_k': by_k,
        'rep2_marked_orbits_closed': len(rep2_marked['closed_reps']),
        'rep2_marked_orbits_total': rep2_marked['total_orbits'],
        'rep2_closed': False,
        'r_f2_ge_21_proved': False,
        'scope': 'Fixed A-support exclusions under Wang F2 occupation rows. The remaining matching strata and rep2 marked orbits must still be closed before the finite-field rank-20 support route yields R_F2>=21.',
        'global_result_unchanged': 'No rank<=22 exact algorithm, no characteristic-zero rank-23 optimality proof, and no complete R_F2>=21 proof.',
    }

    out = {
        'summary': summary,
        'matching_strata': entries,
        'fair_seed_solves': fair_seed,
        'rep2_marked_branch': rep2_marked,
    }
    out_path = WS / 'data/progress/progress.json'
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')

    print(f"matching {summary['matching_strata_closed']}/{summary['matching_strata_total']} closed")
    for k in range(1, 8):
        info = by_k[str(k)]
        print(f"k={k}: {info['closed']}/{info['total']} closed; open={info['open_indices']}")
    print(f"rep2 marked: {summary['rep2_marked_orbits_closed']}/{summary['rep2_marked_orbits_total']} orbit branches closed; rep2_closed={summary['rep2_closed']}")
    print(f"saved {out_path}")


if __name__ == '__main__':
    main()
