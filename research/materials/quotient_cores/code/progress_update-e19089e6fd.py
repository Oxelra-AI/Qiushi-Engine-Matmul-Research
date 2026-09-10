#!/usr/bin/env python3
"""Update the Wang-F2 matching progress ledger with cross-ARTIFACT verified closures.

The older analysis progress script only knew analysis graph certificates and analysis
run directories.  This analysis ledger additionally records the analysis fair
seed-solve closure for k=5 idx13 and is intentionally evidence-facing: every
closed item points to a verification artifact or certificate directory.
"""
from __future__ import annotations
import json
import pathlib
from typing import Dict, Optional

WS = pathlib.Path('workspace')

def read_json(path: pathlib.Path) -> Optional[dict]:
    if not path.exists():
        return None
    return json.loads(path.read_text())


def check_witness_run(path: pathlib.Path) -> dict:
    out = {'path': str(path), 'exists': path.exists()}
    s = read_json(path / 'summary.json')
    if s:
        out.update({
            'status': s.get('status'),
            'rounds': s.get('rounds'),
            'final_clauses': s.get('final_clauses'),
            'learned_clause_count': s.get('learned_clause_count'),
            'target': s.get('target'),
            'survivor_count': s.get('survivor_count'),
            'drat_verified_in_summary': s.get('drat_trim', {}).get('verified'),
        })
    sv = read_json(path / 'strict_verification.json')
    if sv:
        out.update({
            'strict_verification': str(path / 'strict_verification.json'),
            'strict_verified': sv.get('status') == 'verified',
            'structure_ok': sv.get('structure_check', {}).get('structure_ok'),
            'exact_sequence_match': sv.get('cnf_check', {}).get('exact_sequence_match'),
            'drat_verified': sv.get('drat_replay', {}).get('verified') if 'drat_replay' in sv else sv.get('drat_check', {}).get('verified'),
        })
    return out


def check_seed_verification(path: pathlib.Path) -> dict:
    sv = read_json(path)
    out = {'verification': str(path), 'exists': path.exists()}
    if sv:
        out.update({
            'status': sv.get('status'),
            'strict_verified': sv.get('status') == 'verified',
            'structure_ok': sv.get('structure_check', {}).get('structure_ok'),
            'exact_sequence_match': sv.get('cnf_check', {}).get('exact_sequence_match'),
            'drat_verified': sv.get('drat_replay', {}).get('verified'),
            'cnf_clauses': sv.get('cnf_check', {}).get('cnf_clauses'),
            'learned_checked': sv.get('learned_check', {}).get('learned_checked'),
        })
    return out


def main() -> None:
    raw = json.loads((WS / 'data/matching_strata/anchored_matching_strata.json').read_text())
    strata = []
    idx = 0
    for k_str in sorted(raw['representatives_by_k'].keys(), key=int):
        for st in raw['representatives_by_k'][k_str]:
            strata.append({
                'idx': idx,
                'k': int(k_str),
                'canonical': st['canonical'],
                'orbit_size': st.get('orbit_image_count', st.get('enumerated_members', 0)),
            })
            idx += 1

    closed_sources: Dict[int, dict] = {}
    # analysis k=7 graph/direct/clique/DRAT certificates.
    for i in range(32, 38):
        closed_sources[i] = {
            'method': 'k7_graph_or_row_certificate',
            'verification': 'workspace/data/graph_cert/k7_rerun/verification_k7_certified.json',
            'manifest': 'workspace/data/k7_manifest/k7_unified_manifest.json',
            'strict_graph_cnf_verification': 'workspace/data/graph_cert/k7_graph_is_cnf_with_vex/strict_verification_graph_is_cnf.json',
        }
    # analysis k=6 clique-cover/graph certificates plus analysis smoke idx25.
    for i in [22, 23, 24, 28]:
        closed_sources[i] = {
            'method': 'k6_clique_cover_certificate',
            'verification': 'workspace/data/graph_cert/k6_color_pilot/verification_k6_color_certs.json',
        }
    closed_sources[25] = {
        'method': 'witness_subset_drat',
        'run': 'workspace/data/smoke/idx25/idx025',
        'verification': 'workspace/data/smoke/idx25/idx025/strict_verification.json',
    }
    # analysis k=5 closures.
    closed_sources[12] = {
        'method': 'witness_subset_drat',
        'run': 'workspace/data/matching/k5_batch/idx012',
        'verification': 'workspace/data/matching/k5_batch/idx012/strict_verification.json',
    }
    closed_sources[14] = {
        'method': 'witness_subset_drat',
        'run': 'workspace/data/matching/k5_batch/idx014',
        'verification': 'workspace/data/matching/k5_batch/idx014/strict_verification.json',
    }
    closed_sources[13] = {
        'method': 'fair_seed_solve_drat',
        'seed_run': 'workspace/data/matching/k5_batch/idx013',
        'verification': 'workspace/data/promotion/k5_idx13_model_lowres_3w5/seed_formula_verification_drat.json',
    }

    # Known nonclosed run evidence.
    run_dirs = {
        0: WS / 'data/matching/k123_batch/idx000',
        1: WS / 'data/matching/k123_batch/idx001',
        5: WS / 'data/matching/k4_batch/idx005',
        15: WS / 'data/matching/k5_batch/idx015',
        26: WS / 'data/matching/k6_batch/idx026',
    }

    entries = {}
    for st in strata:
        idx = st['idx']
        e = dict(st)
        if idx in closed_sources:
            e['closed'] = True
            e['closure'] = closed_sources[idx]
        else:
            e['closed'] = False
            e['closure'] = None
        if idx in run_dirs:
            e['latest_run'] = check_witness_run(run_dirs[idx])
        entries[str(idx)] = e

    by_k = {}
    for k in range(1, 8):
        ks = [e for e in entries.values() if e['k'] == k]
        by_k[str(k)] = {
            'total': len(ks),
            'closed': sum(1 for e in ks if e['closed']),
            'open': sum(1 for e in ks if not e['closed']),
            'open_indices': [e['idx'] for e in ks if not e['closed']],
        }

    rep2 = {
        'branch': 'rep2_adjacent_pair',
        'closed': False,
        'status': 'OPEN',
        'latest_run': check_witness_run(WS / 'data/matching/rep2_production/rep2'),
        'seeded_promotion_runs': [
            'workspace/data/promotion/rep2_model_lowres_3w5/summary.json',
            'workspace/data/promotion/rep2_model_excess_3w5/summary.json',
            'workspace/data/promotion/rep2_model_lowres_8w5/summary.json',
            'workspace/data/promotion/rep2_prod_lowres_5w8/summary.json',
        ],
        'interpretation': 'Returned violation counts are candidate diagnostics only, not monotone proof-progress measures.',
    }

    summary = {
        'schema': 'matching_progress_v1',
        'matching_strata_total': len(entries),
        'matching_strata_closed': sum(1 for e in entries.values() if e['closed']),
        'matching_strata_open': sum(1 for e in entries.values() if not e['closed']),
        'by_k': by_k,
        'rep2_closed': rep2['closed'],
        'all_closed_for_r_f2_ge_21': False,
        'scope': 'fixed A-support exclusions under the Wang F2 occupation LUT; not a tensor-rank lower bound unless all matching strata and rep2 are closed and external proof layers are bound.',
    }
    output = {'summary': summary, 'matching_strata': entries, 'rep2': rep2}
    out_path = WS / 'data/progress/progress.json'
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(output, indent=2, sort_keys=True) + '\n')

    print(f"Matching strata: {summary['matching_strata_closed']}/{summary['matching_strata_total']} closed")
    for k in range(1, 8):
        info = by_k[str(k)]
        print(f"  k={k}: {info['closed']}/{info['total']} closed; open={info['open_indices']}")
    print(f"Rep2: {rep2['status']}")
    print(f"R_F2 >= 21: {'YES' if summary['all_closed_for_r_f2_ge_21'] else 'NOT YET'}")
    print(f"Saved {out_path}")


if __name__ == '__main__':
    main()
