#!/usr/bin/env python3
"""Track progress across all matching strata and rep2 for the R_F2 >= 21 proof chain.

Reads:
  - analysis anchored matching strata classification
  - analysis graph certificates (k=7, k=6 clique-cover)
  - analysis iterative-separation outputs
  - analysis rep2 output

Produces a unified status JSON.
"""
import json
import pathlib
import sys
from typing import Dict, Optional

def check_dir(path: pathlib.Path) -> Optional[dict]:
    """Read a stratum run directory and return status."""
    summary = path / 'summary.json'
    if not summary.exists():
        return None
    data = json.loads(summary.read_text())
    status = data.get('status', 'UNKNOWN')
    result = {
        'status': status,
        'rounds': data.get('rounds'),
        'learned_clause_count': data.get('learned_clause_count'),
        'final_clauses': data.get('final_clauses'),
        'survivor_count': data.get('survivor_count'),
        'target': data.get('target'),
    }
    if status == 'UNSAT':
        result['drat_verified'] = bool(data.get('drat_trim', {}).get('verified', False))
        result['final_cnf'] = data.get('final_cnf')
    elif status in ('MAX_ROUNDS', 'NO_NEW_CLAUSES'):
        result['current_cnf'] = data.get('current_cnf')
    # Check strict verification
    strict = path / 'strict_verification.json'
    if strict.exists():
        sv = json.loads(strict.read_text())
        result['strict_verified'] = sv.get('status') == 'verified'
        result['structure_ok'] = sv.get('structure_check', {}).get('structure_ok')
    return result

def main():
    ws = pathlib.Path('workspace')
    
    # Load strata classification
    strata_file = ws / 'data/matching_strata/anchored_matching_strata.json'
    raw = json.loads(strata_file.read_text())
    reps_by_k = raw['representatives_by_k']
    
    # Build flat index
    strata = []
    idx = 0
    for k_str in sorted(reps_by_k.keys(), key=int):
        for st in reps_by_k[k_str]:
            strata.append({
                'idx': idx,
                'k': int(k_str),
                'canonical': st['canonical'],
                'orbit_size': st.get('orbit_image_count', st.get('enumerated_members', 0)),
            })
            idx += 1
    
    # k=7 strata (idx 32-37): closed by analysis graph certificates
    k7_cert_dir = ws / 'data/graph_cert/k7_rerun'
    k7_manifest = ws / 'data/k7_manifest/k7_unified_manifest.json'
    
    # k=6 clique-cover strata: idx 22,23,24,28
    k6_clique_dir = ws / 'data/graph_cert/k6_color_pilot'
    
    results = {}
    
    for st in strata:
        idx = st['idx']
        k = st['k']
        entry = dict(st)
        
        if k == 7:
            # Closed by analysis
            entry['proof_method'] = 'graph_certificate'
            entry['closed'] = True
            entry['source_dir'] = str(k7_cert_dir)
        elif k == 6 and idx in [22, 23, 24, 28]:
            # Closed by analysis clique-cover
            entry['proof_method'] = 'clique_cover_certificate'
            entry['closed'] = True
            entry['source_dir'] = str(k6_clique_dir)
        else:
            # Check analysis iterative separation results
            entry['closed'] = False
            entry['proof_method'] = None
            
            # Check various possible output directories
            for batch_name, subdir_fmt in [
                ('smoke/idx25', f'idx{idx:03d}'),
                ('matching/k6_batch', f'idx{idx:03d}'),
                ('matching/k5_batch', f'idx{idx:03d}'),
                ('matching/k4_batch', f'idx{idx:03d}'),
                ('matching/k123_batch', f'idx{idx:03d}'),
            ]:
                run_dir = ws / 'data' / batch_name / subdir_fmt
                info = check_dir(run_dir)
                if info is not None:
                    entry['separation_result'] = info
                    entry['source_dir'] = str(run_dir)
                    if info['status'] == 'UNSAT' and info.get('drat_verified'):
                        entry['closed'] = True
                        entry['proof_method'] = 'iterative_separation_drat'
                    break
        
        results[str(idx)] = entry
    
    # Rep2 branch
    rep2_entry = {
        'branch': 'rep2_adjacent_pair',
        'prefix': [1, 2],
        'target': 18,
        'survivor_count': 509,
        'closed': False,
        'proof_method': None,
    }
    for batch_name in ['matching/rep2_production/rep2',
                       'witness_subset/rep2_seeded_12r/rep2',
                       'witness_subset/rep2_pilot/rep2']:
        run_dir = ws / 'data' / batch_name
        info = check_dir(run_dir)
        if info is not None:
            rep2_entry['separation_result'] = info
            rep2_entry['source_dir'] = str(run_dir)
            if info['status'] == 'UNSAT' and info.get('drat_verified'):
                rep2_entry['closed'] = True
                rep2_entry['proof_method'] = 'iterative_separation_drat'
            break
    
    # Summary
    matching_closed = sum(1 for r in results.values() if r['closed'])
    matching_total = len(results)
    
    summary = {
        'schema': 'matching_progress_v1',
        'matching_strata_total': matching_total,
        'matching_strata_closed': matching_closed,
        'matching_strata_open': matching_total - matching_closed,
        'rep2_closed': rep2_entry['closed'],
        'all_closed_for_r_f2_ge_21': matching_closed == matching_total and rep2_entry['closed'],
        'by_k': {},
    }
    
    for k in range(1, 8):
        k_items = [r for r in results.values() if r['k'] == k]
        k_closed = sum(1 for r in k_items if r['closed'])
        summary['by_k'][str(k)] = {
            'total': len(k_items),
            'closed': k_closed,
            'open': len(k_items) - k_closed,
        }
    
    output = {
        'summary': summary,
        'matching_strata': results,
        'rep2': rep2_entry,
    }
    
    out_path = ws / 'data/matching/progress.json'
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(output, indent=2, sort_keys=True) + '\n')
    
    # Print compact status
    print(f"Matching strata: {matching_closed}/{matching_total} closed")
    for k in range(1, 8):
        info = summary['by_k'][str(k)]
        print(f"  k={k}: {info['closed']}/{info['total']}")
    print(f"Rep2: {'CLOSED' if rep2_entry['closed'] else 'OPEN'}")
    if rep2_entry.get('separation_result'):
        sr = rep2_entry['separation_result']
        print(f"  Status: {sr['status']}, rounds: {sr.get('rounds')}, clauses: {sr.get('final_clauses') or sr.get('learned_clause_count')}")
    print(f"\nR_F2 >= 21: {'YES' if summary['all_closed_for_r_f2_ge_21'] else 'NOT YET'}")
    
    # List open strata
    open_strata = [r for r in results.values() if not r['closed']]
    if open_strata:
        print(f"\nOpen strata ({len(open_strata)}):")
        for r in sorted(open_strata, key=lambda x: x['idx']):
            sr = r.get('separation_result', {})
            status = sr.get('status', 'NOT_STARTED')
            print(f"  idx={r['idx']:2d} k={r['k']} orbit={r['orbit_size']} status={status}")
    
    print(f"\nSaved {out_path}")

if __name__ == '__main__':
    main()
