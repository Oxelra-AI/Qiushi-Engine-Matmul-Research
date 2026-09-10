#!/usr/bin/env python3
"""analysis: Complete branch closure suite with full provenance.

Runs ALL branches for both rank-2 and rank-3 quotients using the
full merged constraint binaries. Records provenance for every closure.
"""
import json, subprocess, time, hashlib
from pathlib import Path

ROOT = Path('research/research_record')
DFS = str(ROOT / 'workspace/scripts/pair_prop_dfs')
OUTDIR = ROOT / 'workspace/data/quotient_lift'

def sha256_file(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for c in iter(lambda: f.read(1<<20), b''): h.update(c)
    return h.hexdigest()

def run_dfs(constraints, pair_rows, force, exclude, timeout):
    cmd = [DFS, '--constraints', constraints, '--pair-rows', pair_rows,
           '--timeout', str(timeout)]
    if force:
        cmd.extend(['--force', ','.join(str(p) for p in force)])
    if exclude:
        cmd.extend(['--exclude', ','.join(str(p) for p in exclude)])
    
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout+30)
    for line in r.stdout.strip().split('\n'):
        line = line.strip()
        if line.startswith('{'):
            return json.loads(line)
    return {'error': 'no output', 'stderr': r.stderr[:500], 'stdout': r.stdout[:500]}

def main():
    t0 = time.time()
    
    specs = json.loads((ROOT / 'workspace/data/quotient_branches/corrected_branch_specs.json').read_text())
    
    binaries = {
        'rank2': {
            'constraints': str(OUTDIR / 'rank2_full_merged_n19.bin'),
            'pair_rows': str(ROOT / 'workspace/data/quotient_dfs/rank2_cap7_first32.bin'),
        },
        'rank3': {
            'constraints': str(OUTDIR / 'rank3_full_merged_n19.bin'),
            'pair_rows': str(ROOT / 'workspace/data/quotient_dfs/rank3_cap7_first32.bin'),
        },
    }
    
    results = {
        'schema': 's0908_complete_branch_closure_v1',
        'dfs_executable': DFS,
        'dfs_source_sha256': sha256_file(ROOT / 'workspace/scripts/pair_prop_dfs.cpp'),
        'dfs_binary_sha256': sha256_file(DFS),
        'quotients': {},
    }
    
    all_closed = True
    
    for qname in ['rank3', 'rank2']:
        qspec = specs['pivots'][qname]
        bins = binaries[qname]
        
        results['quotients'][qname] = {
            'pivot': qspec['pivot'],
            'stabilizer_size': qspec.get('stabilizer_size_independent'),
            'num_orbits': qspec['num_orbits'],
            'constraints_binary': bins['constraints'],
            'constraints_sha256': sha256_file(bins['constraints']),
            'pair_rows_binary': bins['pair_rows'],
            'pair_rows_sha256': sha256_file(bins['pair_rows']),
            'branches': [],
        }
        
        for br in qspec['branches']:
            bi = br['branch']
            rep = br['representative']
            forbid = br['forbid']
            orbit_size = br['orbit_size']
            
            timeout = max(180, orbit_size * 5)  # generous timeout
            
            print(f"{qname} branch {bi} (rep={rep}, orbit_size={orbit_size}, "
                  f"forbid={len(forbid)})...", end='', flush=True)
            
            result = run_dfs(bins['constraints'], bins['pair_rows'],
                           [rep], forbid, timeout)
            
            complete = result.get('complete', False)
            solutions = result.get('solutions', 0)
            calls = result.get('recursive_calls', -1)
            elapsed = result.get('elapsed_sec', -1)
            max_depth = result.get('max_depth', -1)
            
            if not complete or solutions > 0:
                all_closed = False
            
            status = 'CLOSED' if (complete and solutions == 0) else \
                     'TIMEOUT' if not complete else 'SOLUTIONS_FOUND'
            
            print(f" {status}, calls={calls}, depth={max_depth}, time={elapsed:.1f}s")
            
            results['quotients'][qname]['branches'].append({
                'branch': bi,
                'representative': rep,
                'forbid': forbid,
                'orbit_size': orbit_size,
                'status': status,
                'complete': complete,
                'solutions': solutions,
                'recursive_calls': calls,
                'max_depth': max_depth,
                'elapsed_sec': elapsed,
                'pair_prunes': result.get('pair_prunes', 0),
                'pair_propagations': result.get('pair_propagations', 0),
            })
    
    results['all_closed'] = all_closed
    results['total_elapsed_sec'] = time.time() - t0
    
    out_path = OUTDIR / 'complete_closure_suite.json'
    out_path.write_text(json.dumps(results, indent=2) + '\n')
    
    print(f"\n{'='*60}")
    print(f"ALL BRANCHES CLOSED: {all_closed}")
    print(f"Total time: {results['total_elapsed_sec']:.1f}s")
    print(f"Saved: {out_path}")

if __name__ == '__main__':
    main()
