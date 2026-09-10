#!/usr/bin/env python3
"""analysis: Test quotient branch DFS with merged (original + lift-derived) rows.

Compares branches with original cap<=5 vs merged cap<=5 + DC-lift rows.
Uses the corrected branch specs from analysis and the patched pair-prop DFS.
"""
import json, subprocess, time
from pathlib import Path

ROOT = Path('research/research_record')
DFS = str(ROOT / 'workspace/scripts/pair_prop_dfs')
_raw = json.loads((ROOT / 'workspace/data/quotient_branches/corrected_branch_specs.json').read_text())
SPECS = _raw['pivots']
OUTDIR = ROOT / 'workspace/data/quotient_lift'

# Binaries
ORIG = {
    'rank2': str(ROOT / 'workspace/data/quotient_dfs/rank2_cap5_n19.bin'),
    'rank3': str(ROOT / 'workspace/data/quotient_dfs/rank3_cap5_n19.bin'),
}
MERGED = {
    'rank2': str(OUTDIR / 'rank2_merged_cap5_n19.bin'),
    'rank3': str(OUTDIR / 'rank3_merged_cap5_n19.bin'),
}

def run_dfs(binary, force, exclude, target, timeout, pair_binary=None):
    """Run the pair-prop DFS and return parsed JSON."""
    cmd = [DFS, '--constraints', binary, '--target', str(target), '--timeout', str(timeout)]
    if force:
        cmd.extend(['--force'] + [str(p) for p in force])
    if exclude:
        cmd.extend(['--exclude'] + [str(p) for p in exclude])
    if pair_binary:
        cmd.extend(['--pair-rows', pair_binary])
    
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout+30)
        # Parse JSON from stdout
        for line in r.stdout.strip().split('\n'):
            line = line.strip()
            if line.startswith('{'):
                return json.loads(line)
    except Exception as e:
        return {'error': str(e)}
    return {'error': 'no JSON output'}

def main():
    results = {'schema': 's0908_merged_dfs_test_v1', 'tests': []}
    
    for qname in ['rank3', 'rank2']:
        spec = SPECS[qname]
        branches = spec['branches']
        
        # Select a few branches: the first 3 (hardest) and an easy one
        if qname == 'rank3':
            test_indices = [0, 1, 2]  # 6 orbits, 0 and 1 are hard
        else:
            test_indices = [0, 1, 2]  # 14 orbits, several hard
        
        for bi in test_indices:
            br = branches[bi]
            rep = br['representative']
            excl = br['forbid']
            
            for label, binary in [('original', ORIG[qname]), ('merged', MERGED[qname])]:
                timeout = 30
                print(f"{qname} branch {bi} (rep={rep}) [{label}]...", end='', flush=True)
                
                t0 = time.time()
                result = run_dfs(binary, [rep], excl, 19, timeout)
                elapsed = time.time() - t0
                
                complete = result.get('complete', False)
                solutions = result.get('solutions_found', '?')
                calls = result.get('recursive_calls', '?')
                max_depth = result.get('max_depth', '?')
                
                print(f" complete={complete}, solutions={solutions}, "
                      f"calls={calls}, depth={max_depth}, time={elapsed:.1f}s")
                
                results['tests'].append({
                    'quotient': qname,
                    'branch': bi,
                    'rep': rep,
                    'label': label,
                    'complete': complete,
                    'solutions': solutions,
                    'calls': calls,
                    'max_depth': max_depth,
                    'elapsed': elapsed,
                })
    
    out_path = OUTDIR / 'merged_dfs_test.json'
    out_path.write_text(json.dumps(results, indent=2) + '\n')
    print(f"\nSaved to {out_path}")

if __name__ == '__main__':
    main()
