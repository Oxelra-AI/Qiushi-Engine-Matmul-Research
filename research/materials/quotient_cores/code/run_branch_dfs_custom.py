#!/usr/bin/env python3
"""analysis: run analysis pair-propagation DFS with explicit corrected quotient branch specs.

The C++ executable has an old built-in E11 branch table, so this wrapper uses
--force/--exclude with branch=-2 (single custom run) from
corrected_branch_specs.json.  It is suitable for rank2/rank3 quotient
branches with custom row binaries.
"""
from __future__ import annotations
import argparse, hashlib, json, subprocess, time
from pathlib import Path

ROOT = Path('research/research_record')
SPECS = ROOT/'workspace/data/quotient_branches/corrected_branch_specs.json'
PAIR_RUN = ROOT/'workspace/scripts/pair_prop_dfs'


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda: f.read(1 << 20), b''):
            h.update(c)
    return h.hexdigest()


def parse_first_json(stdout: str):
    for line in stdout.splitlines():
        line = line.strip()
        if line.startswith('{') and '"target"' in line:
            return json.loads(line)
    return None


def run_one(pivot: str, br: dict, constraints: Path, pair_rows: Path, outdir: Path, timeout: int, label: str):
    force = ','.join(map(str, br['force']))
    forbid = ','.join(map(str, br['forbid']))
    outfile = outdir/f'{label}_{pivot}_branch{br["branch"]}_{timeout}s.json'
    cmd = [str(PAIR_RUN), '--constraints', str(constraints), '--pair-rows', str(pair_rows), '--target', '19', '--force', force, '--timeout', str(timeout), '--output', str(outfile)]
    if forbid:
        cmd += ['--exclude', forbid]
    t0 = time.time()
    cp = subprocess.run(cmd, text=True, capture_output=True, timeout=timeout+45)
    wall = time.time() - t0
    result = parse_first_json(cp.stdout) if cp.returncode == 0 else None
    rec = {
        'pivot': pivot,
        'branch': br['branch'],
        'representative': br['representative'],
        'force': br['force'],
        'forbid_count': br['forbid_count'],
        'orbit_size': br['orbit_size'],
        'returncode': cp.returncode,
        'wall_sec': wall,
        'output': str(outfile),
        'stdout_tail': cp.stdout[-1200:],
        'stderr_tail': cp.stderr[-800:],
        'result': result,
    }
    if result:
        for k in ['complete','timeout','solutions','recursive_calls','candidate_tests','max_depth','global_shortage','pair_prunes','pair_forces','pair_propagations','saturated_rows','saturation_removed_points']:
            rec[k] = result.get(k)
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pivot', choices=['rank2','rank3'], required=True)
    ap.add_argument('--branches', required=True, help='comma-separated branch ids')
    ap.add_argument('--constraints', type=Path, required=True)
    ap.add_argument('--pair-rows', type=Path, required=True)
    ap.add_argument('--timeout', type=int, default=300)
    ap.add_argument('--label', required=True)
    ap.add_argument('--outdir', type=Path, default=ROOT/'workspace/data/quotient_lift/tightening')
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    specs = json.loads(SPECS.read_text())['pivots'][args.pivot]['branches']
    wanted = {int(x) for x in args.branches.split(',') if x.strip()}
    out = {
        'schema': 's0908_custom_branch_dfs_v1',
        'pivot': args.pivot,
        'branches': sorted(wanted),
        'timeout': args.timeout,
        'label': args.label,
        'dfs_executable': str(PAIR_RUN),
        'constraints': str(args.constraints),
        'constraints_sha256': sha(args.constraints),
        'pair_rows': str(args.pair_rows),
        'pair_rows_sha256': sha(args.pair_rows),
        'runs': [],
    }
    for br in specs:
        if br['branch'] not in wanted:
            continue
        print(f'{args.pivot} branch {br["branch"]} force={br["force"]} forbid_count={br["forbid_count"]}', flush=True)
        rec = run_one(args.pivot, br, args.constraints, args.pair_rows, args.outdir, args.timeout, args.label)
        out['runs'].append(rec)
        print(json.dumps({k: rec.get(k) for k in ['branch','complete','timeout','solutions','recursive_calls','max_depth','pair_prunes','pair_forces','wall_sec']}, sort_keys=True), flush=True)
    out['summary'] = [{k: r.get(k) for k in ['branch','complete','timeout','solutions','recursive_calls','candidate_tests','max_depth','global_shortage','pair_prunes','pair_forces','pair_propagations','wall_sec']} for r in out['runs']]
    out['all_wanted_closed'] = all(r.get('complete') and r.get('solutions') == 0 for r in out['runs'])
    path = args.outdir/f'{args.label}_{args.pivot}_branches_{"_".join(map(str, sorted(wanted)))}_{args.timeout}s_manifest.json'
    path.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print('saved', path)
    print(json.dumps({'all_wanted_closed': out['all_wanted_closed'], 'summary': out['summary'], 'manifest': str(path)}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
