#!/usr/bin/env python3
"""Exercise empty-XOR handling in e11_fixed_u_xor_sat.py.

The fixed-A encoder must distinguish an uncovered Brent equation 0=0 from
an uncovered Brent equation 0=1.  The rank-21 E11 positive control never
forces an empty active set, so this toy test uses a 2 x 1 x 1 core and a
single A-mask u=1.  A-coordinate 1 is uncovered.

Case empty_rhs0: core[1,0,0]=0, should be SAT.
Case empty_rhs1: core[1,0,0]=1, should be UNSAT through an empty CNF clause.
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import numpy as np

ROOT = Path('research/research_record')
SCRIPT = ROOT / 'workspace/scripts/e11_fixed_u_xor_sat.py'
OUTDIR = ROOT / 'workspace/data/e11_fixed_u_xor_tests'


def run_case(name: str, core: np.ndarray, expected: str):
    OUTDIR.mkdir(parents=True, exist_ok=True)
    core_path = OUTDIR / f'{name}_core.npy'
    np.save(core_path, core.astype(np.uint8) & 1)
    cmd = [
        sys.executable, '-B', str(SCRIPT),
        '--core', str(core_path),
        '--u-list', '1',
        '--outdir', str(OUTDIR),
        '--name', name,
        '--timeout', '30',
        '--threads', '1',
    ]
    proc = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60)
    json_path = OUTDIR / f'{name}.json'
    result = json.loads(json_path.read_text()) if json_path.exists() else None
    cnf_path = OUTDIR / f'{name}.xor.cnf'
    cnf_lines = cnf_path.read_text().splitlines() if cnf_path.exists() else []
    empty_clause_count = sum(1 for ln in cnf_lines if ln.strip() == '0')
    empty_xor_count = sum(1 for ln in cnf_lines if ln.strip() == 'x 0')
    status = None if result is None else result.get('solver_status')
    ok = (proc.returncode in (0, 10, 20)) and status == expected
    return {
        'name': name,
        'expected': expected,
        'status': status,
        'ok': bool(ok),
        'returncode': proc.returncode,
        'stdout_tail': proc.stdout[-1000:],
        'stderr_tail': proc.stderr[-1000:],
        'json_path': str(json_path),
        'cnf_path': str(cnf_path),
        'empty_clause_count': int(empty_clause_count),
        'empty_xor_count': int(empty_xor_count),
        'cnf_header': next((ln for ln in cnf_lines if ln.startswith('p cnf ')), None),
    }


def main():
    # A bit 0 is covered by u=1; bit 1 is uncovered.
    core0 = np.zeros((2, 1, 1), dtype=np.uint8)
    core0[0, 0, 0] = 1  # satisfiable by v=w=1; uncovered equation is 0=0.
    core1 = np.zeros((2, 1, 1), dtype=np.uint8)
    core1[1, 0, 0] = 1  # uncovered equation is 0=1 and must be UNSAT.
    cases = [run_case('empty_rhs0_sat', core0, 'SAT'), run_case('empty_rhs1_unsat', core1, 'UNSAT')]
    summary = {
        'purpose': 'direct empty-XOR regression tests for e11_fixed_u_xor_sat.py',
        'script': str(SCRIPT),
        'cases': cases,
        'all_ok': all(c['ok'] for c in cases),
        'interpretation': 'The fixed-A native-XOR encoder correctly ignores empty 0=0 equations and encodes empty 0=1 equations as CNF contradiction; no x 0 line should appear.',
    }
    out = OUTDIR / 'empty_xor_regression_summary.json'
    out.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print(json.dumps(summary, indent=2, sort_keys=True))
    if not summary['all_ok']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
