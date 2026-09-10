#!/usr/bin/env python3
"""Audit the analysis PySAT seqcounter global-cardinality encoding.

analysis built the equality constraint by creating CardEnc.atmost and
CardEnc.atleast inside one Python list while passing the same top_id to both.
For encodings with auxiliary variables this reuses the same auxiliary variable
numbers for two independent circuits.  This script isolates that construction
from all Wang rows.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import time
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF


def sha256(path: Path) -> str | None:
    if not path.exists() or path.stat().st_size == 0:
        return None
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def build_formula(n_decision: int, target: int, buggy: bool) -> CNF:
    formula = CNF()
    lits = list(range(1, n_decision + 1))
    top = n_decision
    if buggy:
        # This is the analysis programming pattern: Python constructs both
        # CardEnc objects before the loop body updates `top`, so both encoders
        # allocate the same auxiliary variable interval starting at top+1.
        for card in [
            CardEnc.atmost(lits, target, top_id=top, encoding=EncType.seqcounter),
            CardEnc.atleast(lits, target, top_id=top, encoding=EncType.seqcounter),
        ]:
            top = max(top, card.nv)
            formula.extend(card.clauses)
    else:
        card = CardEnc.atmost(lits, target, top_id=top, encoding=EncType.seqcounter)
        top = max(top, card.nv)
        formula.extend(card.clauses)
        card = CardEnc.atleast(lits, target, top_id=top, encoding=EncType.seqcounter)
        top = max(top, card.nv)
        formula.extend(card.clauses)
    formula.nv = max(formula.nv, top)
    return formula


def solve(cnf_path: Path, out_prefix: Path, timeout: int) -> dict:
    log = out_prefix.with_suffix('.cadical.log')
    drat = out_prefix.with_suffix('.drat')
    t0 = time.time()
    proc = subprocess.run(
        ['cadical', '--unsat', '--binary=false', '-n', str(cnf_path), str(drat)],
        capture_output=True, text=True, timeout=timeout,
    )
    log.write_text(proc.stdout + proc.stderr)
    trim_log = out_prefix.with_suffix('.drat_trim.log')
    trim_status = None
    if proc.returncode == 20 and drat.exists():
        trim = subprocess.run(['drat-trim', str(cnf_path), str(drat)], capture_output=True, text=True, timeout=timeout)
        trim_log.write_text(trim.stdout + trim.stderr)
        trim_status = 'VERIFIED' if 's VERIFIED' in (trim.stdout + trim.stderr) else f'exit_{trim.returncode}'
    return {
        'exit': proc.returncode,
        'status': 'SAT' if proc.returncode == 10 else ('UNSAT' if proc.returncode == 20 else f'EXIT_{proc.returncode}'),
        'elapsed_sec': time.time() - t0,
        'log': str(log),
        'drat': str(drat),
        'drat_size': drat.stat().st_size if drat.exists() else None,
        'drat_sha256': sha256(drat),
        'trim_log': str(trim_log) if trim_log.exists() else None,
        'trim_status': trim_status,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--n-decision', type=int, default=509)
    ap.add_argument('--target', type=int, default=18)
    ap.add_argument('--outdir', type=Path, default=Path('data/audit'))
    ap.add_argument('--timeout', type=int, default=120)
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)

    results = []
    for buggy in (True, False):
        tag = 'buggy_shared_top' if buggy else 'correct_disjoint_aux'
        cnf = args.outdir / f'global_equal_{tag}.cnf'
        formula = build_formula(args.n_decision, args.target, buggy)
        formula.to_file(str(cnf))
        res = {
            'tag': tag,
            'buggy': buggy,
            'n_decision': args.n_decision,
            'target': args.target,
            'vars': formula.nv,
            'clauses': len(formula.clauses),
            'cnf': str(cnf),
            'cnf_sha256': sha256(cnf),
        }
        res.update(solve(cnf, args.outdir / f'global_equal_{tag}', args.timeout))
        results.append(res)
        print(json.dumps(res, indent=2, sort_keys=True), flush=True)
    out = args.outdir / 'global_cardinality_bug_audit.json'
    out.write_text(json.dumps(results, indent=2, sort_keys=True) + '\n')
    print(f'saved {out}')


if __name__ == '__main__':
    main()
