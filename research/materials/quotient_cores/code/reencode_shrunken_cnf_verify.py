#!/usr/bin/env python3
"""analysis: deterministic re-encoding check for the shrunken fixed-repeat CNF.

Given the selected high-level Wang-row indices stored in shrink_summary.json,
rebuild the clean CNF from source constraints and compare its SHA256 with the
DRAT-verified CNF.  This checks that the saved selected-row provenance really
reproduces the proof formula; it is not a substitute for DRAT, but links the
semantic rows to the binary proof object.
"""
from __future__ import annotations
import json, sys, time
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from complete_core_and_transversal import ROOT
from extract_fixed_repeat_core_cnf import build_high_level_constraints, emit_clean_cnf
from core_repeat_symmetry_and_cnf import sha256

OUTDIR = ROOT / 'workspace/data/repeat_branch_certificate'


def main():
    t0 = time.time()
    shrink_path = OUTDIR / 'iis_shrink_p1/shrink_summary.json'
    shrink = json.loads(shrink_path.read_text())
    source = Path(shrink['source'])
    fixed = int(shrink['fixed_repeat_point'])
    selected = [int(i) for i in shrink['selected_indices']]
    original_cnf = Path(shrink['clean_cnf']['files']['cnf'])
    original_hash = sha256(original_cnf)

    data = build_high_level_constraints(source, fixed)
    outdir = OUTDIR / 'iis_shrink_p1/reencode_check'
    meta = emit_clean_cnf(data, fixed, selected, outdir, 'fixed_repeat_p1_iis_reencoded')
    new_cnf = Path(meta['files']['cnf'])
    new_hash = sha256(new_cnf)

    result = {
        'schema': 'reencode_shrunken_cnf_verify_v1',
        'field': 'F2',
        'core': 'E11',
        'rank_s': int(shrink['rank_s']),
        'fixed_repeat_point': fixed,
        'source_shrink_summary': str(shrink_path),
        'source_constraint_file': str(source),
        'selected_indices_count': len(selected),
        'original_cnf': str(original_cnf),
        'original_cnf_sha256': original_hash,
        'reencoded_cnf': str(new_cnf),
        'reencoded_cnf_sha256': new_hash,
        'hash_match': original_hash == new_hash,
        'original_cnf_size': original_cnf.stat().st_size,
        'reencoded_cnf_size': new_cnf.stat().st_size,
        'reencoded_meta': str(outdir / 'fixed_repeat_p1_iis_reencoded.meta.json'),
        'reencoded_cnf_variables': int(meta['cnf_variables']),
        'reencoded_cnf_clauses': int(meta['cnf_clauses']),
        'elapsed_sec': round(time.time() - t0, 3),
    }
    path = OUTDIR / 'iis_shrink_p1/reencode_check/reencode_verify.json'
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
