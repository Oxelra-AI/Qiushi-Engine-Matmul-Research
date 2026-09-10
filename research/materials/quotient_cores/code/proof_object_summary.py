#!/usr/bin/env python3
"""Summarize related analysis finite-field Wang proof-object carriers for analysis review.

This script does not certify mathematical semantics; it records stable file hashes,
DRAT-trim verification flags, and branch status JSONs for critical review.
"""
import glob
import hashlib
import json
from pathlib import Path

ROOT = Path('data')
OUT = Path('data/review/a01_proof_object_summary.json')

FILES = [
    ROOT/'wang_capacity_cnf/t_s20_dim123_branch_rank3.cnf',
    ROOT/'wang_capacity_cnf/t_s20_dim123_branch_rank3.drat',
    ROOT/'wang_capacity_cnf/t_s20_dim123_branch_rank3.drat_trim.log',
    ROOT/'wang_capacity_cnf/t_s20_dim123_branch_rank3.meta.json',
    ROOT/'wang_capacity_cnf_rank2/t_s20_dim123_branch_rank2.cnf',
    ROOT/'wang_capacity_cnf_rank2/t_s20_dim123_branch_rank2.drat',
    ROOT/'wang_capacity_cnf_rank2/t_s20_dim123_branch_rank2.drat_trim.log',
    ROOT/'wang_capacity_cnf_rank2/t_s20_dim123_branch_rank2.meta.json',
    ROOT/'wang_capacity_rank1_count_cnf/rank1_count_ge19_size_le09.cnf',
    ROOT/'wang_capacity_rank1_count_cnf/rank1_count_ge19_size_le09.drat',
    ROOT/'wang_capacity_rank1_count_cnf/rank1_count_ge19_size_le09.drat_trim.log',
    ROOT/'wang_capacity_rank1_count_cnf/rank1_count_ge19_size_le09.meta.json',
    ROOT/'wang_capacity_rank1_count_cnf/nofixed_retry/rank1_count_ge19_nofixed_size_le09.cnf',
    ROOT/'wang_capacity_rank1_count_cnf/nofixed_retry/rank1_count_ge19_nofixed_size_le09.drat',
    ROOT/'wang_capacity_rank1_count_cnf/nofixed_retry/rank1_count_ge19_nofixed_size_le09.drat_trim.log',
    ROOT/'wang_capacity_rank1_count_cnf/nofixed_retry/rank1_count_ge19_nofixed_size_le09.meta.json',
    ROOT/'wang_capacity_rank1_count_cnf/dim1_lut_lb19_check.json',
    ROOT/'wang_f2_lb20/wang_subspace_lut.meta.json',
]

def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()

def tail(path: Path, n: int = 6) -> str:
    txt = path.read_text(errors='ignore')
    return '\n'.join(txt.strip().splitlines()[-n:])

def maybe_json(path: Path):
    try:
        return json.loads(path.read_text())
    except Exception as exc:
        return {'json_error': repr(exc)}

def summarize_file(path: Path):
    rec = {'path': str(path), 'exists': path.exists()}
    if not path.exists():
        return rec
    rec['size'] = path.stat().st_size
    rec['sha256'] = sha256(path)
    if path.suffix == '.log':
        txt = path.read_text(errors='ignore')
        rec['contains_s_VERIFIED'] = 's VERIFIED' in txt
        rec['contains_s_UNSATISFIABLE'] = 's UNSATISFIABLE' in txt
        rec['contains_exit_20'] = 'exit 20' in txt
        rec['tail'] = tail(path)
    if path.suffix == '.json':
        rec['json'] = maybe_json(path)
    return rec

def main():
    OUT.parent.mkdir(parents=True, exist_ok=True)
    records = [summarize_file(p) for p in FILES]
    fixed_statuses = []
    for f in sorted(glob.glob(str(ROOT/'wang_capacity_e11_fixed/*/*.status.json'))):
        p = Path(f)
        fixed_statuses.append({'path': f, 'sha256': sha256(p), 'json': maybe_json(p)})
    fixed_trim_logs = []
    for f in sorted(glob.glob(str(ROOT/'wang_capacity_e11_fixed/*/*.drat_trim.log'))):
        p = Path(f)
        fixed_trim_logs.append(summarize_file(p))
    pair_statuses = []
    for f in sorted(glob.glob(str(ROOT/'wang_capacity_e11_pairfull/rep_010_dim678/*.status.json'))):
        p = Path(f)
        pair_statuses.append({'path': f, 'sha256': sha256(p), 'json': maybe_json(p)})
    out = {
        'purpose': 'analysis related analysis review of related analysis finite-field Wang proof carriers; hashes and log flags only.',
        'files': records,
        'fixed_e11_statuses': fixed_statuses,
        'fixed_e11_drat_trim_logs': fixed_trim_logs,
        'rep010_pairfull_statuses': pair_statuses,
    }
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True))
    print(json.dumps({
        'out': str(OUT),
        'main_file_count': len(records),
        'fixed_status_count': len(fixed_statuses),
        'fixed_trim_log_count': len(fixed_trim_logs),
        'pair_status_count': len(pair_statuses),
        'verified_trim_logs': [r['path'] for r in fixed_trim_logs + records if r.get('contains_s_VERIFIED')],
    }, indent=2))

if __name__ == '__main__':
    main()
