#!/usr/bin/env python3
"""Batch independent LP/MILP audit for all surviving coset CEGAR closures."""
from __future__ import annotations
import argparse, json, sys, time
from pathlib import Path
from collections import Counter
SCRIPT = Path(__file__).resolve().parent
if str(SCRIPT) not in sys.path:
    sys.path.insert(0, str(SCRIPT))
from coset_active_constraint_audit import audit_one  # type: ignore


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, default=Path('data/coset_ansatz'))
    ap.add_argument('--pattern', default='cegar_H*/cegar_result.json')
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--milp-time', type=float, default=60.0)
    args = ap.parse_args()
    files = sorted(args.root.glob(args.pattern))
    recs=[]; t0=time.time()
    for p in files:
        rec=audit_one(p, Path('data/wang_f2_lb20/wang_subspace_lut.pkl'), Path('data/wang_native/full_tensor/full_wang512_cap19_len20_all_dim9_allbinding.bin'), args.milp_time)
        recs.append(rec)
        print(f"{p.parent.name}: LP {rec['lp']['status']} MILP {None if rec['milp'] is None else rec['milp']['status']} rows {rec['active_reconstruction']['unique_reconstructed_rows']} elapsed {rec['elapsed_sec']:.2f}", flush=True)
    summary={
        'schema':'coset_ansatz_batch_audit_v1',
        'root':str(args.root),
        'pattern':args.pattern,
        'count':len(recs),
        'lp_status_hist':dict(Counter(str(r['lp']['status']) for r in recs)),
        'milp_status_hist':dict(Counter(str(None if r['milp'] is None else r['milp']['status']) for r in recs)),
        'records':recs,
        'elapsed_sec':time.time()-t0,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(summary, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'out':str(args.out),'count':len(recs),'lp_status_hist':summary['lp_status_hist'],'milp_status_hist':summary['milp_status_hist'],'elapsed_sec':summary['elapsed_sec']}, indent=2, sort_keys=True))

if __name__=='__main__':
    main()
