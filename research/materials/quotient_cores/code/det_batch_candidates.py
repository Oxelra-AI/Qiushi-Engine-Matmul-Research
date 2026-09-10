#!/usr/bin/env python3
"""Run inverse-determination fixed-A SAT on candidates from a pipeline summary."""
from __future__ import annotations
import argparse, json, os, subprocess, sys, time
from pathlib import Path

SCRIPT = Path(__file__).resolve().parent

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--summary', type=Path, required=True)
    ap.add_argument('--outdir', type=Path, required=True)
    ap.add_argument('--timeout', type=int, default=120)
    ap.add_argument('--solver', default='cadical', choices=['cadical','kissat','cryptominisat5'])
    ap.add_argument('--mode', default='b2c', choices=['b2c','c2b','both'])
    ap.add_argument('--only-enhanced-pass', action='store_true')
    ap.add_argument('--max-candidates', type=int, default=1000)
    args = ap.parse_args()
    args.outdir.mkdir(parents=True, exist_ok=True)
    data = json.loads(args.summary.read_text())
    results = []
    t0 = time.time()
    picked = []
    for r in data.get('results', []):
        if args.only_enhanced_pass and r.get('enhanced_consistent') is not True:
            continue
        if r.get('violations', 999999) != 0:
            continue
        picked.append(r)
        if len(picked) >= args.max_candidates:
            break
    for idx, r in enumerate(picked):
        name = r.get('name', f'cand{idx}')
        ms = [int(x) for x in r['final_multiset']]
        od = args.outdir / name
        od.mkdir(parents=True, exist_ok=True)
        cmd = [sys.executable, str(SCRIPT / 'full_fixed_a_completion_det.py'),
               '--multiset', ','.join(map(str, ms)), '--outdir', str(od),
               '--name', name + '_det', '--mode', args.mode, '--timeout', str(args.timeout),
               '--solver', args.solver]
        print(f"[{idx+1}/{len(picked)}] {name}", flush=True)
        s0 = time.time()
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=args.timeout+40,
                                  env={**os.environ, 'PYTHONDONTWRITEBYTECODE':'1'})
            parsed = None
            try:
                parsed = json.loads(proc.stdout)
            except Exception:
                pass
            rec = {'name': name, 'rank_sum': r.get('final_rank_sum'), 'cmd': cmd,
                   'returncode_process': proc.returncode, 'elapsed_wrapper_sec': time.time()-s0,
                   'stdout_tail': '\n'.join(proc.stdout.splitlines()[-30:]),
                   'stderr_tail': '\n'.join(proc.stderr.splitlines()[-30:]),
                   'parsed': parsed}
            if parsed:
                print(f"  sat={parsed.get('sat')} rc={parsed.get('returncode')} sec={parsed.get('elapsed_sec')} vars={parsed.get('vars')} clauses={parsed.get('clauses')}", flush=True)
            else:
                print(f"  process rc={proc.returncode}; no parsed stdout", flush=True)
        except subprocess.TimeoutExpired as e:
            rec = {'name': name, 'rank_sum': r.get('final_rank_sum'), 'timeout_expired': True,
                   'elapsed_wrapper_sec': time.time()-s0, 'stdout_tail': (e.stdout or '')[-4000:] if isinstance(e.stdout, str) else '',
                   'stderr_tail': (e.stderr or '')[-4000:] if isinstance(e.stderr, str) else ''}
            print("  wrapper timeout", flush=True)
        results.append(rec)
        (args.outdir / 'det_batch_summary.json').write_text(json.dumps({'schema':'det_batch_candidates_v1','summary':str(args.summary),'timeout':args.timeout,'mode':args.mode,'solver':args.solver,'elapsed_sec':time.time()-t0,'results':results}, indent=2, sort_keys=True)+'\n')
    final = {'schema':'det_batch_candidates_v1','summary':str(args.summary),'timeout':args.timeout,'mode':args.mode,'solver':args.solver,'selected_count':len(picked),'elapsed_sec':time.time()-t0,'results':results}
    out = args.outdir / 'det_batch_summary.json'
    out.write_text(json.dumps(final, indent=2, sort_keys=True)+'\n')
    counts = {'sat':0,'unsat':0,'unknown':0}
    for rec in results:
        p = rec.get('parsed') or {}
        if p.get('sat') is True: counts['sat'] += 1
        elif p.get('sat') is False: counts['unsat'] += 1
        else: counts['unknown'] += 1
    print(json.dumps({'out':str(out),'selected_count':len(picked),'counts':counts,'elapsed_sec':final['elapsed_sec']}, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
