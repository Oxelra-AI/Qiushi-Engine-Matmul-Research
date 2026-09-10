#!/usr/bin/env python3
r"""Run CaDiCaL without -n on graph-IS CNFs to obtain SAT models."""
import argparse
import json
import pathlib
import subprocess
import time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cnfs', nargs='+', required=True)
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--time', type=int, default=60)
    args = ap.parse_args()
    out_dir = pathlib.Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    recs = []
    for cnf_s in args.cnfs:
        cnf = pathlib.Path(cnf_s)
        log = out_dir / (cnf.stem + '.model.log')
        cmd = ['cadical']
        if args.time > 0:
            cmd += ['-t', str(args.time)]
        cmd.append(str(cnf))
        t0 = time.time()
        with log.open('w') as f:
            proc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, text=True)
        text = log.read_text(errors='ignore')
        rec = {
            'cnf': str(cnf),
            'log': str(log),
            'exit': proc.returncode,
            'elapsed_sec': time.time() - t0,
            'has_sat': 'SATISFIABLE' in text and 'UNSATISFIABLE' not in text,
            'has_model_line': any(line.startswith('v ') for line in text.splitlines()),
        }
        print(json.dumps(rec, sort_keys=True))
        recs.append(rec)
    (out_dir / 'summary.json').write_text(json.dumps({'records': recs}, indent=2, sort_keys=True) + '\n')


if __name__ == '__main__':
    main()
