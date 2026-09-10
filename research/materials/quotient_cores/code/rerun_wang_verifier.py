#!/usr/bin/env python3
"""Rerun the pinned Wang q=2 n=333 verifier and save a fresh receipt."""
from __future__ import annotations
import argparse, hashlib, json, subprocess, time, shutil
from pathlib import Path

CERT = Path('data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt')
OUT = Path('data/wang_verify/wang_verifier_rerun.json')

def sha256(p: Path) -> str:
    h=hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda:f.read(1<<20), b''):
            h.update(chunk)
    return h.hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--cert', type=Path, default=CERT)
    ap.add_argument('--out', type=Path, default=OUT)
    args=ap.parse_args()
    cmd=['qiushi-matmul','lower-bound','verify-wang-q2-333',str(args.cert)]
    t0=time.time()
    proc=subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    elapsed=time.time()-t0
    parsed=None
    try:
        parsed=json.loads(proc.stdout) if proc.stdout.strip() else None
    except Exception as e:
        parsed={'parse_error':repr(e)}
    rec={
        'schema':'wang_verifier_rerun_v1',
        'command':cmd,
        'certificate':str(args.cert),
        'certificate_sha256':sha256(args.cert),
        'returncode':proc.returncode,
        'elapsed_sec':elapsed,
        'stdout':proc.stdout,
        'stderr':proc.stderr,
        'parsed_stdout':parsed,
        'status': (parsed or {}).get('status') if isinstance(parsed,dict) else None,
        'claimed_lower_bound': (parsed or {}).get('claimed_lower_bound') if isinstance(parsed,dict) else None,
        'domain': (parsed or {}).get('domain') if isinstance(parsed,dict) else None,
    }
    rec['ok']=(proc.returncode==0 and rec['status']=='verified' and rec['claimed_lower_bound']==20 and rec['domain']=='prime 2' and rec['certificate_sha256']=='25595a883ce877eecd802139ff4e07646e154b2797ad6fe7f9ec737ab0c6135d')
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(rec, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'ok':rec['ok'],'out':str(args.out),'status':rec['status'],'lb':rec['claimed_lower_bound'],'sha256':rec['certificate_sha256'],'elapsed_sec':elapsed}, indent=2, sort_keys=True))
if __name__=='__main__': main()
