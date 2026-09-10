#!/usr/bin/env python3
"""Check frozen inputs and replay requested computations into a fresh run.

Saved successes never substitute for newly requested computations. Historical
mathematical diagnostics stay historical; all_ok covers only the stated scope.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

PACKAGE = Path(__file__).resolve().parent
MANIFEST = PACKAGE / 'manifest.json'
SCRIPTS = 'assets/occupation/scripts/'
WANG_CERT = 'assets/quotients/data/wang_f2_lb20/cert_matrix_q02_n333.pb.txt'


def sha256(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def run(cmd, timeout=None):
    started = time.monotonic()
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    try:
        proc = subprocess.Popen(cmd, cwd=PACKAGE, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, text=True, env=env,
                                start_new_session=True)
    except OSError as exc:
        return {'command': cmd, 'ok': False, 'returncode': None, 'error': str(exc)}
    timed_out = False
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        # Descendants such as drat-trim must not survive a bundle timeout.
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = proc.communicate()
    return {'command': cmd, 'returncode': proc.returncode,
            'elapsed_sec': time.monotonic() - started, 'timed_out': timed_out,
            'stdout_tail': stdout[-4000:], 'stderr_tail': stderr[-4000:],
            'ok': proc.returncode == 0 and not timed_out}


def check_manifest_hashes(manifest):
    bad, seen = [], set()
    files = manifest.get('files')
    if not isinstance(files, list) or not files:
        return {'ok': False, 'bad': ['missing or empty file manifest']}
    for item in files:
        try:
            rel = Path(item['path'])
            path = PACKAGE / rel
            if (rel.is_absolute() or '..' in rel.parts or rel.as_posix() in seen
                    or path.is_symlink() or not path.resolve().is_relative_to(PACKAGE.resolve())):
                raise ValueError('unsafe or duplicate path')
            seen.add(rel.as_posix())
            if not path.is_file() or sha256(path) != item['sha256']:
                raise ValueError('missing input or hash mismatch')
        except (KeyError, TypeError, ValueError, OSError) as exc:
            bad.append({'path': item.get('path') if isinstance(item, dict) else None,
                        'error': str(exc)})
    return {'ok': not bad, 'checked_count': len(seen), 'bad': bad}


def checked_json(cmd, path, schema, success_key, timeout):
    """The caller supplies a new run directory, never a historical result path."""
    if path.exists() or path.is_symlink():
        return {'ok': False, 'error': 'output already exists; stale result refused'}
    result = run(cmd, timeout=timeout)
    if not result.get('ok') or result.get('returncode') != 0:
        result['ok'] = False
        return result
    try:
        if not path.is_file() or path.is_symlink():
            raise ValueError('fresh output missing or not a regular file')
        payload = json.loads(path.read_text())
        if not isinstance(payload, dict) or payload.get('schema') != schema:
            raise ValueError('unexpected output schema')
        if payload.get(success_key) is not True:
            raise ValueError('child reported unsuccessful checks')
        result['result'] = payload
        result['result_sha256'] = sha256(path)
    except (OSError, ValueError, TypeError) as exc:
        result.update(ok=False, error=str(exc))
    return result


def reexpand(directory):
    exe, binary = directory / 'wang_lut_reexpand', directory / 'lut.bin'
    summary, comparison = directory / 'lut-summary.json', directory / 'lut-compare.json'
    compile_result = run(['g++', '-O3', '-std=c++17', SCRIPTS + 'wang_lut_reexpand.cpp',
                          '-o', str(exe)], timeout=120)
    result = {'compile': compile_result, 'ok': False}
    if not compile_result['ok']:
        return result
    execution = run([str(exe), '--cert', WANG_CERT, '--out-bin', str(binary),
                     '--out-json', str(summary)], timeout=600)
    result['expansion'] = execution
    if not execution['ok'] or not binary.is_file() or not summary.is_file():
        return result
    try:
        if json.loads(summary.read_text()).get('ok') is not True:
            return result
    except (OSError, ValueError, AttributeError):
        return result
    comparison_result = checked_json(
        [sys.executable, '-B', SCRIPTS + 'compare_reexpanded_lut.py',
         '--bin', str(binary), '--summary', str(summary), '--out', str(comparison)],
        comparison, 'reexpanded_lut_compare_v1', 'ok', 600)
    result.update(comparison=comparison_result, ok=comparison_result['ok'])
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay-drat', action='store_true')
    parser.add_argument('--regenerate-cnf', action='store_true', help='Also implies DRAT replay.')
    parser.add_argument('--reexpand-lut', action='store_true')
    parser.add_argument('--rerun-wang-verifier', action='store_true')
    parser.add_argument('--drat-timeout', type=int, default=900)
    parser.add_argument('--out', type=Path, help='New result file, relative to current directory.')
    args = parser.parse_args(argv)
    if args.drat_timeout <= 0:
        parser.error('--drat-timeout must be positive')
    if args.out and (args.out.exists() or args.out.is_symlink()
                     or args.out.resolve().is_relative_to(PACKAGE.resolve())):
        parser.error('--out must be new and outside the frozen proof directory')
    build = PACKAGE.parent / 'build/verification'
    build.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix='run-', dir=build)).resolve()
    output = args.out.resolve() if args.out else directory / 'result.json'
    result = {'schema': 'qiushi.matmul.verification.v2', 'run_id': directory.name,
              'started_at': time.time(), 'requested_checks': {
                  'drat': args.replay_drat or args.regenerate_cnf,
                  'regenerate_cnf': args.regenerate_cnf, 'reexpand_lut': args.reexpand_lut,
                  'wang_verifier': args.rerun_wang_verifier},
              'scope': 'requested computational checks; not independent human theorem review',
              'historical_records_are_not_fresh_proof_checks': True, 'all_ok': False}
    checks = []
    try:
        manifest_hash = sha256(MANIFEST)
        manifest = json.loads(MANIFEST.read_text())
        result['manifest_sha256'] = manifest_hash
        result['manifest_before'] = check_manifest_hashes(manifest)
        if not result['manifest_before']['ok']:
            raise ValueError('Input integrity failed; no proof code executed')
        checks.append(True)
        if args.replay_drat or args.regenerate_cnf:
            out = directory / 'bundle.json'
            cmd = [sys.executable, '-B', SCRIPTS + 'bundle_checker.py',
                   '--out', str(out), '--drat-timeout', str(args.drat_timeout)]
            if args.regenerate_cnf:
                cmd.append('--regenerate-cnf')
            bundle = checked_json(cmd, out, 'lower_bound_bundle_check_v1',
                                  'all_ok', max(args.drat_timeout * 10, 1200))
            if bundle['ok']:
                rows = bundle['result'].get('drat_bundle', {}).get('results', [])
                bundle['ok'] = (
                    [r.get('cert_index') for r in rows] == list(range(484, 492))
                    and all(r.get('ok') is True and r.get('drat_trim_returncode') == 0
                            and r.get('drat_trim_verified_now') is True
                            and (not args.regenerate_cnf or r.get('regenerated_cnf_matches') is True)
                            for r in rows))
            result['bundle'] = bundle
            checks.append(bundle['ok'])
        if args.reexpand_lut:
            result['lut'] = reexpand(directory)
            checks.append(result['lut']['ok'])
        if args.rerun_wang_verifier:
            out = directory / 'wang.json'
            result['wang'] = checked_json(
                [sys.executable, '-B', SCRIPTS + 'rerun_wang_verifier.py', '--out', str(out)],
                out, 'wang_verifier_rerun_v1', 'ok', 180)
            checks.append(result['wang']['ok'])
        result['manifest_after'] = check_manifest_hashes(manifest)
        checks.append(result['manifest_after']['ok'] and sha256(MANIFEST) == manifest_hash)
        result['all_ok'] = all(checks)
    except (OSError, ValueError, TypeError, KeyError) as exc:
        result['error'] = str(exc)
    result['elapsed_sec'] = time.time() - result['started_at']
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open('x') as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(json.dumps({'all_ok': result['all_ok'], 'out': str(output),
                      'elapsed_sec': result['elapsed_sec'], 'scope': result['scope']}))
    return 0 if result['all_ok'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
