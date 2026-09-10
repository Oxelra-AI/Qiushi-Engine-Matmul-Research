#!/usr/bin/env python3
"""Add release-hardening metadata to the research_record proof-package manifest.

The builder already records per-file sizes and SHA-256 hashes.  This script adds
package-level payload size/tree hash and records the local executable dependency
used for optional rerun of Wang's public verifier.  The manifest itself is not
included in the payload hash, avoiding a self-reference.
"""
from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import time
from pathlib import Path

PACKAGE = Path('research/research_record/deliverables/report/proof_package')
MANIFEST = PACKAGE / 'manifest.json'


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def tree_digest(files: list[dict]) -> str:
    h = hashlib.sha256()
    for item in sorted(files, key=lambda x: x['path']):
        h.update(item['path'].encode('utf-8'))
        h.update(b'\0')
        h.update(str(item['size_bytes']).encode('ascii'))
        h.update(b'\0')
        h.update(item['sha256'].encode('ascii'))
        h.update(b'\n')
    return h.hexdigest()


def executable_record(name: str) -> dict:
    p = shutil.which(name)
    rec = {'name': name, 'path': p, 'found': p is not None}
    if p:
        path = Path(p)
        rec['resolved_path'] = str(path.resolve())
        try:
            rec['sha256'] = sha256(path)
            rec['size_bytes'] = path.stat().st_size
        except Exception as e:
            rec['hash_error'] = repr(e)
    return rec


def command_json(cmd: list[str], timeout: int = 120) -> dict:
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        out = {'command': cmd, 'returncode': proc.returncode, 'stdout': proc.stdout[-12000:], 'stderr': proc.stderr[-12000:]}
        try:
            out['parsed_stdout'] = json.loads(proc.stdout) if proc.stdout.strip() else None
        except Exception as e:
            out['parse_error'] = repr(e)
        return out
    except Exception as e:
        return {'command': cmd, 'error': repr(e)}


def main() -> None:
    manifest = json.loads(MANIFEST.read_text())
    files = manifest['files']
    payload_size = sum(int(item['size_bytes']) for item in files)
    manifest['payload_file_count'] = len(files)
    manifest['payload_size_bytes'] = payload_size
    manifest['payload_tree_sha256'] = tree_digest(files)
    manifest['package_directory_size_bytes_excluding_manifest'] = sum(
        p.stat().st_size for p in PACKAGE.rglob('*') if p.is_file() and p != MANIFEST
    )
    deps = {
        'python_executable': command_json(['python', '-c', 'import sys, json; print(json.dumps({"executable": sys.executable, "version": sys.version}))'], 30),
        'drat_trim': executable_record('drat-trim'),
        'cadical': executable_record('cadical'),
        'qiushi_matmul': executable_record('qiushi-matmul'),
        'qiushi_matmul_doctor': command_json(['qiushi-matmul', 'doctor', '--json'], 120) if shutil.which('qiushi-matmul') else {'skipped': True, 'reason': 'qiushi-matmul not found'},
    }
    manifest['external_tool_dependencies_recorded_at_unix'] = time.time()
    manifest['external_tool_dependencies'] = deps
    manifest['wang_verifier_dependency_note'] = (
        "The package contains Wang's pinned public certificate and records the local qiushi-matmul "
        "verifier executable/version used for optional replay.  Wang's verifier remains an external "
        "dependency cited through arXiv:2603.07280v6 and the public repository named in that paper."
    )
    MANIFEST.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(json.dumps({
        'manifest': str(MANIFEST),
        'manifest_sha256': sha256(MANIFEST),
        'payload_file_count': manifest['payload_file_count'],
        'payload_size_bytes': manifest['payload_size_bytes'],
        'payload_tree_sha256': manifest['payload_tree_sha256'],
        'package_directory_size_bytes_excluding_manifest': manifest['package_directory_size_bytes_excluding_manifest'],
        'qiushi_matmul': deps['qiushi_matmul'],
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
