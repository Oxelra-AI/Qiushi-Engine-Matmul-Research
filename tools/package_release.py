#!/usr/bin/env python3
"""Package only the reviewed manifest, without Git history or generated work."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

from check_release import PRIVATE_DIRS, ROOT, digest


def package(root, destination):
    root = root.resolve()
    if destination.exists():
        raise ValueError('Refusing to overwrite a release archive')
    subprocess.run([sys.executable, '-B', str(root / 'tools/check_release.py')], check=True)
    manifest_path = root / 'evidence/release-manifest.json'
    manifest_bytes = manifest_path.read_bytes()
    records = json.loads(manifest_bytes)['files']
    expected = {}
    for record in records:
        rel = Path(record['path'])
        if (rel.is_absolute() or '..' in rel.parts or rel.as_posix() != record['path']
                or any(part in PRIVATE_DIRS for part in rel.parts)
                or record['path'] in expected
                or record['path'] == 'evidence/release-manifest.json'):
            raise ValueError('Unsafe or duplicate manifest path')
        expected[record['path']] = record['sha256']
    expected['evidence/release-manifest.json'] = hashlib.sha256(manifest_bytes).hexdigest()
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.pack-', dir=destination.parent) as td:
        temporary = Path(td) / 'release.zip'
        prefix = 'Qiushi-Engine-Matmul-Research/'
        with zipfile.ZipFile(temporary, 'x', compression=zipfile.ZIP_DEFLATED,
                             compresslevel=6, allowZip64=True) as archive:
            for rel, value in sorted(expected.items()):
                source = root / rel
                if source.is_symlink() or not source.resolve().is_relative_to(root):
                    raise ValueError('Unsafe package source')
                if digest(source) != value:
                    raise ValueError('Release changed while packaging: ' + rel)
                archive.write(source, prefix + rel)
        with zipfile.ZipFile(temporary) as archive:
            if archive.testzip() or set(archive.namelist()) != {prefix + p for p in expected}:
                raise ValueError('Archive membership or CRC failure')
            for rel, value in expected.items():
                h = hashlib.sha256()
                with archive.open(prefix + rel) as stream:
                    for block in iter(lambda: stream.read(1 << 20), b''):
                        h.update(block)
                if h.hexdigest() != value or digest(root / rel) != value:
                    raise ValueError('Archive or source hash mismatch: ' + rel)
        # Hard-link publication refuses a destination created by another packer.
        os.link(temporary, destination)
    checksum = digest(destination)
    destination.with_suffix('.zip.sha256').write_text(checksum + '  ' + destination.name + '\n')
    return {'archive': str(destination), 'sha256': checksum,
            'files': len(expected), 'bytes': destination.stat().st_size}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=ROOT / 'dist/Qiushi-Engine-Matmul-Research.zip')
    args = parser.parse_args()
    print(json.dumps(package(ROOT, args.output.resolve())))


if __name__ == '__main__':
    main()
