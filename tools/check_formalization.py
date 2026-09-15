#!/usr/bin/env python3
"""Match released Lean sources to the completed verification record; no replay."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import tomllib


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def source_identity(sources):
    return sha256(json.dumps(sources, sort_keys=True, separators=(',', ':')).encode())


def check_publication_map(project, sources, receipt, receipt_raw):
    mapping = json.loads((project / 'publication-source-map.json').read_text())
    accepted, published = mapping['original_acceptance'], mapping['publication_source']
    compilation, objects = mapping['compilation'], mapping['object_comparison']
    rows = mapping['changed_modules']
    if (mapping['schema'] != 'qiushi.matmul.publication-source-map.v1'
            or mapping['status'] != 'pass' or accepted['sha256'] != sha256(receipt_raw)
            or accepted['source_digest'] != receipt['source_build']['source_digest']
            or published['source_digest'] != source_identity(sources)
            or published['registered_modules'] != len(sources)
            or published['changed_modules'] != len(rows) or not rows
            or published['noncomment_characters_identical'] is not True
            or compilation['all_changed_modules_compiled'] is not True
            or compilation['toolchain'] != receipt['toolchain']
            or compilation['mathlib_revision'] != receipt['mathlib_revision']
            or objects['kernel_payload_identical'] != len(rows)):
        raise ValueError('inconsistent publication source map')
    previous, seen = dict(sources), set()
    allowed_metadata = {'Lean.Linter.lintLogExt', 'Lean.docStringExt',
                        '_private.Lean.DocString.Extension.0.Lean.moduleDocExt'}
    for row in rows:
        name = row['module']
        if (name in seen or name not in sources
                or row['source_sha256_after'] != sources[name]
                or not re.fullmatch(r'[0-9a-f]{64}', row['source_sha256_before'])
                or row['source_sha256_before'] == row['source_sha256_after']
                or row['compile_exit_code'] != 0
                or row['kernel_payload_identical'] is not True
                or not set(row.get('changed_metadata_extensions', [])) <= allowed_metadata):
            raise ValueError('unverified publication module: ' + name)
        if row['olean_byte_identical']:
            if row['olean_sha256_before'] != row['olean_sha256_after']:
                raise ValueError('contradictory object identity: ' + name)
        elif not re.fullmatch(r'[0-9a-f]{64}', row['kernel_payload_sha256_before_and_after']):
            raise ValueError('missing kernel payload identity: ' + name)
        seen.add(name)
        previous[name] = row['source_sha256_before']
    if source_identity(previous) != accepted['source_digest']:
        raise ValueError('publication map does not reconstruct the accepted source set')
    interfaces = mapping['interface_checks']
    if (len(interfaces) != len(receipt['groups'])
            or {r['group']: r['roots'] for r in interfaces}
            != {r['id']: r['roots'] for r in receipt['groups']}
            or any(r['exact_types_and_axioms_identical'] is not True
                   or set(r['allowed_axioms']) != set(receipt['axioms']) for r in interfaces)):
        raise ValueError('publication interfaces do not match the accepted roots')
    return 'comment-only publication map; identical compiled kernel payloads'


def inspect(project):
    project = project.resolve()
    config = tomllib.loads((project / 'lakefile.toml').read_text())
    receipt_raw = (project / 'verification-results.json').read_bytes()
    receipt = json.loads(receipt_raw)
    manifest_raw = (project / 'verification.json').read_bytes()
    manifest = json.loads(manifest_raw)
    names = [name for library in config['lean_lib'] for name in library['roots']]
    if len(names) != len(set(names)) or not names:
        raise ValueError('empty or duplicate registered modules')
    sources, lines, total_bytes = {}, 0, 0
    for name in sorted(names):
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', name):
            raise ValueError('invalid module name')
        path = project.joinpath(*name.split('.')).with_suffix('.lean')
        if path.is_symlink() or not path.resolve().is_relative_to(project):
            raise ValueError('source is not a regular project file: ' + name)
        raw = path.read_bytes()
        sources[name] = sha256(raw)
        lines += len(raw.splitlines())
        total_bytes += len(raw)
    identity = source_identity(sources)
    built = receipt['source_build']
    if (built['status'] != 'pass' or built['registered_modules'] != len(names)
            or built['compiled_modules'] != len(names)):
        raise ValueError('sources do not match the accepted source build')
    relation = 'exact accepted source bytes'
    if built['source_digest'] != identity:
        if not (project / 'publication-source-map.json').is_file():
            raise ValueError('sources do not match the accepted source build')
        relation = check_publication_map(project, sources, receipt, receipt_raw)
    if receipt['root_manifest_sha256'] != sha256(manifest_raw):
        raise ValueError('terminal-root manifest changed')
    pin = (project / 'lean-toolchain').read_text().strip()
    dependencies = json.loads((project / 'lake-manifest.json').read_text())['packages']
    mathlib = next(p for p in dependencies if p['name'] == 'mathlib')
    if pin != receipt['toolchain'] or mathlib['rev'] != receipt['mathlib_revision']:
        raise ValueError('accepted dependency pins changed')
    expected = {group['id']: len(group['roots']) for group in manifest['groups']}
    actual = receipt['groups']
    roots = [root for group in manifest['groups'] for root in group['roots']]
    if (receipt['status'] != 'pass' or len(actual) != len(expected)
            or {group['id']: group['roots'] for group in actual} != expected
            or any(group['status'] != 'pass' for group in actual)
            or len(roots) != len(set(roots)) or receipt['terminal_roots'] != len(roots)
            or set(receipt['axioms']) != {'propext', 'Classical.choice', 'Quot.sound'}):
        raise ValueError('incomplete or inconsistent verification record')
    return {'status': 'pass', 'scope': 'source and verification-record consistency; not a new proof replay',
            'registered_modules': len(names), 'lean_lines': lines, 'lean_bytes': total_bytes,
            'terminal_roots': len(roots), 'accepted_groups': len(expected),
            'source_digest': identity, 'source_relation': relation,
            'checked_on': receipt['checked_on']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'formalization')
    args = parser.parse_args()
    try:
        result = inspect(args.project)
    except (OSError, ValueError, KeyError, TypeError, StopIteration) as error:
        print(json.dumps({'status': 'fail', 'error': str(error)}))
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
