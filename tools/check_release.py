#!/usr/bin/env python3
"""Check the exact public snapshot without consulting private research records."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
IDENTIFIERS = re.compile(r'\bS[0-9]{4}A[0-9]{2}\b|\b[Ss]tep[ _-]*[0-9]+\b')
PRIVATE_DIRS = {'.git', 'build', 'dist', '.venv', '__pycache__', '.lake', '.local', 'paper'}
GENERATED_SUFFIXES = {'.pyc', '.aux', '.bbl', '.blg', '.fls', '.fdb_latexmk', '.out', '.toc',
                      '.olean', '.ilean', '.ir'}


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def public_files(root):
    files = set()
    for directory, dirs, names in os.walk(root, followlinks=False):
        dirs[:] = [name for name in dirs if name not in PRIVATE_DIRS]
        for name in list(dirs):
            path = Path(directory) / name
            if path.is_symlink():
                files.add(path.relative_to(root).as_posix())
                dirs.remove(name)
        for name in names:
            path = Path(directory) / name
            if (name not in PRIVATE_DIRS and path.suffix not in GENERATED_SUFFIXES
                    and not name.endswith(('.olean.private', '.olean.server'))):
                files.add(path.relative_to(root).as_posix())
    return files


def membership_failures(root, expected):
    actual = public_files(root)
    return (['unlisted public file: ' + p for p in sorted(actual - expected)]
            + ['missing public file: ' + p for p in sorted(expected - actual)])


def local_links(text):
    return (re.findall(r'\[[^\]\n]+\]\(([^)\s]+)\)', text)
            + re.findall(r'<(?:img|a)\b[^>]*\b(?:src|href)=[\"\x27]([^\"\x27]+)', text))


def main():
    manifest = json.loads((ROOT / 'evidence/release-manifest.json').read_text())
    failures, seen = [], set()
    for row in manifest['files']:
        rel = Path(row['path'])
        path = ROOT / rel
        if (rel.is_absolute() or '..' in rel.parts or row['path'] in seen
                or any(part in PRIVATE_DIRS for part in rel.parts)
                or path.is_symlink() or not path.resolve().is_relative_to(ROOT)):
            failures.append('unsafe or duplicate path')
            continue
        seen.add(row['path'])
        if not path.is_file() or digest(path) != row['sha256'] or path.stat().st_size != row['bytes']:
            failures.append('missing or changed: ' + row['path'])
    failures.extend(membership_failures(ROOT, seen | {'evidence/release-manifest.json'}))
    for language in ('en', 'zh', 'en-lean', 'zh-lean'):
        text = subprocess.check_output(
            ['pdftotext', '-layout', str(ROOT / 'reports' / language / 'main.pdf'), '-'],
            text=True)
        if IDENTIFIERS.search(text):
            failures.append('internal research identifier in rendered ' + language)
    if any((ROOT / 'reports' / lang / ('supplement.' + ext)).exists()
           for lang in ('en', 'zh', 'en-lean', 'zh-lean') for ext in ('tex', 'pdf')):
        failures.append('obsolete standalone supplement must not be in the unified release')
    if (ROOT / 'meta-trace').exists():
        failures.append('raw transcript directory must not be in this release')
    for rel in sorted(p for p in seen if p.endswith('.md')):
        guide = ROOT / rel
        if not guide.is_file():
            continue
        for link in local_links(guide.read_text()):
            if '://' in link or link.startswith(('#', 'mailto:')):
                continue
            target = (guide.parent / link.split('#')[0]).resolve()
            if not target.is_relative_to(ROOT) or not target.exists():
                failures.append('broken link in ' + str(guide.relative_to(ROOT)))
    figure_receipt = ROOT / 'evidence/figures.json'
    if figure_receipt.exists():
        for record in json.loads(figure_receipt.read_text())['figures']:
            identities = dict(record['sources'], **{record['image']: record['sha256']})
            for rel, expected in identities.items():
                if rel not in seen or not (ROOT / rel).is_file() or digest(ROOT / rel) != expected:
                    failures.append('stale figure or source: ' + rel)
    from audit_public import audit
    privacy = audit(ROOT)
    failures.extend('public content: ' + row['path'] + ' (' + row['rule'] + ')'
                    for row in privacy['failures'])
    result = {'schema': 'qiushi.matmul.public-check.v1',
              'all_ok': not failures, 'hashed_files': len(seen),
              'raw_transcripts_included': False,
              'publication_approved': False, 'failures': failures}
    output = ROOT / 'build/public-check.json'
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
    return 0 if not failures else 1


if __name__ == '__main__':
    raise SystemExit(main())
