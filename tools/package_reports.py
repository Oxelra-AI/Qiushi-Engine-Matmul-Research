#!/usr/bin/env python3
"""Build the unified report source ZIP and compare the rendered PDF text."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import zipfile

from build_reports import ROOT, TARGETS, check_pdf


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def dependencies(root, entry):
    """Resolve the report's explicit static TeX inputs, images and bibliography."""
    found, pending = set(), [entry]
    while pending:
        rel = Path(pending.pop())
        path = root / rel
        if (rel.is_absolute() or '..' in rel.parts or path.is_symlink()
                or not path.resolve().is_relative_to(root.resolve()) or not path.is_file()):
            raise ValueError('Missing, external or symbolic report dependency: ' + str(rel))
        if rel.as_posix() in found:
            continue
        found.add(rel.as_posix())
        if rel.suffix != '.tex':
            continue
        text = re.sub(r'(?<!\\)%[^\n]*', '', path.read_text())
        for command, value in re.findall(
                r'\\(input|include|includegraphics|bibliography)(?:\[[^\]]*\])?\{([^}]+)\}', text):
            if '\\' in value or '#' in value:
                raise ValueError('Dynamic report dependency needs explicit review')
            if command == 'includegraphics':
                pending.append(value)
            elif command == 'bibliography':
                pending.extend(name + '.bib' for name in value.split(','))
            else:
                pending.append(value if value.endswith('.tex') else value + '.tex')
    return sorted(found)


def verified_zip(path, payload):
    if path.exists():
        raise ValueError('Refusing to overwrite source archive')
    if any(Path(name).is_absolute() or '..' in Path(name).parts for name in payload):
        raise ValueError('Unsafe archive member')
    with zipfile.ZipFile(path, 'x', compression=zipfile.ZIP_DEFLATED, compresslevel=6) as archive:
        for name, data in sorted(payload.items()):
            info = zipfile.ZipInfo(name, date_time=(2026, 9, 10, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data)
    with zipfile.ZipFile(path) as archive:
        if archive.testzip() or set(archive.namelist()) != set(payload):
            raise ValueError('Archive integrity failure')
        if any(archive.read(name) != data for name, data in payload.items()):
            raise ValueError('Archive payload changed')


def package(stem, destination, language='en'):
    if language not in TARGETS:
        raise ValueError('Unsupported report language')
    directory = ROOT / 'reports' / language
    receipt = json.loads((ROOT / 'evidence/report-build.json').read_text())
    report = next(r for r in receipt['reports'] if r['pdf'] == f'reports/{language}/{stem}.pdf')
    for row in report['sources']:
        path = ROOT / row['path']
        if not path.is_file() or digest(path) != row['sha256']:
            raise ValueError('Report receipt is stale')
    if digest(ROOT / report['pdf']) != report['sha256']:
        raise ValueError('Published PDF differs from build receipt')
    files = dependencies(directory, stem + '.tex')
    payload = {name: (directory / name).read_bytes() for name in files}
    payload['LICENSE.txt'] = (ROOT / 'LICENSE').read_bytes()
    original_text = subprocess.check_output(
        ['pdftotext', '-layout', str(ROOT / report['pdf']), '-'], text=True).split()
    archive_stem = stem if language == 'en' else language
    output = destination / ('qiushi-matmul-' + archive_stem + '-source.zip')
    with tempfile.TemporaryDirectory(prefix='matmul-tex-') as td:
        tree = Path(td)
        for name, data in payload.items():
            target = tree / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        env = dict(os.environ, SOURCE_DATE_EPOCH='1788998400', FORCE_SOURCE_DATE='1',
                   TEXMFVAR=str(tree / '.texmf-var'))
        with (tree / 'standalone-build.log').open('w') as log:
            subprocess.run(['latexmk', '-xelatex', '-no-shell-escape',
                            '-interaction=nonstopmode', '-halt-on-error',
                            '-file-line-error', stem + '.tex'], cwd=tree, env=env,
                           stdout=log, stderr=subprocess.STDOUT, check=True, timeout=600)
        validation = check_pdf(tree / (stem + '.pdf'), tree / (stem + '.log'))
        text = subprocess.check_output(
            ['pdftotext', '-layout', str(tree / (stem + '.pdf')), '-'], text=True).split()
        if text != original_text:
            raise ValueError('Standalone PDF text differs from maintained report')
        payload[stem + '.bbl'] = (tree / (stem + '.bbl')).read_bytes()
        payload['README.txt'] = (
            'Qiushi Engine matrix multiplication report source\n\n'
            f'Master file: {stem}.tex\n'
            f'Build: latexmk -xelatex -no-shell-escape {stem}.tex\n'
            'Requires XeLaTeX, BibTeX, latexmk and standard TeX Live packages.\n'
            + ('Chinese edition additionally requires CTeX and Noto CJK fonts.\n'
               'On Ubuntu/Debian: texlive-lang-chinese and fonts-noto-cjk.\n'
               if language == 'zh' else '') +
            'No network access, model, research service or external figure path is needed.\n'
            'Original report and figures: CC BY 4.0; see LICENSE.txt.\n'
            'This source archive is not an arXiv submission receipt.\n'
        ).encode()
        verified_zip(output, payload)
    for name in files:
        if (directory / name).read_bytes() != payload[name]:
            raise ValueError('Source changed during packaging')
    if (ROOT / 'LICENSE').read_bytes() != payload['LICENSE.txt']:
        raise ValueError('License changed during packaging')
    return {'archive': output.name, 'sha256': digest(output),
            'bytes': output.stat().st_size, 'master': stem + '.tex',
            'files': [{'path': n, 'sha256': hashlib.sha256(b).hexdigest()}
                      for n, b in sorted(payload.items())],
            'standalone_pdf_text_matches': True, 'validation': validation}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'dist/report-sources')
    parser.add_argument('--language', choices=tuple(TARGETS) + ('all',), default='en')
    args = parser.parse_args()
    destination = args.output.resolve()
    destination.mkdir(parents=True, exist_ok=True)
    receipt = destination / 'source-packages.json'
    previous = json.loads(receipt.read_text()) if receipt.exists() else {}
    records = previous.get('packages', [])
    languages = TARGETS if args.language == 'all' else (args.language,)
    for language in languages:
        record = package('main', destination, language)
        records = [r for r in records if r['archive'] != record['archive']] + [record]
        records.sort(key=lambda r: r['archive'])
        print(json.dumps({k: record[k] for k in ('archive', 'bytes', 'standalone_pdf_text_matches')}),
              flush=True)
    receipt.write_text(json.dumps({
        'schema': 'qiushi.matmul.report-packages.v1',
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'arxiv_submitted': False, 'packages': records}, indent=2) + '\n')


if __name__ == '__main__':
    main()
