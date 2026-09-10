#!/usr/bin/env python3
"""Build maintained reports, with fresh output and source-bound receipts."""
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

ROOT = Path(__file__).resolve().parents[1]
TARGETS = {
    'en': ('en', 'main', 'xelatex'),
    'zh': ('zh', 'main', 'xelatex'),
}
BAD_LOG = re.compile(
    r'Overfull \\[hv]box|Missing character:|'
    r'LaTeX Warning: (?:Citation|Reference).*undefined|'
    r'There were undefined references|There were multiply-defined labels|'
    r'LaTeX Font Warning|Package fontspec Warning')


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def source_files(directory):
    return sorted(p for p in directory.rglob('*')
                  if p.is_file() and p.suffix in ('.tex', '.bib', '.bst', '.png'))


def check_pdf(pdf, log):
    warnings = [line for line in log.read_text(errors='replace').splitlines()
                if BAD_LOG.search(line)]
    if warnings:
        raise ValueError('TeX validation failed:\n' + '\n'.join(warnings))
    fonts = subprocess.check_output(['pdffonts', str(pdf)], text=True)
    font_rows = fonts.splitlines()[2:]
    if not font_rows or any(row.split()[-5] != 'yes' for row in font_rows if row.strip()):
        raise ValueError('PDF fonts are missing or not embedded')
    if any('Type 3' in row for row in font_rows):
        raise ValueError('Type 3 bitmap font found')
    content = subprocess.check_output(['pdftotext', '-layout', str(pdf), '-'], text=True)
    if len(content.split()) < 500 or '\ufffd' in content:
        raise ValueError('Empty, short or malformed report text')
    return {'embedded_fonts': len(font_rows), 'word_tokens': len(content.split()),
            'layout_and_reference_warnings': 0}


def build(target):
    language, stem, engine = TARGETS[target]
    directory = ROOT / 'reports' / language
    base = ROOT / 'build/reports' / target
    base.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix='render-', dir=base))
    sources = [{'path': str(p.relative_to(ROOT)), 'sha256': digest(p)}
               for p in source_files(directory)]
    for row in sources:
        source = ROOT / row['path']
        target_path = output / source.relative_to(directory)
        target_path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target_path)
    env = dict(os.environ, TEXMFVAR=str(ROOT / 'build/texmf-var'),
               SOURCE_DATE_EPOCH='1788998400', FORCE_SOURCE_DATE='1')
    command = ['latexmk', '-' + engine, '-no-shell-escape', '-interaction=nonstopmode',
               '-halt-on-error', '-file-line-error', stem + '.tex']
    # Relative input/output names keep xdvipdfmx's trailer ID independent of the checkout.
    with (output / 'build.log').open('w') as log:
        subprocess.run(command, cwd=output, env=env, check=True, timeout=600,
                       stdout=log, stderr=subprocess.STDOUT)
    pdf = output / (stem + '.pdf')
    validation = check_pdf(pdf, output / (stem + '.log'))
    if any(digest(ROOT / row['path']) != row['sha256'] for row in sources):
        raise ValueError('Report sources changed during rendering')
    published = directory / (stem + '.pdf')
    temporary = published.with_suffix('.pdf.tmp')
    shutil.copyfile(pdf, temporary)
    temporary.replace(published)
    return {'target': target, 'engine': engine,
            'pdf': str(published.relative_to(ROOT)), 'bytes': published.stat().st_size,
            'sha256': digest(published), 'sources': sources, 'validation': validation,
            'build_directory': str(output.relative_to(ROOT))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--language', choices=tuple(TARGETS) + ('all',), default='all')
    args = parser.parse_args()
    receipt = ROOT / 'evidence/report-build.json'
    previous = json.loads(receipt.read_text()) if receipt.exists() else {}
    records = previous.get('reports', [])
    targets = TARGETS if args.language == 'all' else (args.language,)
    for target in targets:
        record = build(target)
        records = [r for r in records if r['pdf'] != record['pdf']] + [record]
        records.sort(key=lambda r: r['pdf'])
        # A reproducible rebuild should not invalidate the frozen release manifest.
        if report_identities(previous.get('reports', [])) != report_identities(records):
            receipt.write_text(json.dumps({
                'schema': 'qiushi.matmul.report-build.v1',
                'checked_at_utc': datetime.now(timezone.utc).isoformat(),
                'scope': 'Rendering and source integrity; not publication approval',
                'reports': records}, indent=2) + '\n')
        print(json.dumps({k: record[k] for k in ('target', 'pdf', 'validation')}),
              flush=True)


def report_identities(records):
    return [{k: v for k, v in record.items() if k != 'build_directory'}
            for record in records]


if __name__ == '__main__':
    main()
