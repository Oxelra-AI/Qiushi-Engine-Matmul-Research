#!/usr/bin/env python3
"""Render README images from the report's existing TikZ sources and typography."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from build_reports import ROOT, digest

FIGURES = ('proof_structure', 'research_route')


def main():
    directory = ROOT / 'reports/en'
    base = ROOT / 'build/figures'
    base.mkdir(parents=True, exist_ok=True)
    records = []
    for name in FIGURES:
        output = Path(tempfile.mkdtemp(prefix=name + '-', dir=base))
        sources = [directory / 'figures' / (name + '.tex'),
                   directory / 'latex/preamble.tex', directory / 'latex/style.tex']
        hashes = {str(p.relative_to(ROOT)): digest(p) for p in sources}
        wrapper = output / 'figure.tex'
        wrapper.write_text(
            '\\documentclass[11pt,a4paper]{article}\n'
            '\\input{latex/preamble}\n\\pagestyle{empty}\n'
            '\\begin{document}\n\\centering\n'
            '\\input{figures/' + name + '}\n\\end{document}\n')
        env = dict(os.environ, SOURCE_DATE_EPOCH='1788998400', FORCE_SOURCE_DATE='1')
        with (output / 'render.log').open('w') as log:
            subprocess.run(['xelatex', '-no-shell-escape', '-interaction=nonstopmode',
                            '-halt-on-error', '-output-directory=' + str(output), str(wrapper)],
                           cwd=directory, env=env, stdout=log, stderr=subprocess.STDOUT,
                           check=True, timeout=120)
            subprocess.run(['pdfcrop', '--margins', '10', str(output / 'figure.pdf'),
                            str(output / 'cropped.pdf')], stdout=log, stderr=subprocess.STDOUT,
                           check=True, timeout=60)
        subprocess.run(['pdftoppm', '-singlefile', '-r', '160', '-png',
                        str(output / 'cropped.pdf'), str(output / name)],
                       check=True, timeout=60)
        if any(digest(ROOT / p) != h for p, h in hashes.items()):
            raise ValueError('Figure source changed during rendering')
        target = directory / 'figures' / (name + '.png')
        temporary = target.with_suffix('.png.tmp')
        shutil.copyfile(output / (name + '.png'), temporary)
        temporary.replace(target)
        records.append({'image': str(target.relative_to(ROOT)),
                        'sha256': digest(target), 'sources': hashes})
    (ROOT / 'evidence/figures.json').write_text(json.dumps({
        'schema': 'qiushi.matmul.figure-render.v1', 'figures': records}, indent=2) + '\n')
    print(json.dumps({'rendered': [r['image'] for r in records]}))


if __name__ == '__main__':
    main()
