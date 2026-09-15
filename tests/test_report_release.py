import importlib.util
import json
from pathlib import Path
import re
import sys
import subprocess
import tempfile
import unittest
import zipfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import package_reports
import build_reports


class ReportReleaseTests(unittest.TestCase):
    def test_lean_reports_are_self_contained_and_source_matched(self):
        receipt = json.loads((ROOT / 'evidence/lean-report-build.json').read_text())
        self.assertEqual({r['pdf'] for r in receipt['reports']},
                         {'reports/en-lean/main.pdf', 'reports/zh-lean/main.pdf'})
        for record in receipt['reports']:
            self.assertEqual(build_reports.digest(ROOT / record['pdf']), record['sha256'])
            for source in record['sources']:
                self.assertEqual(build_reports.digest(ROOT / source['path']), source['sha256'])
        for language in ('en', 'zh'):
            directory = ROOT / 'reports' / (language + '-lean')
            files = package_reports.dependencies(directory, 'main.tex')
            self.assertIn('sections/research_record.tex', files)
            self.assertIn('latex/authors.tex', files)
            for part in ('latex/authors.tex', 'refs.bib', 'figures/proof_structure.tex',
                         'figures/research_route.tex'):
                self.assertEqual((directory / part).read_bytes(),
                                 (ROOT / 'reports' / language / part).read_bytes())
            text = (directory / 'main.tex').read_text()
            self.assertIn(r'\subsection{Lean', text)
            self.assertIn(r'\texttt{bilinear\_mul\_requires\_21}', text)

    def test_lean_edition_has_separate_sources_and_receipt(self):
        for language in ('en', 'zh'):
            self.assertEqual(build_reports.report_directory(language),
                             ROOT / 'reports' / language)
            self.assertEqual(build_reports.report_directory(language, 'lean'),
                             ROOT / 'reports' / (language + '-lean'))
        self.assertEqual(build_reports.report_receipt(), ROOT / 'evidence/report-build.json')
        self.assertEqual(build_reports.report_receipt('lean'),
                         ROOT / 'evidence/lean-report-build.json')

    def test_unknown_report_edition_rejected(self):
        with self.assertRaises(ValueError):
            build_reports.report_directory('en', '../private')
        with self.assertRaises(ValueError):
            build_reports.report_directory('../private', 'lean')

    def test_keywords_describe_research_topics(self):
        main = (ROOT / 'reports/en/main.tex').read_text()
        abstract = main.split(r'\begin{abstract}', 1)[1].split(r'\end{abstract}', 1)[0]
        keywords = abstract.split(r'\textbf{Keywords}\quad', 1)[1]
        terms = [' '.join(term.split()) for term in keywords.split(';')]
        self.assertEqual(terms, [
            'Matrix multiplication', 'tensor rank', 'bilinear complexity',
            'finite fields', 'computer-assisted proof',
            'autonomous mathematical research',
        ])
        self.assertNotIn('Meta-Trace', abstract)

    def test_research_attribution_without_start_date(self):
        directory = ROOT / 'reports/en'
        paths = [directory / 'main.tex', *(directory / 'sections').glob('*.tex'),
                 ROOT / 'README.md', ROOT / 'README.zh-CN.md']
        for path in paths:
            with self.subTest(path=path.name):
                self.assertNotRegex(path.read_text(),
                                    r'4 September|September 4|2026-09-04|9\s*月\s*4\s*日')
        main = (directory / 'main.tex').read_text()
        self.assertIn(r'\date{9 September 2026}', main)
        self.assertIn('Qiushi Engine independently developed the argument', main)
        process = (directory / 'sections/research_process.tex').read_text()
        self.assertIn('carried out the mathematical research end to end', process)
        comparison = (directory / 'sections/comparison.tex').read_text()
        self.assertIn('after the research and scientific report had been completed', comparison)
        self.assertIn(r'\cite{wang2026twentyone}', comparison)

    def test_contemporaneous_comparison_is_only_in_the_appendix(self):
        directory = ROOT / 'reports/en'
        main = (directory / 'main.tex').read_text()
        comparison = '\\input{sections/comparison}'
        self.assertGreater(main.index(comparison), main.index('\\appendix'))
        self.assertGreater(main.index(comparison), main.index('\\input{sections/research_record}'))
        citations = [p.relative_to(directory).as_posix() for p in directory.rglob('*.tex')
                     if 'wang2026twentyone' in p.read_text()]
        self.assertEqual(citations, ['sections/comparison.tex'])
        self.assertNotIn('tab:comparison', main)
        note = (directory / 'sections/comparison.tex').read_text()
        self.assertIn('\\label{app:comparison}', note)
        self.assertLess(len(note.split()), 650)
        for aspect in ('Finite premises', 'After coset reduction',
                       'Decisive deduction', 'Verification', 'Further results',
                       'Research development and open materials'):
            self.assertIn(aspect, note)

    def test_citations_follow_first_appearance(self):
        directory = ROOT / 'reports/en'
        main = (directory / 'main.tex').read_text()
        for name in ('research_process', 'research_record', 'comparison'):
            main = main.replace(r'\input{sections/' + name + '}',
                                (directory / 'sections' / (name + '.tex')).read_text())
        keys = [key.strip() for group in re.findall(r'\\cite\{([^}]+)\}', main)
                for key in group.split(',')]
        first = list(dict.fromkeys(keys))
        self.assertEqual(first[:2], ['laderman1976noncommutative', 'heule2019waysa'])
        self.assertIn(r'\bibliographystyle{unsrtnat}', main)
        self.assertIn(r'\usepackage[numbers,sort&compress]{natbib}',
                      (directory / 'latex/preamble.tex').read_text())
        bibliography = (directory / 'refs.bib').read_text()
        available = re.findall(r'@\w+\s*\{\s*([^,]+),', bibliography)
        self.assertEqual(len(available), len(set(available)))
        self.assertTrue(set(first).issubset(available))
        self.assertEqual(len(re.findall(r'^\s*url\s*=\s*\{https://',
                                        bibliography, re.MULTILINE)), len(available))

    def test_key_equations_are_numbered_and_references_resolve(self):
        directory = ROOT / 'reports/en'
        main = (directory / 'main.tex').read_text()
        preamble = (directory / 'latex/preamble.tex').read_text()
        self.assertIn(r'\numberwithin{equation}{section}', preamble)
        labels = re.findall(r'\\label\{([^}]+)\}', main)
        self.assertEqual(len(labels), len(set(labels)))
        for label in ('eq:tensor', 'eq:occ', 'eq:decomp', 'eq:rksum',
                      'eq:profile', 'eq:idempotent', 'eq:product', 'eq:diagonal',
                      'eq:general-decomposition', 'eq:coefficient-action',
                      'eq:finite-proof-implication', 'eq:off-diagonal-zero'):
            self.assertRegex(main, r'\\begin\{equation\}\s*\\label\{' + label + r'\}')
        for label in re.findall(r'\\eqref\{([^}]+)\}', main):
            self.assertIn(label, labels)

    def test_public_system_description_and_integrated_meta_trace(self):
        directory = ROOT / 'reports/en'
        process = (directory / 'sections/research_process.tex').read_text()
        self.assertIn('hierarchical multi-agent research system', process)
        self.assertIn(r'\cite{yang2026optical}', process)
        bibliography = (directory / 'refs.bib').read_text()
        self.assertIn('2604.27092', bibliography)
        main = (directory / 'main.tex').read_text()
        self.assertIn(r'\section{Meta-Trace: Development of the Research}', main)
        self.assertIn(r'\input{sections/research_record}', main)
        for name in ('README.md', 'README.zh-CN.md', 'research/README.md'):
            self.assertIn('Meta-Trace', (ROOT / name).read_text())

    def test_meta_trace_definition_sources_and_first_citation(self):
        directory = ROOT / 'reports/en'
        main = (directory / 'main.tex').read_text()
        abstract = main.split(r'\begin{abstract}', 1)[1].split(r'\end{abstract}', 1)[0]
        self.assertIn('A documented research trajectory', abstract)
        self.assertNotIn(r'\cite', abstract)
        process = (directory / 'sections/research_process.tex').read_text()
        self.assertIn(r'Meta-Trace~\cite{yang2026optical}', process)
        for phrase in ('structured record of the research process',
                       "Qiushi Engine's memory system", 'Layered summaries and retrieval',
                       r'\emph{history}', r'\emph{evidence}', r'\emph{trajectory}',
                       'synthesis of the original Meta-Trace records'):
            self.assertIn(phrase, process)
        guide = (ROOT / 'research/guide.md').read_text()
        self.assertIn('## Reading the Source Materials', guide)
        links = re.findall(r'\]\((materials/[^)#]+)\)', guide)
        self.assertGreaterEqual(len(set(links)), 12)
        for link in links:
            self.assertTrue((ROOT / 'research' / link).is_file(), link)

    def test_research_terminology_in_maintained_narrative(self):
        directory = ROOT / 'reports/en'
        paths = [directory / 'main.tex', *(directory / 'sections').glob('*.tex'),
                 ROOT / 'README.md', ROOT / 'research/README.md',
                 ROOT / 'research/guide.md', directory / 'README.md']
        for path in paths:
            self.assertNotRegex(path.read_text().lower(), r'\binvestigat\w*')
        self.assertIn('autonomous mathematical research',
                      ' '.join((directory / 'main.tex').read_text().split()))

    def test_file_digests_stay_out_of_scientific_narrative(self):
        directory = ROOT / 'reports/en'
        paths = [directory / 'main.tex', *(directory / 'sections').glob('*.tex')]
        for path in paths:
            with self.subTest(path=path.name):
                self.assertNotRegex(path.read_text(), r'\b[0-9a-fA-F]{64}\b|SHA-?256')

    def test_sources_are_self_contained(self):
        for stem in ('main',):
            files = package_reports.dependencies(ROOT / 'reports/en', stem + '.tex')
            self.assertIn('latex/authors.tex', files)
            self.assertIn('figures/qiushi-engine-logo.png', files)
            self.assertIn('refs.bib', files)
            self.assertNotIn('sn-nature.bst', files)
            self.assertFalse(any('..' in Path(p).parts for p in files))

    def test_source_archive_carries_reuse_terms(self):
        source = (ROOT / 'tools/package_reports.py').read_text()
        self.assertIn("payload['LICENSE.txt'] = (ROOT / 'LICENSE').read_bytes()", source)
        license_text = (ROOT / 'LICENSE').read_text()
        self.assertIn('MIT License', license_text)
        self.assertIn('creativecommons.org/licenses/by/4.0/legalcode.en', license_text)
        self.assertNotIn('have not yet selected', license_text)

    def test_main_archive_contains_integrated_record(self):
        files = package_reports.dependencies(ROOT / 'reports/en', 'main.tex')
        self.assertNotIn('supplement.tex', files)
        self.assertIn('sections/research_record.tex', files)

    def test_only_one_master_and_build_target(self):
        directory = ROOT / 'reports/en'
        masters = [p.name for p in directory.rglob('*.tex')
                   if '\\documentclass' in p.read_text()]
        self.assertEqual(masters, ['main.tex'])
        self.assertEqual(set(build_reports.TARGETS), {'en', 'zh'})
        self.assertFalse((directory / 'supplement.pdf').exists())
        record = (directory / 'sections/research_record.tex').read_text()
        self.assertEqual(record.count('\\subsection{'), 13)
        self.assertNotIn('\\section{', record)
        main = (directory / 'main.tex').read_text()
        self.assertLess(main.index('\\input{sections/research_record}'),
                        main.index('\\bibliography{refs}'))
        files = package_reports.dependencies(directory, 'main.tex')
        joined = '\n'.join((directory / p).read_text() for p in files if p.endswith('.tex'))
        self.assertEqual(joined.count('\\maketitle'), 1)
        self.assertEqual(main.count('\\tableofcontents'), 1)
        self.assertEqual(joined.count('\\bibliography{refs}'), 1)
        self.assertEqual(joined.count('\\input{figures/research_route}'), 1)

    def test_dependency_traversal_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)
            (p / 'main.tex').write_text('\\input{../private}')
            with self.assertRaises(ValueError):
                package_reports.dependencies(p, 'main.tex')

    def test_symlink_dependency_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)
            (p / 'real.tex').write_text('safe')
            (p / 'main.tex').symlink_to(p / 'real.tex')
            with self.assertRaises(ValueError):
                package_reports.dependencies(p, 'main.tex')

    def test_dynamic_dependency_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)
            (p / 'main.tex').write_text('\\input{\\privatepath}')
            with self.assertRaises(ValueError):
                package_reports.dependencies(p, 'main.tex')

    def test_zip_is_portable_and_exact(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / 'source.zip'
            package_reports.verified_zip(p, {'main.tex': b'proof', 'figures/x.tex': b'figure'})
            with zipfile.ZipFile(p) as z:
                self.assertIsNone(z.testzip())
                self.assertEqual(z.read('main.tex'), b'proof')
                self.assertTrue(all('\\' not in n for n in z.namelist()))

    def test_zip_rejects_traversal_and_overwrite(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / 'source.zip'
            with self.assertRaises(ValueError):
                package_reports.verified_zip(p, {'../private': b'x'})
            package_reports.verified_zip(p, {'main.tex': b'x'})
            with self.assertRaises(ValueError):
                package_reports.verified_zip(p, {'main.tex': b'y'})

    def test_author_order_and_correspondence(self):
        text = (ROOT / 'reports/en/latex/authors.tex').read_text()
        names = ['Shuxing Yang', 'Rui Zhao', 'Junyao Wu', 'Yize Wang',
                 'Wenhao Li', 'Fujia Chen', 'Taowen Deng', 'Shenzhan Hong',
                 'Yaqi Li', 'Zichen Li', 'Jincheng Mi', 'Yuang Pan',
                 'Kaihao Zhu', 'Junjie Yang', 'Hongsheng Chen', 'Yihao Yang']
        positions = [text.index(name) for name in names]
        self.assertEqual(positions, sorted(positions))
        metadata = re.search(r'\\newcommand\{\\ReportAuthorNames\}\{([^}]+)\}', text)
        self.assertIsNotNone(metadata)
        self.assertEqual(metadata.group(1).split(', '), names)
        main = (ROOT / 'reports/en/main.tex').read_text()
        self.assertIn(r'pdfauthor={\ReportAuthorNames}', main)
        info = subprocess.check_output(['pdfinfo', str(ROOT / 'reports/en/main.pdf')], text=True)
        actual = re.search(r'^Author:\s*(.+)$', info, re.MULTILINE)
        self.assertIsNotNone(actual)
        self.assertEqual(actual.group(1).split(', '), names)
        self.assertIn('Hongsheng Chen\\textsuperscript{*}', text)
        self.assertIn('Yihao Yang\\textsuperscript{*}', text)
        self.assertIn('yangyihao@zju.edu.cn', text)
        self.assertIn('hansomchen@zju.edu.cn', text)
        citation = (ROOT / 'CITATION.cff').read_text()
        positions = [citation.index('given-names: ' + name.rsplit(' ', 1)[0])
                     for name in names]
        self.assertEqual(positions, sorted(positions))

    def test_no_editorial_author_confirmation(self):
        for name in ('reports/en/README.md', 'reports/en/latex/authors.tex'):
            text = (ROOT / name).read_text().lower()
            self.assertNotIn('confirmed by', text)
            self.assertNotIn('project owner', text)

    def test_primary_table_counts_match_bundled_files(self):
        main = (ROOT / 'reports/en/main.tex').read_text()
        for index in range(484, 492):
            row = next(line for line in main.splitlines() if line.startswith(str(index) + ' &'))
            cells = row.split('&')
            base = ROOT / 'proof/assets/occupation/data/dim2_cnf_cert_all' / f'orbit_{index}'
            with (base / f'orbit_{index}_target_18.cnf').open() as stream:
                header = next(line.split() for line in stream if line.startswith('p cnf '))
            numbers = [int(re.sub(r'[^0-9]', '', cells[i])) for i in (4, 5)]
            self.assertEqual(numbers, list(map(int, header[2:])))
            size = (base / f'orbit_{index}_target_18.drat').stat().st_size / (1 << 20)
            self.assertEqual(float(re.search(r'[0-9]+\.[0-9]+', cells[6]).group()), round(size, 1))


if __name__ == '__main__':
    unittest.main()
