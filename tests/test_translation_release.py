import ast
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import build_reports
import package_reports


class TranslationTests(unittest.TestCase):
    def test_translation_retains_sections_labels_citations_and_environments(self):
        for rel in ('main.tex', 'sections/research_process.tex',
                    'sections/research_record.tex', 'sections/comparison.tex'):
            en = (ROOT / 'reports/en' / rel).read_text()
            zh = (ROOT / 'reports/zh' / rel).read_text()
            with self.subTest(source=rel):
                for pattern in (r'\\label\{([^}]+)\}', r'\\cite\{([^}]+)\}',
                                r'\\(?:section|subsection|paragraph)\{',
                                r'\\begin\{(theorem|lemma|proposition|proof|figure|table|longtable|equation)\}'):
                    self.assertEqual(re.findall(pattern, en), re.findall(pattern, zh))
                self.assertGreater(len(re.findall(r'[\u4e00-\u9fff]', zh)), 300)
                self.assertNotRegex(zh, r'2026-09-04|9\s*月\s*4\s*日|4 September')

    def test_shared_assets_are_identical(self):
        for rel in ('refs.bib', 'latex/style.tex',
                    'figures/qiushi-engine-logo.png', 'figures/research_route.tex',
                    'figures/proof_structure.tex'):
            with self.subTest(asset=rel):
                self.assertEqual((ROOT / 'reports/en' / rel).read_bytes(),
                                 (ROOT / 'reports/zh' / rel).read_bytes())

    def test_bilingual_authors_preserve_order_and_four_row_layout(self):
        en = (ROOT / 'reports/en/latex/authors.tex').read_text()
        zh = (ROOT / 'reports/zh/latex/authors.tex').read_text()
        metadata = r'\\newcommand\{\\ReportAuthorNames\}\{([^}]+)\}'
        names = re.search(metadata, en).group(1).split(', ')
        self.assertEqual(re.search(metadata, zh).group(1).split(', '), names)
        block = zh.split(r'\begin{tabular*}', 1)[1].split(r'\end{tabular*}', 1)[0]
        rows = block.splitlines()[1:]
        self.assertEqual(len(rows), 4)
        self.assertTrue(all(row.count('&') == 3 for row in rows))
        pairs = re.findall(r'([\u4e00-\u9fff]+)（([A-Za-z ]+)）', block)
        self.assertEqual([name for _, name in pairs], names)
        self.assertEqual([name for name, _ in pairs], [
            '杨书行', '赵瑞', '吴俊尧', '汪易泽', '李文浩', '陈福家', '邓韬文', '洪沈展',
            '李亚琪', '李子晨', '密金城', '潘宇昂', '朱凯昊', '杨俊杰', '陈红胜', '杨怡豪',
        ])
        self.assertEqual(re.findall(r'（([A-Za-z ]+)）\\textsuperscript\{\*\}', block),
                         names[-2:])
        self.assertEqual(re.findall(r'mailto:([^}]+)', zh),
                         re.findall(r'mailto:([^}]+)', en))

    def test_translation_keeps_proof_table_and_critical_identities(self):
        en = (ROOT / 'reports/en/main.tex').read_text()
        zh = (ROOT / 'reports/zh/main.tex').read_text()
        for index in range(484, 492):
            rows = [next(line for line in text.splitlines()
                         if line.startswith(str(index) + ' &')) for text in (en, zh)]
            self.assertEqual(*rows)
        normalized = re.sub(r'\s|\\[,;!]|~', '', zh)
        for formula in (r'A_tB_sC_t^TA_s', r'M_tP^{-1}M_s=\delta_{ts}',
                        r'B_tC_t^T=A_t^{-1}', r'A_1B_2C_1^TA_2=0',
                        r'20\;\le\;R_{\FF}(\Tmmm)\;\le\;23',
                        r'21\le R_{\FF}(\Tmmm)\le23',
                        r'(U^TAV^{-T},\;V^TBH^{-T},\;U^{-1}CH)'):
            self.assertIn(re.sub(r'\s|\\[,;!]|~', '', formula), normalized)

    def test_both_reports_have_one_self_contained_master(self):
        for language in build_reports.TARGETS:
            directory = ROOT / 'reports' / language
            masters = [p.name for p in directory.rglob('*.tex')
                       if r'\documentclass' in p.read_text()]
            self.assertEqual(masters, ['main.tex'])
            files = package_reports.dependencies(directory, 'main.tex')
            for expected in ('refs.bib', 'latex/authors.tex', 'latex/preamble.tex',
                             'sections/research_record.tex', 'sections/comparison.tex',
                             'figures/proof_structure.tex', 'figures/research_route.tex'):
                self.assertIn(expected, files)
            self.assertFalse(any('..' in Path(name).parts for name in files))

    def test_chinese_metadata_and_keywords(self):
        zh = (ROOT / 'reports/zh/main.tex').read_text()
        self.assertIn(r'\date{2026年9月9日}', zh)
        self.assertIn(r'pdfauthor={\ReportAuthorNames}', zh)
        abstract = zh.split(r'\begin{abstract}', 1)[1].split(r'\end{abstract}', 1)[0]
        self.assertNotIn('Meta-Trace', abstract)
        self.assertNotIn(r'\cite', abstract)
        self.assertIn('独立形成', abstract)
        comparison = (ROOT / 'reports/zh/sections/comparison.tex').read_text()
        self.assertIn(r'\cite{wang2026twentyone}', comparison)
        self.assertIn('研究及科学报告完成之后', comparison)

    def test_chinese_headings_keep_technical_name_in_explanatory_text(self):
        main = (ROOT / 'reports/zh/main.tex').read_text()
        research = (ROOT / 'reports/zh/sections/research_process.tex').read_text()
        headings = re.findall(r'\\(?:section|subsection)\{([^}]+)\}', main + research)
        self.assertTrue(all('Meta-Trace' not in heading for heading in headings))
        self.assertIn(r'\subsection{研究记忆与证据}', research)
        self.assertIn(r'\section{研究历程与知识积累}', main)
        explanation = research.split(r'\subsection{研究记忆与证据}', 1)[1].split('\n\n')[1]
        self.assertIn('Meta-Trace', explanation)
        self.assertIn(r'\cite{yang2026optical}', explanation)
        self.assertIn('长程自主科学研究', explanation)

    def test_chinese_abstract_is_one_paragraph_with_background_and_contribution(self):
        main = (ROOT / 'reports/zh/main.tex').read_text()
        abstract = main.split(r'\begin{abstract}', 1)[1].split(
            r'\par\smallskip\noindent\textbf{关键词}', 1)[0].strip()
        self.assertNotRegex(abstract, r'\n\s*\n|\\par\b|\\\\')
        self.assertTrue(abstract.startswith('两个 $3\\times3$ 矩阵相乘'))
        for phrase in ('27 次', '23 次', '21 次', '精确双线性算法',
                       '二元域', '取等', '跨因子', '独立复验', '研究历程'):
            self.assertIn(phrase, abstract)
        self.assertNotIn(r'\cite', abstract)

    def test_chinese_first_paragraphs_share_standard_indentation(self):
        preamble = (ROOT / 'reports/zh/latex/preamble.tex').read_text()
        self.assertIn(r'\usepackage{indentfirst}', preamble)
        self.assertIn(r'\setlength{\parindent}{2em}', preamble)
        for level in ('section', 'subsection', 'subsubsection'):
            self.assertIn('\\titlespacing{\\' + level + '}', preamble)
            self.assertNotIn('\\titlespacing*{\\' + level + '}', preamble)
        self.assertIn(r'\textbf{摘要}\par\smallskip\indent', preamble)
        main = (ROOT / 'reports/zh/main.tex').read_text()
        self.assertEqual(main.count(r'\noindent'), 1)

    def test_targeted_build_preserves_other_language_receipt(self):
        for language, other in (('zh', 'en'), ('en', 'zh')):
            with self.subTest(language=language), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                (root / 'evidence').mkdir()
                receipt = root / 'evidence/report-build.json'
                old = {'target': other, 'pdf': f'reports/{other}/main.pdf', 'sha256': 'old'}
                receipt.write_text(json.dumps({'reports': [old]}))
                new = {'target': language, 'pdf': f'reports/{language}/main.pdf',
                       'sha256': 'new', 'validation': {}}
                with patch.object(build_reports, 'ROOT', root), \
                     patch.object(build_reports, 'build', return_value=new), \
                     patch.object(sys, 'argv', ['build_reports.py', '--language', language]), \
                     patch('builtins.print'):
                    build_reports.main()
                records = json.loads(receipt.read_text())['reports']
                self.assertIn(old, records)
                self.assertIn(new, records)
                before = receipt.read_bytes()
                with patch.object(build_reports, 'ROOT', root), \
                     patch.object(build_reports, 'build', return_value=new), \
                     patch.object(sys, 'argv', ['build_reports.py', '--language', language]), \
                     patch('builtins.print'):
                    build_reports.main()
                self.assertEqual(receipt.read_bytes(), before)

    def test_targeted_source_package_preserves_other_archive_receipt(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            receipt = root / 'source-packages.json'
            old = {'archive': 'qiushi-matmul-main-source.zip', 'sha256': 'old'}
            new = {'archive': 'qiushi-matmul-zh-source.zip', 'bytes': 10,
                   'standalone_pdf_text_matches': True}
            receipt.write_text(json.dumps({'packages': [old]}))
            with patch.object(package_reports, 'package', return_value=new) as package, \
                 patch.object(sys, 'argv', ['package_reports.py', '--language', 'zh',
                                           '--output', td]), patch('builtins.print'):
                package_reports.main()
            package.assert_called_once_with('main', root, 'zh', 'original')
            self.assertIn(old, json.loads(receipt.read_text())['packages'])

    def test_lean_build_preserves_original_receipt(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / 'evidence').mkdir()
            original = root / 'evidence/report-build.json'
            original.write_text(json.dumps({'reports': [{'pdf': 'reports/en/main.pdf'}]}))
            before = original.read_bytes()
            new = {'target': 'en', 'pdf': 'reports/en-lean/main.pdf',
                   'sha256': 'new', 'validation': {}}
            with patch.object(build_reports, 'ROOT', root), \
                 patch.object(build_reports, 'build', return_value=new) as build, \
                 patch.object(sys, 'argv', ['build_reports.py', '--edition', 'lean',
                                           '--language', 'en']), patch('builtins.print'):
                build_reports.main()
            build.assert_called_once_with('en', 'lean')
            self.assertEqual(original.read_bytes(), before)
            receipt = root / 'evidence/lean-report-build.json'
            self.assertEqual(json.loads(receipt.read_text())['reports'], [new])

    def test_explanatory_record_names_match_producers(self):
        materials = ROOT / 'research/materials'
        manifest = json.loads((materials / 'finite_certification/results/repeat_branch_certificate/certificate_manifest.json').read_text())
        self.assertEqual(manifest['supporting_records']['explanatory_note'],
                         'notes/repeated_core_certificate.md')
        source = (materials / 'finite_certification/code/make_certificate_manifest.py').read_text()
        ast.parse(source)
        self.assertIn("'explanatory_note':", source)
        result = json.loads((materials / 'exact_baselines/results/frontier_recheck/wang_latest_recheck.json').read_text())
        self.assertEqual(result['conclusion']['frontier_recheck_result'], 'needs_verification')
        fetch = (materials / 'quotient_cores/code/fetch_wang_latest.py').read_text()
        ast.parse(fetch)
        self.assertIn("else 'needs_verification'", fetch)
        resolved = json.loads((materials / 'exact_baselines/results/frontier_recheck/wang_v11_resolved.json').read_text())
        self.assertIn('frontier_recheck_result=needs_verification', resolved['note'])


if __name__ == '__main__':
    unittest.main()
