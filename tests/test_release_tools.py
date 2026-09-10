import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import zipfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import build_reports
import check_release
import package_release


def manifest(root, paths):
    rows = [{'path': p, 'sha256': check_release.digest(root / p),
             'bytes': (root / p).stat().st_size} for p in paths]
    (root / 'evidence').mkdir(exist_ok=True)
    (root / 'evidence/release-manifest.json').write_text(json.dumps({'files': rows}))


class ReleaseToolsTests(unittest.TestCase):
    def test_exact_inventory_rejects_unlisted_file(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / 'README.md').write_text('public')
            (root / 'private-notes.txt').write_text('not approved')
            self.assertEqual(check_release.membership_failures(root, {'README.md'}),
                             ['unlisted public file: private-notes.txt'])

    def test_inventory_prunes_generated_and_private_directories(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            for name in check_release.PRIVATE_DIRS:
                (root / name).mkdir()
                (root / name / 'internal.txt').write_text('excluded')
            (root / 'README.md').write_text('public')
            self.assertEqual(check_release.public_files(root), {'README.md'})

    def test_symlink_directory_is_not_followed(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / 'outside-link').symlink_to(ROOT, target_is_directory=True)
            self.assertEqual(check_release.public_files(root), {'outside-link'})

    def test_markdown_and_html_links(self):
        links = check_release.local_links(
            '[Report](reports/main.pdf) <img src="figures/a.png" width="500"> '
            "<a href='proof/README.md'>Proof</a>")
        self.assertEqual(links, ['reports/main.pdf', 'figures/a.png', 'proof/README.md'])

    def test_checker_rejects_stale_figure_receipt(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / 'evidence').mkdir()
            (root / 'figure.tex').write_text('revised source')
            (root / 'figure.png').write_bytes(b'old render')
            receipt = {'figures': [{'image': 'figure.png',
                       'sha256': check_release.digest(root / 'figure.png'),
                       'sources': {'figure.tex': '0' * 64}}]}
            (root / 'evidence/figures.json').write_text(json.dumps(receipt))
            manifest(root, ['figure.tex', 'figure.png', 'evidence/figures.json'])
            with patch.object(check_release, 'ROOT', root), \
                    patch.object(check_release.subprocess, 'check_output', return_value='Report'), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(check_release.main(), 1)
            result = json.loads((root / 'build/public-check.json').read_text())
            self.assertIn('stale figure or source: figure.tex', result['failures'])

    def test_report_identity_ignores_only_build_location(self):
        a = [{'sha256': 'a', 'sources': ['source'], 'build_directory': 'build/one'}]
        b = [{'sha256': 'a', 'sources': ['source'], 'build_directory': 'build/two'}]
        self.assertEqual(build_reports.report_identities(a), build_reports.report_identities(b))
        b[0]['sha256'] = 'b'
        self.assertNotEqual(build_reports.report_identities(a), build_reports.report_identities(b))
        b[0]['sha256'] = 'a'
        b[0]['sources'] = ['changed-source']
        self.assertNotEqual(build_reports.report_identities(a), build_reports.report_identities(b))

    def test_scientific_cover_date_is_separate_from_build_receipt(self):
        source = (ROOT / 'reports/en/main.tex').read_text()
        self.assertIn('\\date{9 September 2026}', source)
        receipt = json.loads((ROOT / 'evidence/report-build.json').read_text())
        self.assertIn('checked_at_utc', receipt)

    def test_report_build_uses_relative_names_in_a_source_snapshot(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            directory = root / 'reports/en'
            directory.mkdir(parents=True)
            (directory / 'main.tex').write_text('report source')

            def compile_snapshot(command, *, cwd, **kwargs):
                self.assertEqual(command[-1], 'main.tex')
                self.assertFalse(any(arg.startswith('-outdir=') for arg in command))
                self.assertNotEqual(cwd, directory)
                self.assertEqual((cwd / 'main.tex').read_text(), 'report source')
                (cwd / 'main.pdf').write_bytes(b'fresh compiled PDF')

            with patch.object(build_reports, 'ROOT', root), \
                    patch.object(build_reports.subprocess, 'run', compile_snapshot), \
                    patch.object(build_reports, 'check_pdf', return_value={'checked': True}):
                result = build_reports.build('en')
            self.assertEqual((directory / 'main.pdf').read_bytes(), b'fresh compiled PDF')
            self.assertEqual(result['sources'][0]['path'], 'reports/en/main.tex')

    def test_package_contains_only_manifest_payloads(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / 'README.md').write_text('reviewed content')
            (root / '.git').mkdir()
            (root / '.git/private').write_text('private history')
            manifest(root, ['README.md'])
            output = root / 'dist/release.zip'
            with patch.object(package_release.subprocess, 'run'):
                result = package_release.package(root, output)
            with zipfile.ZipFile(output) as archive:
                self.assertIsNone(archive.testzip())
                self.assertEqual(len(archive.namelist()), 2)
                self.assertEqual(archive.read('Qiushi-Engine-Matmul-Research/README.md'),
                                 b'reviewed content')
            self.assertEqual(result['sha256'], check_release.digest(output))
            self.assertEqual(result['files'], 2)
            self.assertTrue(output.with_suffix('.zip.sha256').is_file())
            with self.assertRaises(ValueError):
                package_release.package(root, output)

    def test_package_rejects_failed_precheck(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            output = root / 'release.zip'
            with patch.object(package_release.subprocess, 'run',
                              side_effect=subprocess.CalledProcessError(1, ['check'])):
                with self.assertRaises(subprocess.CalledProcessError):
                    package_release.package(root, output)
            self.assertFalse(output.exists())

    def test_package_rejects_changed_source_without_publishing(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / 'README.md').write_text('original')
            manifest(root, ['README.md'])
            original_write = zipfile.ZipFile.write

            def change_after_write(archive, filename, *args, **kwargs):
                original_write(archive, filename, *args, **kwargs)
                if Path(filename).name == 'README.md':
                    Path(filename).write_text('concurrent change')

            output = root / 'dist/release.zip'
            with patch.object(package_release.subprocess, 'run'), \
                    patch.object(zipfile.ZipFile, 'write', change_after_write):
                with self.assertRaises(ValueError):
                    package_release.package(root, output)
            self.assertFalse(output.exists())

    def test_package_rejects_traversal_in_manifest(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / 'evidence').mkdir()
            (root / 'evidence/release-manifest.json').write_text(json.dumps({
                'files': [{'path': 'x/../README.md', 'sha256': '0' * 64}]}))
            with patch.object(package_release.subprocess, 'run'):
                with self.assertRaises(ValueError):
                    package_release.package(root, root / 'dist/release.zip')


if __name__ == '__main__':
    unittest.main()
