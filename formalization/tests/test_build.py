"""Scheduler tests use a fake compiler; they make no Lean verification claim."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import tomllib
import unittest

BUILD = Path(__file__).resolve().parents[1] / 'tools/build.py'


class BuildTests(unittest.TestCase):
    def run_build(self, bad=False, batch=2, jobs=4, resume=False, cache_good=True,
                  selection=None, lakefile=None, extra_sources=None):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'lake-manifest.json').write_text('{}')
            sources = {'Base': '', 'Left': 'import Base', 'Right': 'import Base',
                       'Top': 'import Left\nimport Right'}
            sources.update(extra_sources or {})
            for name, contents in sources.items():
                path = root / Path(*name.split('.')).with_suffix('.lean')
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(contents)
            if lakefile is not None:
                (root / 'lakefile.toml').write_text(lakefile)
            fake = root / 'fake-lake'
            fake.write_text(
                '#!' + sys.executable + '\nimport sys\n'
                + ('\nif "--no-build" in sys.argv: sys.exit(9)\n' if not cache_good else '')
                + ('sys.exit(3 if "+Left:olean" in sys.argv else 0)\n' if bad
                   else 'sys.exit(0)\n'))
            fake.chmod(0o755)
            command = [sys.executable, str(BUILD), str(root),
                '--lake', str(fake), '--jobs', str(jobs),
                '--batch-size', str(batch)]
            command += ['--root', 'Top'] if selection is None else selection
            if resume:
                receipt = root / 'previous.json'
                receipt.write_text(json.dumps([{'module': 'Base', 'returncode': 0}]))
                command += ['--resume-from', str(receipt)]
            result = subprocess.run(command, capture_output=True, text=True)
            receipts = list((root / '.local').glob('build-*/results.json'))
            records = json.loads(receipts[0].read_text()) if receipts else []
            return result, records

    def test_independent_nodes_are_batched(self):
        result, records = self.run_build()
        self.assertEqual(result.returncode, 0, result.stderr)
        by_name = {r['module']: r for r in records}
        self.assertEqual(by_name['Left']['batch'], ['Left', 'Right'])
        self.assertEqual(by_name['Top']['batch'], ['Top'])
        self.assertEqual([r['module'] for r in records][0], 'Base')
        self.assertEqual([r['module'] for r in records][-1], 'Top')

    def test_failed_batch_never_reports_partial_success(self):
        result, records = self.run_build(bad=True)
        self.assertNotEqual(result.returncode, 0)
        by_name = {r['module']: r for r in records}
        self.assertEqual(by_name['Left']['returncode'], 3)
        self.assertEqual(by_name['Right']['returncode'], 3)
        self.assertEqual(by_name['Top']['returncode'], 125)

    def test_single_module_mode_is_retained(self):
        result, records = self.run_build(batch=1)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(all(len(r['batch']) == 1 for r in records))

    def test_invalid_batch_sizes_are_rejected(self):
        for batch in (0, -1, 5):
            result, records = self.run_build(batch=batch)
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(records)

    def test_resume_requires_successful_lake_cache_validation(self):
        result, records = self.run_build(resume=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(next(r for r in records if r['module'] == 'Base')['cache_revalidated'])

    def test_invalid_cache_is_rebuilt_not_accepted(self):
        result, records = self.run_build(resume=True, cache_good=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn('cache_revalidated', next(r for r in records if r['module'] == 'Base'))

    def test_all_includes_unrelated_standalone_registered_roots(self):
        result, records = self.run_build(
            selection=['--all'], extra_sources={'tests.Standalone': ''},
            lakefile='defaultTargets = ["Top"]\n'
                     '[[lean_lib]]\nname = "Main"\nroots = ["Top"]\n'
                     '[[lean_lib]]\nname = "Checks"\nroots = ["tests.Standalone", "Top"]\n')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual({r['module'] for r in records},
                         {'Base', 'Left', 'Right', 'Top', 'tests.Standalone'})
        self.assertEqual(len(records), 5)

    def test_all_and_root_are_mutually_exclusive(self):
        for selection in (['--all', '--root', 'Top'], ['--root', 'Top', '--all']):
            with self.subTest(selection=selection):
                result, records = self.run_build(selection=selection)
                self.assertEqual(result.returncode, 2)
                self.assertIn('not allowed with argument', result.stderr)
                self.assertFalse(records)

    def test_all_rejects_empty_or_missing_registrations(self):
        for lakefile in ('', 'lean_lib = []', '[[lean_lib]]\nname = "Main"',
                         '[[lean_lib]]\nroots = []'):
            with self.subTest(lakefile=lakefile):
                result, records = self.run_build(selection=['--all'], lakefile=lakefile)
                self.assertEqual(result.returncode, 2)
                self.assertIn('nonempty', result.stderr)
                self.assertFalse(records)

    def test_all_rejects_malformed_registrations(self):
        for lakefile in ('[[lean_lib]', 'lean_lib = "Main"',
                         '[lean_lib]\nroots = ["Top"]',
                         'lean_lib = [1]', '[[lean_lib]]\nroots = "Top"',
                         '[[lean_lib]]\nroots = [1]', '[[lean_lib]]\nroots = [""]',
                         '[[lean_lib]]\nroots = ["tests..Standalone"]',
                         '[[lean_lib]]\nroots = ["/Top"]'):
            with self.subTest(lakefile=lakefile):
                result, records = self.run_build(selection=['--all'], lakefile=lakefile)
                self.assertEqual(result.returncode, 2)
                self.assertFalse(records)
                self.assertNotIn('Traceback', result.stderr)

    def test_all_rejects_missing_config_and_source(self):
        result, records = self.run_build(selection=['--all'])
        self.assertEqual(result.returncode, 2)
        self.assertIn('Cannot read lakefile.toml', result.stderr)
        self.assertFalse(records)
        result, records = self.run_build(selection=['--all'],
            lakefile='[[lean_lib]]\nroots = ["Top", "tests.Missing"]')
        self.assertEqual(result.returncode, 2)
        self.assertIn('Root module does not exist: tests.Missing', result.stderr)
        self.assertFalse(records)

    def test_default_root_is_unchanged_without_config(self):
        result, records = self.run_build(selection=[],
            extra_sources={'QiushiMatmul': 'import Top', 'tests.Standalone': ''})
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual({r['module'] for r in records},
                         {'Base', 'Left', 'Right', 'Top', 'QiushiMatmul'})

    def fresh_build(self, missing_output=False):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'lake-manifest.json').write_text('{}')
            (root / 'Top.lean').write_text('import Base')
            (root / 'Base.lean').write_text('')
            fake_lean = root / 'fake-lean'
            fake_lean.write_text('#!' + sys.executable + '\n'
                'import os,resource,sys\nfrom pathlib import Path\n'
                'assert sys.argv[1] == "--threads=1", sys.argv\n'
                'soft,_=resource.getrlimit(resource.RLIMIT_STACK)\n'
                'assert soft == resource.RLIM_INFINITY or soft >= 256*1024*1024\n'
                'out=Path(sys.argv[sys.argv.index("-o")+1])\n'
                'assert str(out.parent) == os.environ["LEAN_PATH"].split(":")[0]\n'
                'assert "/.lake/build/lib/lean" not in os.environ["LEAN_PATH"]\n'
                'assert "-s262144" in sys.argv\n'
                + ('\n' if missing_output else 'out.write_text("test artifact")\n'))
            fake_lean.chmod(0o755)
            fake_lake = root / 'fake-lake'
            config = {'lean': str(fake_lean), 'path': ':'.join([
                str(root / '.lake/build/lib/lean'),
                str(root / '.lake/packages/mathlib/objects')])}
            fake_lake.write_text('#!' + sys.executable + '\nprint(' +
                                 repr(json.dumps(config)) + ')\n')
            fake_lake.chmod(0o755)
            result = subprocess.run([sys.executable, str(BUILD), str(root),
                '--root', 'Top', '--lake', str(fake_lake), '--jobs', '2',
                '--fresh-lean'], capture_output=True, text=True)
            outputs = list((root / '.local').glob('build-*/lib/*.olean'))
            return result, sorted(p.name for p in outputs)

    def test_fresh_build_excludes_old_project_artifacts(self):
        result, outputs = self.fresh_build()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(outputs, ['Base.olean', 'Top.olean'])

    def test_fresh_build_rejects_missing_outputs(self):
        result, outputs = self.fresh_build(missing_output=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(outputs)

    def test_lake_compiler_threads_match_fresh_build(self):
        config = tomllib.loads((BUILD.parents[1] / 'lakefile.toml').read_text())
        self.assertIn('--threads=1', config['moreLeanArgs'])


if __name__ == '__main__':
    unittest.main()
