import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('verify', ROOT / 'proof/verify_proof_package.py')
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)


class VerificationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.path = Path(self.tmp.name)
        self.package = self.path / 'proof'
        self.package.mkdir()
        self.patch = patch.object(verify, 'PACKAGE', self.package)
        self.patch.start()

    def tearDown(self):
        self.patch.stop()
        self.tmp.cleanup()

    def child(self, code, filename=None):
        output = filename or self.path / 'fresh.json'
        return verify.checked_json([sys.executable, '-c', code, str(output)],
                                   output, 'test.v1', 'all_ok', 3)

    def test_fresh_success(self):
        self.assertTrue(self.child("import json,sys; json.dump({'schema':'test.v1','all_ok':True},open(sys.argv[1],'w'))")['ok'])

    def test_old_success_is_not_read_or_overwritten(self):
        out = self.path / 'old.json'
        old = '{"schema":"test.v1","all_ok":true}'
        out.write_text(old)
        with patch.object(verify, 'run') as run:
            result = self.child('raise SystemExit(1)', out)
        self.assertFalse(result['ok'])
        run.assert_not_called()
        self.assertEqual(out.read_text(), old)

    def test_child_failure_with_fresh_success_json(self):
        self.assertFalse(self.child("import json,sys; json.dump({'schema':'test.v1','all_ok':True},open(sys.argv[1],'w')); sys.exit(1)")['ok'])

    def test_missing_output_after_zero_exit(self):
        self.assertFalse(self.child('pass')['ok'])

    def test_malformed_output(self):
        self.assertFalse(self.child("import sys; open(sys.argv[1],'w').write('broken')")['ok'])

    def test_wrong_schema(self):
        self.assertFalse(self.child("import json,sys; json.dump({'schema':'old','all_ok':True},open(sys.argv[1],'w'))")['ok'])

    def test_false_result(self):
        self.assertFalse(self.child("import json,sys; json.dump({'schema':'test.v1','all_ok':False},open(sys.argv[1],'w'))")['ok'])

    def test_missing_executable(self):
        self.assertFalse(verify.run([str(self.path / 'absent')], 1)['ok'])

    def test_timeout(self):
        result = verify.run([sys.executable, '-c', 'import time; time.sleep(10)'], 0.1)
        self.assertFalse(result['ok'])
        self.assertTrue(result['timed_out'])
        self.assertLess(result['elapsed_sec'], 2)

    def test_bad_manifest_stops_before_any_child(self):
        manifest = self.package / 'manifest.json'
        manifest.write_text(json.dumps({'files': [{'path': 'missing', 'sha256': '0' * 64}]}))
        with patch.object(verify, 'MANIFEST', manifest), patch.object(verify, 'run') as run:
            status = verify.main(['--replay-drat'])
        self.assertEqual(status, 1)
        run.assert_not_called()

    def test_empty_manifest_rejected(self):
        self.assertFalse(verify.check_manifest_hashes({'files': []})['ok'])

    def test_top_level_child_failure_cannot_reuse_legacy_success(self):
        legacy = self.package / 'verify_bundle_check.json'
        legacy.write_text('{"all_ok": true}')
        manifest = self.package / 'manifest.json'
        manifest.write_text(json.dumps({'files': [{'path': legacy.name,
                                                  'sha256': verify.sha256(legacy)}]}))
        out = self.path / 'result.json'
        with patch.object(verify, 'MANIFEST', manifest), patch.object(
                verify, 'run', return_value={'ok': False, 'returncode': 1}):
            status = verify.main(['--replay-drat', '--out', str(out)])
        result = json.loads(out.read_text())
        self.assertEqual(status, 1)
        self.assertFalse(result['all_ok'])
        self.assertFalse(result['bundle']['ok'])
        self.assertEqual(legacy.read_text(), '{"all_ok": true}')

    def test_traversal_rejected(self):
        self.assertFalse(verify.check_manifest_hashes({'files': [{'path': '../x', 'sha256': ''}]})['ok'])

    def test_lut_compile_failure_stops_pipeline(self):
        with patch.object(verify, 'run', return_value={'ok': False, 'returncode': 1}) as run:
            result = verify.reexpand(self.path)
        self.assertFalse(result['ok'])
        self.assertEqual(run.call_count, 1)

    def test_lut_run_failure_stops_before_compare(self):
        with patch.object(verify, 'run', side_effect=[{'ok': True, 'returncode': 0},
                                                     {'ok': False, 'returncode': 1}]) as run:
            result = verify.reexpand(self.path)
        self.assertFalse(result['ok'])
        self.assertEqual(run.call_count, 2)

    def test_proof_output_refused(self):
        with self.assertRaises(SystemExit) as stopped:
            verify.main(['--out', str(self.package / 'result.json')])
        self.assertEqual(stopped.exception.code, 2)


if __name__ == '__main__':
    unittest.main()
