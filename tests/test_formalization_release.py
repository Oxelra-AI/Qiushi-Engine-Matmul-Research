import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import check_formalization


class FormalizationReleaseTests(unittest.TestCase):
    def fixture(self, root):
        (root / 'Main.lean').write_text('theorem identity (n : Nat) : n = n := rfl\n')
        (root / 'lakefile.toml').write_text('[[lean_lib]]\nname="Proof"\nroots=["Main"]\n')
        (root / 'lean-toolchain').write_text('leanprover/lean4:test\n')
        (root / 'lake-manifest.json').write_text(json.dumps({
            'packages': [{'name': 'mathlib', 'rev': 'test'}]}))
        (root / 'verification.json').write_text(json.dumps({
            'groups': [{'id': 'main', 'roots': ['identity']}]}))
        digest = check_formalization.sha256
        receipt = {'status': 'pass', 'checked_on': '2026-09-15',
                   'toolchain': 'leanprover/lean4:test', 'mathlib_revision': 'test',
                   'axioms': ['propext', 'Classical.choice', 'Quot.sound'],
                   'terminal_roots': 1,
                   'root_manifest_sha256': digest((root / 'verification.json').read_bytes()),
                   'source_build': {'status': 'pass', 'registered_modules': 1, 'compiled_modules': 1,
                       'source_digest': digest(json.dumps({'Main': digest((root / 'Main.lean').read_bytes())},
                                                        separators=(',', ':')).encode())},
                   'groups': [{'id': 'main', 'roots': 1, 'status': 'pass'}]}
        (root / 'verification-results.json').write_text(json.dumps(receipt))
        return receipt

    def publication_fixture(self, root):
        receipt = self.fixture(root)
        digest = check_formalization.sha256
        old = digest((root / 'Main.lean').read_bytes())
        with (root / 'Main.lean').open('a') as stream:
            stream.write('-- Mathematical identity.\n')
        new = digest((root / 'Main.lean').read_bytes())
        mapping = {
            'schema': 'qiushi.matmul.publication-source-map.v1', 'status': 'pass',
            'original_acceptance': {
                'sha256': digest((root / 'verification-results.json').read_bytes()),
                'source_digest': receipt['source_build']['source_digest']},
            'publication_source': {
                'source_digest': check_formalization.source_identity({'Main': new}),
                'registered_modules': 1, 'changed_modules': 1,
                'noncomment_characters_identical': True},
            'compilation': {'all_changed_modules_compiled': True,
                            'toolchain': receipt['toolchain'], 'mathlib_revision': 'test'},
            'object_comparison': {'kernel_payload_identical': 1},
            'changed_modules': [{'module': 'Main', 'source_sha256_before': old,
                'source_sha256_after': new, 'compile_exit_code': 0,
                'kernel_payload_identical': True, 'olean_byte_identical': True,
                'olean_sha256_before': 'a' * 64, 'olean_sha256_after': 'a' * 64}],
            'interface_checks': [{'group': 'main', 'roots': 1,
                'exact_types_and_axioms_identical': True, 'allowed_axioms': receipt['axioms']}]}
        (root / 'publication-source-map.json').write_text(json.dumps(mapping))
        return mapping

    def test_comment_map_preserves_the_accepted_record(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            self.publication_fixture(root)
            before = (root / 'verification-results.json').read_bytes()
            result = check_formalization.inspect(root)
            self.assertIn('comment-only', result['source_relation'])
            self.assertEqual((root / 'verification-results.json').read_bytes(), before)

    def test_comment_map_rejects_failed_compile_or_changed_proof(self):
        for field, value in [('compile_exit_code', 1), ('kernel_payload_identical', False),
                             ('olean_sha256_after', 'b' * 64),
                             ('changed_metadata_extensions', ['unknown-extension'])]:
            with self.subTest(field=field), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                mapping = self.publication_fixture(root)
                mapping['changed_modules'][0][field] = value
                (root / 'publication-source-map.json').write_text(json.dumps(mapping))
                with self.assertRaises(ValueError):
                    check_formalization.inspect(root)

    def test_comment_map_rejects_unrecorded_source_change(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            self.publication_fixture(root)
            (root / 'Main.lean').write_text('theorem different : True := True.intro\n')
            with self.assertRaisesRegex(ValueError, 'publication source map'):
                check_formalization.inspect(root)

    def test_comment_map_rejects_unmatched_predecessor(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mapping = self.publication_fixture(root)
            mapping['changed_modules'][0]['source_sha256_before'] = 'c' * 64
            (root / 'publication-source-map.json').write_text(json.dumps(mapping))
            with self.assertRaisesRegex(ValueError, 'reconstruct'):
                check_formalization.inspect(root)

    def test_matches_sources_without_claiming_a_new_replay(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            self.fixture(root)
            result = check_formalization.inspect(root)
            self.assertEqual(result['registered_modules'], 1)
            self.assertEqual(result['lean_lines'], 1)
            self.assertIn('not a new proof replay', result['scope'])

    def test_modified_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            self.fixture(root)
            (root / 'Main.lean').write_text('theorem different : True := True.intro\n')
            with self.assertRaisesRegex(ValueError, 'sources do not match'):
                check_formalization.inspect(root)

    def test_incomplete_receipt_is_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            receipt = self.fixture(root)
            receipt['groups'][0]['status'] = 'timeout'
            (root / 'verification-results.json').write_text(json.dumps(receipt))
            with self.assertRaisesRegex(ValueError, 'incomplete'):
                check_formalization.inspect(root)

    def test_changed_pin_is_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            self.fixture(root)
            (root / 'lean-toolchain').write_text('different\n')
            with self.assertRaisesRegex(ValueError, 'pins changed'):
                check_formalization.inspect(root)


if __name__ == '__main__':
    unittest.main()
