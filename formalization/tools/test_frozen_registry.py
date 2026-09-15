"""Focused tests for replay bookkeeping, independent of the Lean installation."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import frozen_registry as registry


class RegistryTests(unittest.TestCase):
    def setUp(self):
        self.manifest = {'entries': [{
            'index': 1, 'declaration': 'QiushiMatmul.FrozenRegistry.rep001'}]}
        self.log = (
            'REGISTRY_TYPE QiushiMatmul.FrozenRegistry.rep001: bound\n'
            'REGISTRY_AXIOMS QiushiMatmul.FrozenRegistry.rep001: '
            '[propext, Classical.choice, Quot.sound]\n'
            'REGISTRY_CHECKED 1\n')

    def test_complete_audit(self):
        self.assertEqual(registry.validate_audit(self.manifest, self.log), 1)

    def test_missing_duplicate_or_wrong_count(self):
        for log in [self.log.replace('REGISTRY_TYPE', 'MISSING_TYPE'),
                    self.log + self.log, self.log.replace('CHECKED 1', 'CHECKED 2')]:
            with self.subTest(log=log), self.assertRaises(ValueError):
                registry.validate_audit(self.manifest, log)

    def test_unexpected_axiom(self):
        with self.assertRaises(ValueError):
            registry.validate_audit(self.manifest, self.log.replace('propext', 'untrusted'))

    def test_wrong_index_or_declaration(self):
        for index in [-1, 496, 2]:
            manifest = copy.deepcopy(self.manifest)
            manifest['entries'][0]['index'] = index
            with self.subTest(index=index), self.assertRaises(ValueError):
                registry.checked_names(manifest)
        duplicate = copy.deepcopy(self.manifest)
        duplicate['entries'] *= 2
        with self.assertRaises(ValueError):
            registry.checked_names(duplicate)

    def test_output_separation(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            root, out = base / 'source', base / 'output'
            registry.check_output(root, out, [base / 'imports'])
            for imports in [[out / 'lib'], [out], [out / 'lib/nested']]:
                with self.subTest(imports=imports), self.assertRaises(ValueError):
                    registry.check_output(root, out, imports)
            with self.assertRaises(ValueError):
                registry.check_output(root, base, [])

    def test_failed_replay_does_not_reuse_receipt(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / 'source'
            (root / 'FrozenRegistry').mkdir(parents=True)
            (root / 'FrozenRegistry/checked.json').write_text(json.dumps(self.manifest))
            out = Path(tmp) / 'output'
            out.mkdir()
            receipt = out / 'checkpoint.json'
            receipt.write_text('{"checked": 999}')
            with patch.object(registry, 'build', return_value=[{'exit_code': 1}]):
                self.assertFalse(registry.replay(root, Path('unused.json'), [], out))
            self.assertFalse(receipt.exists())

    def test_binary_span_discovery(self):
        self.assertEqual(registry.span([1, 2]), registry.span([1, 3]))
        self.assertNotEqual(registry.span([96, 2, 1]), registry.span([272, 4, 1]))
        self.assertTrue(registry.span([]) <= registry.span([1]))


if __name__ == '__main__':
    unittest.main()
