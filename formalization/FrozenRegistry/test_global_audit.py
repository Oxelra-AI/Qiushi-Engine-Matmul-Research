"""Global replay bookkeeping; mathematical acceptance remains Lean compilation."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from frozen_registry import replay_roots, validate_global_audit


class GlobalAuditTests(unittest.TestCase):
    def setUp(self):
        self.log = ''.join('FROZEN_GLOBAL_AXIOMS QiushiMatmul.FrozenRegistry.' + name +
                           ': [propext, Classical.choice, Quot.sound]\n' for name in
                           ['all_representatives', 'L0_rank_sound', 'coverage_with_rank_bound'])
        self.log += 'FROZEN_GLOBAL_CHECKED 496\n'

    def test_complete_audit(self):
        validate_global_audit(self.log)

    def test_missing_duplicate_wrong_count_or_axiom(self):
        for log in [self.log.replace('L0_rank_sound', 'wrong_name'), self.log + self.log,
                    self.log.replace('496', '495'), self.log.replace('propext', 'untrusted')]:
            with self.subTest(log=log), self.assertRaises(ValueError):
                validate_global_audit(log)

    def test_full_replay_requires_global_guards(self):
        manifest = {'entries': [dict(index=i,
                    declaration=f'QiushiMatmul.FrozenRegistry.rep{i:03}') for i in range(496)]}
        self.assertEqual(replay_roots(manifest), ['FrozenRegistry.Bindings', 'FrozenRegistry.Tests',
                                                'FrozenRegistry.Remaining', 'FrozenRegistry.GlobalTests'])
        manifest['entries'].pop()
        self.assertEqual(replay_roots(manifest), ['FrozenRegistry.Bindings', 'FrozenRegistry.Tests'])


if __name__ == '__main__':
    unittest.main()
