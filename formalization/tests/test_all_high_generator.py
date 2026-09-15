import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class AllHighGeneratorTests(unittest.TestCase):
    def test_regeneration_matches_checked_sources(self):
        with tempfile.TemporaryDirectory() as temporary:
            out = Path(temporary)
            subprocess.run(
                [sys.executable, str(ROOT / 'tools/generate_all_high_count.py'),
                 '--output', str(out)], check=True, capture_output=True, text=True)
            receipt = json.loads((out / 'generated-fixtures.json').read_text())
            self.assertEqual(receipt['status'], 'untrusted_until_lean_checked')
            self.assertEqual(receipt['first_codes'] * receipt['second_codes_per_row'],
                             512 * 512)
            self.assertEqual(receipt['shards'] * receipt['rows_per_shard'], 512)
            self.assertEqual(receipt['expected_total'], 192108)
            self.assertEqual(len(receipt['modules']), 34)
            for name in receipt['modules']:
                with self.subTest(module=name):
                    self.assertEqual((out / (name + '.lean')).read_bytes(),
                                     (ROOT / (name + '.lean')).read_bytes())


if __name__ == '__main__':
    unittest.main()
