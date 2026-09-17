from collections import Counter
import hashlib
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


class ResearchMaterialsTests(unittest.TestCase):
    def test_catalog_is_an_exact_material_inventory(self):
        catalog = json.loads((ROOT / 'research/catalog.json').read_text())
        paths = set()
        for row in catalog['files']:
            relative = Path(row['path'])
            self.assertFalse(relative.is_absolute())
            self.assertNotIn('..', relative.parts)
            self.assertEqual(relative.parts[:2], ('research', 'materials'))
            self.assertNotIn(row['path'], paths)
            paths.add(row['path'])
            data = (ROOT / relative).read_bytes()
            self.assertEqual(len(data), row['bytes'], row['path'])
            self.assertEqual(hashlib.sha256(data).hexdigest(), row['sha256'], row['path'])
            self.assertEqual(row['status'], 'historical')
            for reference in row.get('references', []):
                self.assertTrue((ROOT / reference).is_file(), reference)
        self.assertEqual(Counter(r['kind'] for r in catalog['files']), catalog['counts'])
        self.assertEqual(set(catalog['counts']), {'notes', 'plans', 'code', 'results', 'arrays'})
        expected = {p.relative_to(ROOT).as_posix()
                    for topic in (ROOT / 'research/materials').iterdir() if topic.is_dir()
                    for kind in topic.iterdir() if kind.is_dir()
                    for p in kind.rglob('*') if p.is_file()}
        self.assertEqual(paths, expected)

    def test_coverage_and_catalog_agree(self):
        data = (ROOT / 'research/catalog.json').read_bytes()
        catalog = json.loads(data)
        coverage = json.loads((ROOT / 'evidence/research-coverage.json').read_text())
        self.assertEqual(coverage['catalog_sha256'], hashlib.sha256(data).hexdigest())
        self.assertEqual(coverage['artifacts'], len(catalog['files']))
        self.assertEqual(coverage['by_kind'], catalog['counts'])
        self.assertFalse(coverage['all_historical_experiments_rerun'])
        self.assertFalse(coverage['mathematical_proof_payloads_modified'])

    def test_historical_notes_keep_their_status(self):
        catalog = json.loads((ROOT / 'research/catalog.json').read_text())
        for row in catalog['files']:
            if row['kind'] in {'notes', 'plans'}:
                self.assertIn('Historical research record.', (ROOT / row['path']).read_text())
        withdrawals = list((ROOT / 'research/materials').rglob('proof_r_f2_ge_21.md'))
        self.assertEqual(len(withdrawals), 1)
        self.assertIn('proof note is invalid', withdrawals[0].read_text().lower())
        self.assertIn('CardEnc', withdrawals[0].read_text())

    def test_metadata_records_match_published_proof_inputs(self):
        coverage = json.loads((ROOT / 'evidence/research-coverage.json').read_text())
        caches = json.loads((ROOT / coverage['cache_metadata']).read_text())
        self.assertTrue(caches['mathematical_payload_unchanged'])
        for row in caches['caches']:
            self.assertEqual(hashlib.sha256((ROOT / row['path']).read_bytes()).hexdigest(),
                             row['sha256'])
            self.assertTrue(row['all_other_encoded_bytes_unchanged'])
            self.assertTrue((ROOT / 'proof' / row['public_certificate_path']).is_file())
        proof = json.loads((ROOT / coverage['proof_input_metadata']).read_text())
        self.assertEqual(hashlib.sha256((ROOT / proof['path']).read_bytes()).hexdigest(),
                         proof['sha256'])
        self.assertTrue(proof['mathematical_values_encoding_logic_and_proof_bytes_unchanged'])
        self.assertTrue(proof['data_equal_except_check_labels_and_cache_hashes'])

    def test_paths_work_on_case_insensitive_filesystems(self):
        catalog = json.loads((ROOT / 'research/catalog.json').read_text())
        paths = [r['path'] for r in catalog['files']]
        self.assertEqual(len(paths), len(set(p.casefold() for p in paths)))
        self.assertTrue(all(len('Qiushi-Engine-Matmul-Research/' + p) <= 240 for p in paths))


if __name__ == '__main__':
    unittest.main()
