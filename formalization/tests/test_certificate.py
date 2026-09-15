"""Regression checks for certificate preparation; Lean remains authoritative."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from generate_certificate import emit_checks, emit_data, emit_dispatch, names, rref, span
from source_graph import imports


def check_ray(meta, leaf):
    free = sorted(set(range(9)) - {b.bit_length() - 1 for b in rref(meta['basis'])})
    live = meta['live_list']
    sections = [sum(((q + 1) >> j & 1) << bit for j, bit in enumerate(free)) for q in live]
    index = {q: j for j, q in enumerate(live)}
    sources = {r['orig']: r for r in meta['source_rows']}
    total = [0] * len(live)
    rhs = 0
    for row in leaf['used_rows']:
        weight, kind = row['multiplier'], row['type']
        if not isinstance(weight, int) or weight < 0:
            raise ValueError('Invalid multiplier')
        coefficients = [0] * len(live)
        if kind == 'occ':
            source = sources[row['row']]
            coefficients = [int(c in span(source['basis'])) for c in sections]
            bound = meta['target'] - source['lb']
        elif kind == 'total_ge':
            coefficients = [-1] * len(live)
            bound = -meta['target']
        else:
            j = index[row['label'] - 1]
            if kind == 'nonneg':
                coefficients[j], bound = -1, 0
            elif kind == 'branch_upper':
                coefficients[j], bound = 1, row['bound']
            elif kind == 'branch_lower':
                coefficients[j], bound = -1, -row['bound']
            else:
                raise ValueError('Unsupported row')
        total = [a + weight * b for a, b in zip(total, coefficients)]
        rhs += weight * bound
    if any(total) or rhs >= 0:
        raise ValueError('Invalid Farkas contradiction')


class CertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        directory = ROOT / 'certificates/282'
        cls.meta = json.loads((directory / 'tables.json').read_text())
        cls.cert = json.loads((directory / 'branch.json').read_text())

    def test_row_reduction_is_canonical(self):
        for basis in ([5, 3], [258, 16, 10, 1], [19, 10]):
            self.assertEqual(span(basis), span(rref(basis)))
            self.assertEqual(rref(basis), rref(reversed(basis)))
            self.assertEqual(rref(basis), rref(span(basis)))

    def test_all_exact_rays(self):
        for leaf in self.cert['branch']['certs']:
            check_ray(self.meta, leaf)

    def test_all_large_certificate_rays(self):
        directory = ROOT / 'certificates/484'
        meta = json.loads((directory / 'tables.json').read_text())
        cert = json.loads((directory / 'branch.json').read_text())
        for leaf in cert['branch']['certs']:
            check_ray(meta, leaf)

    def test_corrupted_multiplier_is_rejected(self):
        leaf = copy.deepcopy(self.cert['branch']['certs'][0])
        leaf['used_rows'][0]['multiplier'] += 1
        with self.assertRaises(ValueError):
            check_ray(self.meta, leaf)

    def test_negative_multiplier_is_rejected(self):
        leaf = copy.deepcopy(self.cert['branch']['certs'][0])
        leaf['used_rows'][0]['multiplier'] = -1
        with self.assertRaises(ValueError):
            check_ray(self.meta, leaf)

    def test_nested_comment_imports_are_ignored(self):
        text = '/- import Wrong /- import AlsoWrong -/ -/\nimport Correct\n-- import Wrong'
        self.assertEqual(imports(text), ['Correct'])

    def test_invalid_block_width_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            for width in (0, -1):
                with self.assertRaises(ValueError):
                    emit_checks(self.meta, Path(directory), width=width)

    def test_missing_source_index_is_rejected(self):
        meta = copy.deepcopy(self.meta)
        meta['source_rows'].pop()
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(ValueError):
                emit_dispatch(meta, Path(directory))

    def test_missing_dead_witness_is_rejected(self):
        meta = copy.deepcopy(self.meta)
        meta['dead_witnesses'].pop()
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(ValueError):
                emit_dispatch(meta, Path(directory))

    def test_tag_changes_names_not_the_mathematical_instance(self):
        meta = dict(self.meta, name_tag='Lower')
        self.assertEqual(names(meta), ('plane282LowerGen', 'QiushiPlane282LowerGen'))
        self.assertEqual(meta['basis'], self.meta['basis'])
        for tag in ('../../X', 'Bad\nName', '123'):
            with self.assertRaises(ValueError):
                names(dict(meta, name_tag=tag))

    def test_empty_live_table_is_eliminated(self):
        meta = dict(self.meta, n_live=0, live_list=[])
        meta['dead_witnesses'] = [dict(basis=[256,128,64,32,16,8,4,2,1])]
        meta['n_dead'] = 1
        with tempfile.TemporaryDirectory() as directory:
            emit_data(meta, Path(directory))
            data = (Path(directory) / 'QiushiPlane282GenData.lean').read_text()
            self.assertIn('Section (i : Fin 0) : Fin 512 := Fin.elim0 i', data)

    def test_all_packaged_certificate_rays(self):
        for path in sorted((ROOT / 'certificates').glob('*/tables.json')):
            meta = json.loads(path.read_text())
            cert = json.loads(path.with_name('branch.json').read_text())
            with self.subTest(instance=path.parent.name):
                for leaf in cert['branch']['certs']:
                    check_ray(meta, leaf)


if __name__ == '__main__':
    unittest.main()
