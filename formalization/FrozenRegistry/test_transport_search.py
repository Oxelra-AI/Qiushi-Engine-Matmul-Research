"""Discovery regression tests; formal acceptance is in TransportBindings.lean."""
import unittest
import numpy as np

from transport_search import actions, canonical_rows, coefficient_spaces, packed, packed_rows, rref, search


class TransportSearchTests(unittest.TestCase):
    def test_vectorized_normal_form(self):
        _, _, _, table, _ = actions()
        for basis in [[1], [1, 2], [96, 2, 1], [256, 64, 16, 4, 1]]:
            sample = table[::113, basis]
            normal = canonical_rows(sample)
            self.assertEqual([tuple(row) for row in normal], [rref(row) for row in sample])

    def test_coefficient_spaces(self):
        for n, d, count in [(2, 1, 3), (3, 1, 7), (4, 2, 35), (7, 5, 2667)]:
            rows = coefficient_spaces(n, d)
            self.assertEqual(len(rows), count)
            self.assertEqual(len({tuple(row) for row in rows}), count)
            self.assertTrue(all(tuple(row) == rref(row) for row in rows))
            self.assertTrue(np.all(rows < (1 << n)))

    def test_exact_positive_and_bound_strength(self):
        candidate = {'basis': [272, 4, 1], 'bound': 17, 'theorem': 'fixture'}
        rep = {'index': 416, 'basis': [96, 2, 1], 'lb': 17}
        self.assertIn('witness', search([candidate], [rep])[0])
        candidate['bound'] = 16
        self.assertNotIn('witness', search([candidate], [rep])[0])

    def test_containment_is_separate_from_exact_orbit(self):
        candidate = {'basis': [4, 2, 1], 'bound': 15, 'theorem': 'fixture'}
        rep = {'index': 0, 'basis': [2, 1], 'lb': 15}
        self.assertNotIn('witness', search([candidate], [rep])[0])
        self.assertIn('witness', search([candidate], [rep], containment=True)[0])

    def test_packing_above_64_bits(self):
        rows = np.array([[256, 128, 64, 32, 16, 8, 4, 2],
                         [256, 128, 64, 32, 16, 8, 4, 3]], dtype=np.uint16)
        keys = packed_rows(rows)
        self.assertEqual(list(keys), [packed(row) for row in rows])
        self.assertGreater(int(keys[0]), 2 ** 64 - 1)
        self.assertNotEqual(keys[0], keys[1])

    def test_dimension_eight_exact_transport(self):
        basis = [256, 128, 64, 32, 16, 8, 4, 2]
        candidate = dict(basis=basis, bound=1, theorem='fixture8')
        rep = dict(index=0, basis=basis, lb=1)
        self.assertIn('witness', search([candidate], [rep])[0])


if __name__ == '__main__':
    unittest.main()
