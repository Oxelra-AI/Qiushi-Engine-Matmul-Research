"""Negative tests for the untrusted exact-transport witness cache."""
from copy import deepcopy
import unittest
from unittest.mock import patch

import generate_frozen_bindings as generator


class WitnessValidationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.action_data = generator.actions()

    def setUp(self):
        self.row = {"idx": 0, "orbit": 0, "basis": [4, 2, 1]}
        self.reps = [{"basis": [4, 2, 1]}]
        self.witness = {"P": 273, "Q": 273, "Qinv": 273, "flip": False,
                        "pairs": [[4, 4], [2, 2], [1, 1]]}
        mock = patch.object(generator, "actions", return_value=self.action_data)
        mock.start()
        self.addCleanup(mock.stop)

    def check(self, row=None, witness=None):
        generator.validate_witnesses([row or self.row], self.reps,
                                     {0: witness or self.witness})

    def test_exact_identity_is_accepted(self):
        self.check()

    def test_forward_containment_without_reverse_coverage_is_rejected(self):
        row, witness = deepcopy(self.row), deepcopy(self.witness)
        row["basis"] = [1]
        witness["pairs"] = [[1, 1]]
        with self.assertRaisesRegex(ValueError, "missing reverse span coverage"):
            self.check(row, witness)

    def test_wrong_inverse_is_rejected(self):
        witness = deepcopy(self.witness)
        witness["Qinv"] = 0
        with self.assertRaisesRegex(ValueError, "invalid inverse"):
            self.check(witness=witness)

    def test_wrong_image_is_rejected(self):
        witness = deepcopy(self.witness)
        witness["pairs"][0][1] = 2
        with self.assertRaisesRegex(ValueError, "invalid forward membership or image"):
            self.check(witness=witness)

    def test_missing_cached_space_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "incomplete witness cache"):
            generator.validate_witnesses([self.row], self.reps, {})


if __name__ == "__main__":
    unittest.main()
