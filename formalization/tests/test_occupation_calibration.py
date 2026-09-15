import io
import json
from pathlib import Path
import pickle
import sys
import unittest

FORMALIZATION = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FORMALIZATION / "tools"))
from replay_occupation_calibration import (  # noqa: E402
    PrimitiveUnpickler,
    decode_support,
    tensor_mismatches,
)


class CalibrationTests(unittest.TestCase):
    def test_multiplicities_are_not_booleanized(self):
        counts = decode_support([[2, 2], [7, 1]])
        self.assertEqual(counts[1], 2)
        self.assertEqual(sum(counts), 3)

    def test_invalid_support_rejected(self):
        bad_supports = [
            [[0, 1]], [[128, 1]], [[1, 0]], [[1, -1]],
            [[1, 1], [1, 2]], [[True, 1]], [[1, True]],
        ]
        for support in bad_supports:
            with self.subTest(support=support), self.assertRaises(ValueError):
                decode_support(support)

    def test_primitive_pickle_only(self):
        primitive = {"lut": {1: 19}}
        self.assertEqual(PrimitiveUnpickler(io.BytesIO(pickle.dumps(primitive))).load(), primitive)
        with self.assertRaises(pickle.UnpicklingError):
            PrimitiveUnpickler(io.BytesIO(pickle.dumps(Path("not-an-input")))).load()

    def test_tensor_identity_and_mutation(self):
        path = FORMALIZATION.parent / (
            "research/materials/quotient_cores/results/pivot_fixed/"
            "pivot17_rank23_transformed_control.json"
        )
        terms = json.loads(path.read_text())["terms"]
        self.assertEqual(tensor_mismatches(terms), [])
        mutated = [list(term) for term in terms]
        mutated[0][2] ^= 1
        self.assertNotEqual(tensor_mismatches(mutated), [])

    def test_invalid_tensor_codes_rejected(self):
        with self.assertRaises(ValueError):
            tensor_mismatches([[0, 0, 0]] * 22)
        with self.assertRaises(ValueError):
            tensor_mismatches([[512, 0, 0]] * 23)
        self.assertEqual(len(tensor_mismatches([[0, 0, 0]] * 23)), 27)


if __name__ == "__main__":
    unittest.main()
