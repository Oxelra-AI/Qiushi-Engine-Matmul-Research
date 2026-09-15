import sys
from pathlib import Path
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from generate_strict_rows import emit_instance, witnesses


class StrictRowTests(unittest.TestCase):
    def test_separating_functionals(self):
        lower, upper = [19, 10], [68, 19, 10]
        x, d, e, y = witnesses(lower, upper)
        self.assertTrue(all((d & b).bit_count() % 2 == 0 for b in lower))
        self.assertEqual((d & x).bit_count() % 2, 1)
        self.assertTrue(all((e & b).bit_count() % 2 == 0 for b in upper))
        self.assertEqual((e & y).bit_count() % 2, 1)

    def test_rejects_non_strict_and_full_spaces(self):
        for lower, upper in [([1], [1]), ([2], [1]), ([1], [1 << i for i in range(9)])]:
            with self.subTest(lower=lower, upper=upper), self.assertRaises(ValueError):
                witnesses(lower, upper)

    def test_emits_indexed_public_statement(self):
        meta = {"plane": 484, "basis": [19, 10],
                "source_rows": [{"idx": 0, "basis": [68, 19, 10]}],
                "dead_witnesses": [{"d_idx": 0, "basis": [68, 19, 10]}]}
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)
            self.assertEqual(emit_instance(meta, out), 2)
            final = (out / "QiushiPlane484StrictFinal.lean").read_text()
            self.assertIn("plane484GenConfig.W < plane484GenConfig.sourceU i", final)
            self.assertIn("plane484GenConfig.deadU i < ⊤", final)
            self.assertIn("strictSpanCheck_sound", final)
            meta["source_rows"][0]["idx"] = 1
            with self.assertRaises(ValueError):
                emit_instance(meta, out)


if __name__ == "__main__":
    unittest.main()
