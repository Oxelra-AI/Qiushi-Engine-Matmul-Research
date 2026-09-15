import sys
from pathlib import Path
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from generate_frozen_table import emit, read_representatives


HEADER = '''problem_name: "matrix_q02_n333"
characteristic: 2
extension_degree: 1
na: 9
nb: 9
nc: 9
'''


def certificate_text():
    return HEADER + "\n".join(
        f"constrained_tensors {{ index: {i} rank_lower_bound: {i % 28} }}"
        for i in reversed(range(496)))


class FrozenTableTests(unittest.TestCase):
    def parse(self, text):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "certificate.pb.txt"
            path.write_text(text)
            return read_representatives(path)

    def test_structured_parse_and_bounded_definition(self):
        rows, digest = self.parse(certificate_text())
        self.assertEqual([r["index"] for r in rows], list(range(496)))
        self.assertEqual(rows[495]["lb"], 495 % 28)
        self.assertEqual(len(digest), 64)
        source = emit(rows)
        self.assertIn("def frozenWangTable : FrozenOrbitTable", source)
        self.assertIn("match i.val / 32 with", source)
        self.assertNotIn("axiom", source)

    def test_rejects_wrong_problem(self):
        for old, new in [("characteristic: 2", "characteristic: 3"),
                         ("na: 9", "na: 8"),
                         ("matrix_q02_n333", "matrix_q02_n334")]:
            with self.subTest(new=new), self.assertRaises(ValueError):
                self.parse(certificate_text().replace(old, new))

    def test_rejects_duplicate_or_missing_index(self):
        text = certificate_text()
        with self.assertRaises(ValueError):
            self.parse(text.replace("index: 495", "index: 494"))
        with self.assertRaises(ValueError):
            self.parse("\n".join(text.splitlines()[:-1]))

    def test_rejects_invalid_codes_and_labels(self):
        for field in [r'constraints: "\001"', r'constraints: "\000\002"',
                      r'constraints: "\001\000\001\000"']:
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.parse(certificate_text().replace("index: 495", f"index: 495 {field}"))
        with self.assertRaises(ValueError):
            self.parse(certificate_text().replace("rank_lower_bound: 19", "rank_lower_bound: 28"))


if __name__ == "__main__":
    unittest.main()
