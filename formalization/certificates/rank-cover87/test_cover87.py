"""Finite geometry regression checks; Lean verifies the actual rank theorem."""

import argparse
import copy
import json
from pathlib import Path
import sys
import unittest


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--helpers", type=Path, default=ROOT)
args, remaining = parser.parse_known_args()
sys.path.insert(0, str(args.helpers / "tools"))

from generate_certificate import span
from global_orbit_unused_certificate import transport, word_code


def check_cover(data):
    if (data["node"], data["basis"], data["bound"], data["source_bound"]) != (
            87, [64, 8, 4, 2, 1], 11, 9):
        raise ValueError("Unexpected rank target")
    covered = set()
    for row in data["rows"]:
        if row["orbit"] != 5 or row["source"] != {
                "theorem": "QiushiMatmul.orbit5_lb9", "module": "QiushiOrbit5FP",
                "basis": [1, 2, 4, 8, 16, 64, 160], "bound": 9}:
            raise ValueError("Unapproved predecessor")
        actual = span(row["basis"])
        if not span(data["basis"]) <= actual:
            raise ValueError("Target is not contained in source")
        if not set(row["preimages"]) <= span(row["source"]["basis"]):
            raise ValueError("Invalid source preimage")
        if [word_code(row["word"], c) for c in row["preimages"]] != row["basis"]:
            raise ValueError("Wrong transported generators")
        if json.loads(json.dumps(transport(row))) != row["witness"]:
            raise ValueError("Wrong explicit transport")
        covered.update(actual)
    if covered != set(range(512)):
        raise ValueError("Incomplete matrix cover")


class Cover87Tests(unittest.TestCase):
    def setUp(self):
        self.data = json.loads((HERE / "cover.json").read_text())

    def test_all_transports_and_actual_matrix_cover(self):
        self.assertEqual(len(self.data["rows"]), 9)
        check_cover(self.data)

    def test_concrete_basis_order_matches_lean(self):
        render = lambda xs: "[" + ",".join(map(str, xs)) + "]"
        literal = ",\n  ".join(render(row["basis"]) for row in self.data["rows"])
        self.assertIn(literal, (ROOT / "QiushiGlobalOrbitUnused87.lean").read_text())

    def test_corrupted_matrix_rejected(self):
        self.data["rows"][0]["witness"]["P"] = 0
        with self.assertRaisesRegex(ValueError, "Wrong explicit transport"):
            check_cover(self.data)

    def test_missing_cover_row_rejected(self):
        for i in range(9):
            broken = copy.deepcopy(self.data)
            broken["rows"].pop(i)
            with self.subTest(row=i), self.assertRaisesRegex(ValueError, "Incomplete"):
                check_cover(broken)

    def test_capacity_contradiction(self):
        for r in (9, 10):
            self.assertLess(9 * (r - 9), r)


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0], *remaining])
