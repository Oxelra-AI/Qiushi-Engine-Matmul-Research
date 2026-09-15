"""Check node-88 certificate data and deterministic Lean emission, not rank axioms."""

import argparse
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--helpers", type=Path, default=ROOT)
args, remaining = parser.parse_known_args()
sys.path[:0] = [str(args.helpers / "tools"), str(args.helpers / "tests")]

from generate_certificate import emit_data, finish, span
from global_orbit_unused_certificate import transport
from test_certificate import check_ray


class Node88Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.meta = json.loads((HERE / "tables.json").read_text())
        cls.cert = json.loads((HERE / "branch.json").read_text())
        cls.sources = json.loads((HERE / "sources.json").read_text())
        cls.witnesses = {
            int(k): v for k, v in
            json.loads((HERE / "transport-witnesses.json").read_text()).items()
        }

    def test_exact_target_and_closed_predecessors(self):
        self.assertEqual(self.meta["plane"], 88)
        self.assertEqual(self.meta["basis"], [80, 8, 4, 2, 1])
        self.assertEqual(self.meta["target"], 12)
        self.assertEqual(self.meta["module_prefix"], "QiushiGlobalOrbitUnused88")
        self.assertEqual(self.meta["n_live"], 3)
        self.assertEqual(self.meta["n_occ"], 13)
        self.assertEqual(self.meta["n_dead"], 12)
        closed = json.loads((HERE / "closed-predecessors.json").read_text())
        allowed = {r["index"]: r for r in closed["entries"]}
        self.assertEqual(set(allowed), {5, 20, 23, 25})
        self.assertEqual({r["orbit"] for r in self.meta["source_rows"]}, set(allowed))
        for row in self.meta["source_rows"]:
            self.assertEqual(row["source"], allowed[row["orbit"]]["source"])
            self.assertLessEqual(row["lb"], row["source"]["bound"])
            self.assertNotIn("FrozenRegistry", row["source"]["module"])

    def test_all_explicit_transports(self):
        self.assertEqual(set(self.witnesses), set(range(13)))
        for row in self.meta["source_rows"]:
            with self.subTest(row=row["idx"]):
                self.assertTrue(set(row["preimages"]) <= span(row["source"]["basis"]))
                expected = json.loads(json.dumps(transport(row)))
                self.assertEqual(self.witnesses[row["idx"]], expected)

    def test_dead_rows_use_checked_target_bounds(self):
        rows = self.meta["source_rows"]
        self.assertEqual(len(self.meta["dead_witnesses"]), 12)
        for dead in self.meta["dead_witnesses"]:
            source = rows[dead["witness_source_idx"]]
            self.assertEqual(dead["basis"], source["basis"])
            self.assertEqual(source["lb"], 12)

    def test_exact_leaf(self):
        self.assertEqual(self.cert["branch"]["tree"], {"type": "leaf", "path": ""})
        leaves = self.cert["branch"]["certs"]
        self.assertEqual(len(leaves), 1)
        self.assertEqual(leaves[0]["rhs"], -9)
        check_ray(self.meta, leaves[0])

    def test_corrupt_multiplier_rejected(self):
        broken = copy.deepcopy(self.cert["branch"]["certs"][0])
        broken["used_rows"][0]["multiplier"] += 1
        with self.assertRaises(ValueError):
            check_ray(self.meta, broken)

    def test_deterministic_emission(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            emit_data(self.meta, output)
            finish(self.meta, self.cert, self.sources, output, transports=self.witnesses)
            files = sorted(output.glob("QiushiGlobalOrbitUnused88*.lean"))
            self.assertEqual(len(files), 51)
            for path in files:
                self.assertEqual(path.read_bytes(), (ROOT / path.name).read_bytes(), path.name)


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0], *remaining])
