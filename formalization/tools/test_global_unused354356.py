"""Replay the single-leaf certificates for reserved nodes 354, 355 and 356."""

import argparse
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--helpers", type=Path, default=ROOT)
parser.add_argument("--node", type=int, choices=(354, 355, 356), action="append")
args, remaining = parser.parse_known_args()
sys.path[:0] = [str(args.helpers / "tools"), str(args.helpers / "tests")]

from generate_certificate import emit_checks, emit_data, finish, span
from global_orbit_unused_certificate import transport, word_code
from test_certificate import check_ray


EXPECTED = {
    354: ([136, 96, 20, 1], 20, 30, 11, -31),
    355: ([164, 96, 20, 1], 22, 21, 9, -2),
    356: ([290, 96, 20, 1], 20, 27, 11, -2),
}


class SingleLeafBatchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = {}
        for node in args.node or EXPECTED:
            directory = ROOT / "certificates" / f"global-unused{node}"
            cls.data[node] = {
                name: json.loads((directory / (name + ".json")).read_text())
                for name in ("tables", "branch", "sources", "transport-witnesses",
                             "closed-predecessors", "generation")
            }

    def test_targets_and_closed_predecessors(self):
        for node, data in self.data.items():
            with self.subTest(node=node):
                meta = data["tables"]
                basis, live, rows, dead, _ = EXPECTED[node]
                self.assertEqual((meta["plane"], meta["basis"], meta["target"]),
                                 (node, basis, 16))
                self.assertEqual((meta["n_live"], meta["n_occ"], meta["n_dead"]),
                                 (live, rows, dead))
                allowed = {r["index"]: r for r in data["closed-predecessors"]["entries"]}
                self.assertEqual({r["orbit"] for r in meta["source_rows"]}, set(allowed))
                self.assertTrue(set(allowed).isdisjoint(EXPECTED))
                for row in meta["source_rows"]:
                    self.assertEqual(row["source"], allowed[row["orbit"]]["source"])
                    self.assertLessEqual(row["lb"], row["source"]["bound"])
                    self.assertNotIn("FrozenRegistry", row["source"]["module"])

    def test_all_explicit_transports_and_containments(self):
        for node, data in self.data.items():
            with self.subTest(node=node):
                meta, witnesses = data["tables"], data["transport-witnesses"]
                self.assertEqual(set(map(int, witnesses)), set(range(meta["n_occ"])))
                for row in meta["source_rows"]:
                    self.assertTrue(span(meta["basis"]) <= span(row["basis"]))
                    self.assertTrue(set(row["preimages"]) <= span(row["source"]["basis"]))
                    self.assertEqual([word_code(row["word"], c) for c in row["preimages"]],
                                     row["basis"])
                    self.assertEqual(json.loads(json.dumps(transport(row))),
                                     witnesses[str(row["idx"])])

    def test_dead_witnesses_and_complete_live_partition(self):
        for node, data in self.data.items():
            with self.subTest(node=node):
                meta = data["tables"]
                for dead in meta["dead_witnesses"]:
                    source = meta["source_rows"][dead["witness_source_idx"]]
                    self.assertEqual(dead["basis"], source["basis"])
                    self.assertEqual(source["lb"], 16)
                killed = set().union(*(span(d["basis"]) for d in meta["dead_witnesses"]))
                free = sorted(set(range(9)) - {c.bit_length() - 1 for c in meta["basis"]})
                sections = [sum(((q >> j) & 1) << bit for j, bit in enumerate(free))
                            for q in range(1 << len(free))]
                self.assertEqual(meta["live_list"],
                                 [q - 1 for q, c in enumerate(sections) if c not in killed])

    def test_exact_single_leaf_without_branch_assumptions(self):
        for node, data in self.data.items():
            with self.subTest(node=node):
                branch = data["branch"]["branch"]
                self.assertEqual(branch["tree"], {"type": "leaf", "path": ""})
                self.assertEqual(len(branch["certs"]), 1)
                leaf = branch["certs"][0]
                self.assertEqual((leaf["path"], leaf["lower"], leaf["upper"]), ("", {}, {}))
                self.assertEqual(leaf["rhs"], EXPECTED[node][-1])
                self.assertTrue(all(row["type"] in ("occ", "total_ge", "nonneg")
                                    for row in leaf["used_rows"]))
                check_ray(data["tables"], leaf)

    def test_corrupted_multipliers_rejected(self):
        for node, data in self.data.items():
            broken = copy.deepcopy(data["branch"]["branch"]["certs"][0])
            broken["used_rows"][0]["multiplier"] += 1
            with self.subTest(node=node), self.assertRaises(ValueError):
                check_ray(data["tables"], broken)

    def test_deterministic_emission(self):
        for node, data in self.data.items():
            with self.subTest(node=node), tempfile.TemporaryDirectory() as directory:
                output = Path(directory)
                meta, cert, ledger = data["tables"], data["branch"], data["sources"]
                witnesses = {int(k): v for k, v in data["transport-witnesses"].items()}
                emit_data(meta, output)
                finish(meta, cert, ledger, output, transports=witnesses)
                prefix = f"QiushiGlobalOrbitUnused{node}"
                for field in ("Section", "Dead", "Source", "DeadSource", "Indicator"):
                    for path in output.glob(prefix + field + "Block*.lean"):
                        path.unlink()
                self.assertEqual(data["generation"]["check_width"], 128)
                emit_checks(meta, output, width=128)
                files = sorted(output.glob(prefix + "*.lean"))
                self.assertEqual(len(files), 29)
                for path in files:
                    self.assertEqual(path.read_bytes(), (ROOT / path.name).read_bytes(), path.name)


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0], *remaining])
