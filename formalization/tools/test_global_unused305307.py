"""Replay only the reserved 305/306/307 certificates; Lean remains authoritative."""

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
parser.add_argument("--node", type=int, choices=(305, 306, 307), action="append")
args, remaining = parser.parse_known_args()
sys.path[:0] = [str(args.helpers / "tools"), str(args.helpers / "tests")]

from generate_certificate import emit_checks, emit_data, finish, span
from global_orbit_unused_certificate import transport, word_code
from test_certificate import check_ray


EXPECTED = {
    305: ([258, 84, 10, 1], 30, 84, 1, 7, 47),
    306: ([132, 96, 10, 1], 17, 30, 14, 1, 29),
    307: ([272, 96, 10, 1], 19, 20, 12, 1, 27),
}


def check_paths(cert):
    leaves = {leaf["path"]: leaf for leaf in cert["branch"]["certs"]}
    if len(leaves) != len(cert["branch"]["certs"]):
        raise ValueError("Duplicate leaf path")
    visited = set()

    def visit(node, path, lower, upper):
        if node["path"] != path:
            raise ValueError("Wrong branch path")
        if node["type"] == "leaf":
            leaf = leaves[path]
            if leaf["lower"] != lower or leaf["upper"] != upper:
                raise ValueError("Leaf assumes a different branch context")
            for row in leaf["used_rows"]:
                if row["type"] in ("branch_upper", "branch_lower"):
                    bounds = upper if row["type"] == "branch_upper" else lower
                    if bounds.get(str(row["label"] - 1)) != row["bound"]:
                        raise ValueError("Leaf uses an unproved branch bound")
            visited.add(path)
        elif node["type"] == "branch":
            label, floor = str(node["label"] - 1), node["floor"]
            visit(node["left"], path + "L", lower, dict(upper, **{label: floor}))
            visit(node["right"], path + "R", dict(lower, **{label: floor + 1}), upper)
        else:
            raise ValueError("Unclosed branch")

    visit(cert["branch"]["tree"], "", {}, {})
    if visited != set(leaves):
        raise ValueError("Unreachable leaf")


class ReservedNodesTests(unittest.TestCase):
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
                basis, live, rows, dead, leaves, _ = EXPECTED[node]
                self.assertEqual((meta["plane"], meta["basis"], meta["target"]),
                                 (node, basis, 16))
                self.assertEqual((meta["n_live"], meta["n_occ"], meta["n_dead"]),
                                 (live, rows, dead))
                self.assertEqual(len(data["branch"]["branch"]["certs"]), leaves)
                allowed = {r["index"]: r for r in data["closed-predecessors"]["entries"]}
                self.assertEqual({r["orbit"] for r in meta["source_rows"]}, set(allowed))
                self.assertTrue(set(allowed).isdisjoint({305, 306, 307}))
                for row in meta["source_rows"]:
                    self.assertEqual(row["source"], allowed[row["orbit"]]["source"])
                    self.assertLessEqual(row["lb"], row["source"]["bound"])
                    self.assertNotIn("FrozenRegistry", row["source"]["module"])

    def test_transports_dead_bounds_and_live_partition(self):
        for node, data in self.data.items():
            with self.subTest(node=node):
                meta, witnesses = data["tables"], data["transport-witnesses"]
                self.assertEqual(set(map(int, witnesses)), set(range(meta["n_occ"])))
                rows = meta["source_rows"]
                for row in rows:
                    self.assertTrue(set(row["preimages"]) <= span(row["source"]["basis"]))
                    self.assertEqual([word_code(row["word"], c) for c in row["preimages"]],
                                     row["basis"])
                    self.assertEqual(json.loads(json.dumps(transport(row))),
                                     witnesses[str(row["idx"])])
                for dead in meta["dead_witnesses"]:
                    source = rows[dead["witness_source_idx"]]
                    self.assertEqual(dead["basis"], source["basis"])
                    self.assertEqual(source["lb"], 16)
                killed = set().union(*(span(d["basis"]) for d in meta["dead_witnesses"]))
                free = sorted(set(range(9)) - {c.bit_length() - 1 for c in meta["basis"]})
                sections = [sum(((q >> j) & 1) << bit for j, bit in enumerate(free))
                            for q in range(1 << len(free))]
                self.assertEqual(meta["live_list"],
                                 [q - 1 for q, c in enumerate(sections) if c not in killed])

    def test_all_exact_rays_and_branch_contexts(self):
        for node, data in self.data.items():
            with self.subTest(node=node):
                check_paths(data["branch"])
                for leaf in data["branch"]["branch"]["certs"]:
                    check_ray(data["tables"], leaf)

    def test_corrupted_multipliers_rejected(self):
        for node, data in self.data.items():
            broken = copy.deepcopy(data["branch"]["branch"]["certs"][0])
            broken["used_rows"][0]["multiplier"] += 1
            with self.subTest(node=node), self.assertRaises(ValueError):
                check_ray(data["tables"], broken)

    def test_corrupted_branch_paths_rejected(self):
        for node, data in self.data.items():
            broken = copy.deepcopy(data["branch"])
            broken["branch"]["tree"]["path"] = "L"
            with self.subTest(node=node), self.assertRaises(ValueError):
                check_paths(broken)

    def test_deterministic_emission_at_recorded_width(self):
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
                emit_checks(meta, output, width=data["generation"]["check_width"])
                files = sorted(output.glob(prefix + "*.lean"))
                self.assertEqual(len(files), EXPECTED[node][-1])
                for path in files:
                    self.assertEqual(path.read_bytes(), (ROOT / path.name).read_bytes(), path.name)


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0], *remaining])
