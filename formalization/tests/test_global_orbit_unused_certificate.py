"""Regenerated node certificates are tested as data; Lean checks their semantics."""

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from generate_certificate import finish, names, span
from generate_global_orbit_checks import unpack
from global_orbit_unused_certificate import exact_branch, matrix_product, transport, word_code
from test_certificate import check_ray


class UnusedCertificateTests(unittest.TestCase):
    def test_word_matrix_transport_including_transpose(self):
        for word in [[], [0], [1, 3, 2], [3, 2, 0, 3, 1], [2, 3, 0, 1, 2, 3]]:
            original = [1, 2, 4]
            row = dict(word=word, basis=[word_code(word, c) for c in original], preimages=original)
            witness = transport(row)
            self.assertEqual(matrix_product(witness["Q"], witness["Qinv"]), 273)
            self.assertEqual(witness["pairs"], list(zip(row["basis"], original)))

    def test_custom_module_prefix_is_bounded(self):
        meta = dict(plane=184, name_tag="Unused", module_prefix="QiushiGlobalOrbitUnused184")
        self.assertEqual(names(meta), ("plane184UnusedGen", "QiushiGlobalOrbitUnused184"))
        for bad in ["../Outside", "Bad\nModule", "42Bad", ""]:
            with self.assertRaises(ValueError):
                names(dict(meta, module_prefix=bad))

    def test_supplied_transports_must_cover_all_rows(self):
        meta = dict(plane=184, n_live=1, n_occ=1, source_rows=[dict(idx=0, orbit=7, lb=9)])
        ledger = dict(entries={"7": dict(orbit=7, lb=9, module="Source", basis_codes=[1])})
        with tempfile.TemporaryDirectory() as directory:
            for witnesses in [{}, {1: {}}]:
                with self.assertRaisesRegex(ValueError, "transport indices"):
                    finish(meta, {}, ledger, Path(directory), transports=witnesses)

    def test_regenerated_exact_leaf_and_corruption(self):
        data = dict(node=1, basis=[1], target=3, sections=[0, 2, 4, 6], rows=[
            dict(idx=0, basis=[1, 2], orbit=2, lb=3),
            dict(idx=1, basis=[1, 2, 4], orbit=3, lb=2)])
        meta, cert = exact_branch(data)
        self.assertEqual(meta["n_live"], 2)
        self.assertEqual(len(cert["branch"]["certs"]), 1)
        leaf = cert["branch"]["certs"][0]
        check_ray(meta, leaf)
        broken = copy.deepcopy(leaf)
        broken["used_rows"][0]["multiplier"] += 1
        with self.assertRaises(ValueError):
            check_ray(meta, broken)

    def test_integer_occupation_model_rejected(self):
        data = dict(node=1, basis=[1], target=1, sections=[0, 2],
                    rows=[dict(idx=0, basis=[1], orbit=2, lb=1)])
        with self.assertRaisesRegex(ValueError, "integer occupation model"):
            exact_branch(data)

    def test_packaged_branch_and_node_limit(self):
        directory = ROOT / "certificates/global-unused353"
        meta = json.loads((directory / "tables.json").read_text())
        certificate = json.loads((directory / "branch.json").read_text())
        pivots = {row.bit_length() - 1 for row in meta["basis"]}
        free = [bit for bit in range(9) if bit not in pivots]
        data = dict(node=353, basis=meta["basis"], target=meta["target"],
                    rows=meta["source_rows"],
                    sections=[unpack(free, mask) for mask in range(1 << len(free))])
        with self.assertRaisesRegex(RuntimeError, "bounded branch search exhausted"):
            exact_branch(data, node_limit=1)
        generated_meta, generated = exact_branch(data, node_limit=3)
        self.assertEqual(generated["branch"]["tree"], certificate["branch"]["tree"])
        self.assertEqual(len(generated["branch"]["certs"]), 2)
        for leaf in generated["branch"]["certs"]:
            check_ray(generated_meta, leaf)

    def test_packaged_certificates(self):
        expected = {
            88: ([80, 8, 4, 2, 1], 12, {5, 20, 23, 25}),
            92: ([160, 80, 4, 2, 1], 12, {8, 9, 25}),
            181: ([258, 84, 32, 10, 1], 14, {5, 55, 78, 82, 83, 84}),
            184: ([386, 84, 32, 10, 1], 14, {7, 51, 55, 56, 79, 82, 84}),
            203: ([272, 176, 68, 10, 1], 15, {8, 10, 67, 69}),
            240: ([261, 161, 68, 19, 10], 15, {66, 67, 84}),
            248: ([8, 4, 2, 1], 13, {5, 20, 23, 25, 88}),
            249: ([80, 4, 2, 1], 13, {23, 25, 27, 88}),
            273: ([156, 80, 2, 1], 15, {23, 31, 35, 97, 101, 134}),
            284: ([68, 20, 10, 1], 16, {19, 75, 96, 150, 156, 159, 160, 161}),
            289: ([258, 20, 10, 1], 16,
                  {3, 7, 10, 11, 17, 35, 75, 118, 156, 160, 161, 164, 166, 175}),
            291: ([84, 32, 10, 1], 15,
                  {23, 32, 35, 99, 101, 120, 141, 179, 180, 181, 182, 183, 184, 185}),
            301: ([176, 68, 10, 1], 16,
                  {1, 75, 147, 149, 150, 159, 160, 178, 203, 204}),
            302: ([304, 68, 10, 1], 16, {30, 161, 178, 202}),
            304: ([256, 84, 10, 1], 15,
                  {10, 35, 65, 112, 128, 141, 149, 151, 182, 183, 185, 208, 209, 211}),
            305: ([258, 84, 10, 1], 16,
                  {3, 10, 14, 16, 35, 41, 51, 55, 56, 57, 65, 68, 78, 79, 82, 83, 84, 109, 150, 185}),
            306: ([132, 96, 10, 1], 16,
                  {3, 10, 14, 17, 35, 65, 128, 152, 162, 178, 179, 180, 196, 212, 213, 214, 216, 217, 218}),
            307: ([272, 96, 10, 1], 16,
                  {3, 10, 11, 14, 35, 71, 112, 164, 178, 212, 213, 214}),
            308: ([288, 96, 10, 1], 15,
                  {3, 10, 14, 35, 101, 103, 120, 165, 182, 183, 197}),
            309: ([290, 96, 10, 1], 16,
                  {3, 11, 14, 30, 31, 111, 156, 166, 194, 196, 216}),
            312: ([386, 96, 10, 1], 16,
                  {10, 14, 35, 55, 72, 161, 164, 166, 178, 194, 196, 201, 212, 213, 216, 218}),
            337: ([258, 98, 16, 1], 15,
                  {30, 35, 43, 67, 69, 124, 130, 155, 165, 179, 182, 184, 197, 199, 232, 233, 234}),
            339: ([296, 98, 16, 1], 15,
                  {14, 35, 40, 43, 65, 69, 130, 134, 144, 153, 165, 180, 182, 183, 185, 209, 225, 233, 234}),
            353: ([196, 38, 20, 1], 16,
                  {2, 3, 10, 11, 14, 51, 56, 69, 72, 118, 133, 156, 157, 166, 194, 198, 216, 235}),
            354: ([136, 96, 20, 1], 16,
                  {3, 10, 14, 35, 55, 74, 78, 124, 162, 164, 179, 189, 196, 198, 201, 214, 216, 236, 237, 238}),
            355: ([164, 96, 20, 1], 16,
                  {3, 10, 11, 14, 17, 35, 55, 56, 78, 164, 187, 194, 201, 216, 235, 236, 238}),
            356: ([290, 96, 20, 1], 16,
                  {11, 14, 35, 55, 143, 165, 166, 194, 201, 235, 236, 238}),
            386: ([161, 68, 20, 10], 16,
                  {3, 10, 11, 75, 159, 218, 238, 240, 245}),
            387: ([162, 68, 20, 10], 16,
                  {3, 10, 11, 14, 74, 75, 159, 166, 175, 180, 197, 212, 216, 218, 235, 236, 242, 244, 246}),
            388: ([164, 68, 20, 10], 16,
                  {11, 65, 75, 78, 82, 159, 162, 168, 175, 178, 193, 197, 213, 235, 241, 242, 244, 245, 246}),
            389: ([166, 68, 20, 10], 16,
                  {11, 14, 67, 75, 159, 160, 175, 187, 192, 194, 216, 241, 244, 246}),
            390: ([167, 68, 20, 10], 16,
                  {10, 14, 55, 75, 78, 159, 180, 201, 204, 217, 218, 238, 242, 246}),
            392: ([259, 68, 20, 10], 16,
                  {2, 75, 160, 164, 235, 239, 246}),
            394: ([289, 68, 20, 10], 16,
                  {12, 14, 41, 43, 75, 161, 164, 166, 175, 185, 189, 194, 196, 198, 201, 213, 216, 235, 236, 238, 239, 244, 245, 246}),
            395: ([131, 96, 20, 10], 16,
                  {10, 12, 16, 35, 40, 65, 75, 162, 175, 178, 180, 201, 212, 213, 214, 218, 235, 236, 238, 239, 241, 246}),
            396: ([133, 96, 20, 10], 16,
                  {2, 10, 14, 55, 74, 75, 162, 175, 178, 202, 212, 213, 237, 238, 245, 246}),

            321: ([306, 160, 10, 1], 16,
                  {3, 10, 14, 17, 55, 56, 65, 76, 78, 150, 202, 204, 218}),
            328: ([140, 96, 16, 1], 15,
                  {14, 29, 65, 67, 105, 108, 140, 148, 179, 181, 192, 197, 220, 225, 227}),
            333: ([298, 96, 16, 1], 15,
                  {10, 13, 16, 35, 44, 76, 80, 81, 107, 134, 140, 163, 180, 182, 188, 189, 227}),
            371: ([290, 224, 20, 1], 16,
                  {11, 14, 17, 56, 72, 75, 164, 175, 189, 196, 236, 237}),
            372: ([298, 224, 20, 1], 16,
                  {3, 10, 11, 14, 55, 65, 69, 80, 144, 146, 183, 201, 213, 214, 218, 236}),
            376: ([160, 68, 19, 10], 16,
                  {14, 29, 74, 202, 239}),
            378: ([162, 68, 19, 10], 16,
                  {1, 217, 237, 241}),
            379: ([164, 68, 19, 10], 16,
                  {3, 10, 67, 74, 147, 152, 203, 212, 241, 242}),
            380: ([258, 68, 19, 10], 16,
                  {10, 47, 67, 150, 166, 194, 196, 202, 220, 235, 241, 242}),
            382: ([262, 68, 19, 10], 16,
                  {14, 68, 150, 155, 194, 212, 216, 217, 235, 239, 240, 241, 242}),
            383: ([289, 68, 19, 10], 16,
                  {10, 11, 14, 38, 151, 166, 196, 212, 216, 235, 237, 239, 241}),
            398: ([161, 96, 20, 10], 16,
                  {3, 10, 14, 35, 67, 178, 213, 235, 236, 238, 239, 242}),
            399: ([164, 96, 20, 10], 16,
                  {10, 35, 47, 75, 175, 178, 241, 244, 246}),
            401: ([261, 96, 20, 10], 16,
                  {10, 14, 41, 55, 75, 164, 166, 175, 196, 199, 201, 213, 214, 218, 221, 235, 236, 237, 238, 241, 246}),
            402: ([391, 96, 20, 10], 16,
                  {2, 3, 10, 14, 55, 64, 75, 78, 164, 175, 183, 196, 201, 212, 213, 214, 216, 218, 236, 238, 242, 245, 246}),
            403: ([304, 161, 68, 10], 16,
                  {10, 202, 218, 238}),
            404: ([309, 162, 68, 10], 16,
                  {10, 14, 47, 75, 78, 202, 213, 214, 217, 236, 246}),
            406: ([276, 179, 68, 10], 16,
                  {10, 14, 47, 203, 213, 218, 239}),
            407: ([257, 163, 84, 10], 16,
                  {2, 10, 56, 78, 212, 213, 214, 217, 236, 238, 241}),
            408: ([262, 163, 84, 10], 16,
                  {10, 14, 65, 212, 237, 238}),
        }
        directories = list((ROOT / "certificates").glob("global-unused*"))
        self.assertTrue(directories)
        for directory in directories:
            with self.subTest(node=directory.name):
                meta = json.loads((directory / "tables.json").read_text())
                cert = json.loads((directory / "branch.json").read_text())
                basis, target, predecessors = expected[meta["plane"]]
                self.assertEqual(meta["basis"], basis)
                self.assertEqual(meta["target"], target)
                self.assertEqual({r["orbit"] for r in meta["source_rows"]}, predecessors)
                for row in meta["source_rows"]:
                    self.assertGreaterEqual(row["source"]["bound"], row["lb"])
                    self.assertTrue(set(row["preimages"]) <= span(row["source"]["basis"]))
                    transport(row)
                for leaf in cert["branch"]["certs"]:
                    check_ray(meta, leaf)


if __name__ == "__main__":
    unittest.main()
