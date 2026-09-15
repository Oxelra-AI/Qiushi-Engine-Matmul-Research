"""Producer and source-boundary checks; these do not replace the Lean replay."""

import importlib.util
from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("finite_orbits", ROOT / "tools/generate_finite_orbits.py")
GEN = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GEN)


class FiniteOrbitTests(unittest.TestCase):
    def test_generators_are_involutions(self):
        for g in range(4):
            for a in range(512):
                b = GEN.transform(g, a)
                self.assertIn(b, range(512))
                self.assertEqual(GEN.transform(g, b), a)

    def test_individual_orbit_certificates(self):
        for rep, expected in zip(GEN.REPS + GEN.EXTRA_REPS, GEN.SIZES + GEN.EXTRA_SIZES):
            root, rows = GEN.orbit(rep)
            self.assertEqual(root, 0)
            self.assertEqual(len(rows), expected)
            pairs = [row[0] for row in rows]
            self.assertEqual(pairs, sorted(set(pairs)))
            self.assertEqual(pairs[0], GEN.pair(*rep))
            for i, ((a, b), depth, parent, nxt) in enumerate(rows):
                self.assertTrue(0 < a < b < (a ^ b) < 512)
                for g, target in enumerate(nxt):
                    self.assertEqual(pairs[target], GEN.pair(GEN.transform(g, a), GEN.transform(g, b)))
                if i:
                    self.assertLess(rows[parent][1], depth)
                    self.assertIn(i, rows[parent][3])

    def test_fourteen_disjoint_orbits(self):
        seen = set()
        for rep in GEN.EXTRA_REPS + GEN.REPS:
            _, rows = GEN.orbit(rep)
            pairs = {row[0] for row in rows}
            self.assertFalse(pairs & seen)
            seen.update(pairs)
        self.assertEqual(len(seen), 43435)

    def test_no_untrusted_proof_escape(self):
        forbidden = re.compile(
            r"^\s*(?:axiom|constant)\b|\bsorry\b|\badmit\b|native_decide|ofReduceBool|"
            r"implemented_by|skipKernelTC|trustLevel", re.MULTILINE,
        )
        for file in ROOT.glob("QiushiPlaneOrbit*.lean"):
            self.assertIsNone(forbidden.search(file.read_text()), str(file))


if __name__ == "__main__":
    unittest.main()
