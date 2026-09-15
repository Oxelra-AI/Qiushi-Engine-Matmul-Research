"""Consumer rejection tests; matrix/group correctness is proved by the Lean modules."""

import importlib.util
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
SPEC = importlib.util.spec_from_file_location("global_checks", ROOT / "tools/generate_global_orbit_checks.py")
GEN = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GEN)
BASES = ROOT / ".local/global-orbits/logs/QiushiGlobalOrbitExport.log"
TRANSITIONS = ROOT / ".local/global-orbits/transitions-masks.jsonl"


class GlobalOrbitSourceTests(unittest.TestCase):
    def test_no_proof_escape(self):
        forbidden = re.compile(
            r"^\s*(?:axiom|constant)\b|\bsorry\b|\badmit\b|native_decide|ofReduceBool|"
            r"implemented_by|skipKernelTC|trustLevel", re.MULTILINE,
        )
        for path in ROOT.glob("QiushiGlobalOrbit*.lean"):
            self.assertIsNone(forbidden.search(path.read_text()), str(path))


@unittest.skipUnless(BASES.exists() and TRANSITIONS.exists(), "requires the explicit private input snapshots")
class GlobalOrbitConsumerTests(unittest.TestCase):
    def records(self):
        return [json.loads(line) for line in TRANSITIONS.read_text().splitlines()]

    def rejected(self, records):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bad.jsonl"
            path.write_text("\n".join(json.dumps(r) for r in records) + "\n")
            with self.assertRaises(ValueError):
                GEN.load_cases(BASES, path)

    def test_all_residue_cases(self):
        cases = GEN.load_cases(BASES, TRANSITIONS)
        self.assertEqual(len(cases), 496)
        self.assertEqual(sum(len(rows) for _, rows in cases), 15807)

    def test_incomplete_producer_rejected(self):
        self.rejected(self.records()[:-1])

    def test_wrong_mask_rejected(self):
        rows = self.records()
        witness = next(r for r in rows if "forward" in r)
        witness["forward"][0] ^= 1
        self.rejected(rows)

    def test_missing_extension_rejected(self):
        rows = self.records()
        index = next(i for i, r in enumerate(rows) if "forward" in r)
        del rows[index]
        rows[-1]["extensions"] -= 1
        self.rejected(rows)


if __name__ == "__main__":
    unittest.main()
