import hashlib
import json
from pathlib import Path
import pickle
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from check_frozen_rows import check


class FrozenRowsTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.project = Path(self.tmp.name) / "project"
        self.proof = Path(self.tmp.name) / "proof"
        self.relative = "assets/quotients/data/wang_f2_lb20/wang_subspace_lut.pkl"
        self.table = self.proof / self.relative
        self.table.parent.mkdir(parents=True)
        self.write_table(pickle.dumps({"lut": {17: 19}}))
        for index in range(484, 492):
            directory = self.project / "certificates" / str(index)
            directory.mkdir(parents=True)
            (directory / "tables.json").write_text(json.dumps({
                "source_rows": [{"basis": [1], "lb": 19}], "dead_witnesses": []}))

    def write_table(self, raw):
        self.table.write_bytes(raw)
        (self.proof / "manifest.json").write_text(json.dumps({"files": [{
            "path": self.relative, "sha256": hashlib.sha256(raw).hexdigest()}]}))

    def test_exact_rows_match(self):
        result = check(self.project, self.proof)
        self.assertEqual(result["status"], "pass")
        self.assertEqual(result["total_rows"], 8)

    def test_changed_value_fails(self):
        self.write_table(pickle.dumps({"lut": {17: 18}}))
        result = check(self.project, self.proof)
        self.assertEqual(result["status"], "fail")
        self.assertEqual(len(result["mismatches"]), 8)

    def test_changed_bytes_rejected(self):
        self.table.write_bytes(pickle.dumps({"lut": {17: 18}}))
        with self.assertRaisesRegex(ValueError, "manifest"):
            check(self.project, self.proof)

    def test_lfs_pointer_rejected(self):
        self.write_table(b"version https://git-lfs.github.com/spec/v1\n")
        with self.assertRaisesRegex(ValueError, "LFS"):
            check(self.project, self.proof)

    def test_pickle_globals_rejected(self):
        self.write_table(b"cbuiltins\nset\n.")
        with self.assertRaisesRegex(pickle.UnpicklingError, "primitive"):
            check(self.project, self.proof)

    def test_trailing_data_rejected(self):
        self.write_table(pickle.dumps({"lut": {17: 19}}) + b"extra")
        with self.assertRaisesRegex(ValueError, "trailing"):
            check(self.project, self.proof)


if __name__ == "__main__":
    unittest.main()
