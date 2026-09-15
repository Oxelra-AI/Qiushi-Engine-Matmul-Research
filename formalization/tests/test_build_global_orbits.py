"""Exercise the private runner with a deterministic stand-in compiler."""

import fcntl
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


RUNNER = Path(__file__).resolve().parents[1] / "tools/build_global_orbits.py"
FAKE_COMPILER = f"#!{sys.executable}\n" + r'''
import os
from pathlib import Path
import sys

source = Path(sys.argv[-1])
text = source.read_text()
root = Path.cwd()
with (root / "started").open("a") as log:
    log.write(source.stem + "\n")
assert os.environ["LEAN_NUM_THREADS"] == "1"
print(text)
if "--run" in sys.argv:
    raise SystemExit(0)
output = Path(sys.argv[sys.argv.index("-o") + 1])
assert not output.exists(), "selected stale object survived"
for line in text.splitlines():
    if line.startswith("import "):
        for dependency in line.split()[1:]:
            assert (output.parent / (dependency + ".olean")).read_text() == "fresh"
if "MUTATE" in text:
    source.write_text(text + "\n-- changed\n")
if "NO_OBJECT" not in text:
    output.write_text("fresh")
raise SystemExit(1 if "FAIL" in text else 0)
'''


class GlobalOrbitBuildTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "tools").mkdir()
        self.runner = self.root / "tools/build_global_orbits.py"
        shutil.copyfile(RUNNER, self.runner)
        self.compiler = self.root / "lean"
        self.compiler.write_text(FAKE_COMPILER)
        self.compiler.chmod(0o755)
        self.environment = self.root / "environment.json"
        self.environment.write_text(json.dumps({"lean": str(self.compiler),
                                                 "lean_path": "/read-only/imports"}))
        self.base = self.root / ".local/global-orbits"
        self.output = self.base / "lib"
        self.output.mkdir(parents=True)

    def source(self, name, content="-- good"):
        (self.root / (name + ".lean")).write_text(content)
        (self.output / (name + ".olean")).write_text("stale")

    def build(self, *names, extra=()):
        return subprocess.run(
            [sys.executable, str(self.runner), "--environment", str(self.environment),
             "--jobs", "2", *extra, *(name + ".lean" for name in names)],
            cwd=self.root, capture_output=True, text=True, timeout=15)

    def receipts(self):
        return [json.loads(p.read_text()) for p in sorted(self.base.glob("build-*.json"))]

    def started(self):
        path = self.root / "started"
        return path.read_text().splitlines() if path.exists() else []

    def test_rebuilds_selected_in_dependency_order_preserves_unselected(self):
        self.source("A", "import B\n-- good")
        self.source("B")
        self.source("Unselected")
        result = self.build("A", "B")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.started(), ["B", "A"])
        self.assertEqual((self.output / "Unselected.olean").read_text(), "stale")
        receipt, = self.receipts()
        self.assertEqual(receipt["status"], "succeeded")
        self.assertEqual(receipt["not_built"], [])
        self.assertEqual(set(receipt["selected"]), {"A", "B"})
        self.assertEqual(receipt["selected"]["A"]["dependencies"], ["B"])
        self.assertEqual(receipt["environment_sha256"],
                         hashlib.sha256(self.environment.read_bytes()).hexdigest())
        self.assertEqual(receipt["results"]["A"]["object_sha256"],
                         hashlib.sha256(b"fresh").hexdigest())

    def test_failure_removes_partial_and_blocked_objects(self):
        self.source("A", "-- FAIL")
        self.source("B", "import A")
        self.source("C", "import B")
        result = self.build("A", "B", "C")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertEqual(self.started(), ["A"])
        self.assertEqual(list(self.output.glob("*.olean")), [])
        receipt, = self.receipts()
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["not_built"], ["B", "C"])
        self.assertEqual(set(receipt["results"]), {"A"})
        self.assertIsNone(receipt["results"]["A"]["object_sha256"])

    def test_receipts_and_logs_are_per_invocation_not_cached_success(self):
        self.source("A", "-- first success")
        self.assertEqual(self.build("A").returncode, 0)
        first, = self.receipts()
        first_log = Path(first["results"]["A"]["log"])
        before = first_log.read_bytes()
        self.source("A", "-- second FAIL")
        self.assertEqual(self.build("A").returncode, 1)
        original, second = self.receipts()
        self.assertEqual(original, first)
        self.assertNotEqual(first["invocation"], second["invocation"])
        self.assertEqual(first_log.read_bytes(), before)
        self.assertIn("second FAIL", Path(second["results"]["A"]["log"]).read_text())
        self.assertEqual(second["results"]["A"]["exit_code"], 1)
        self.assertFalse((self.output / "A.olean").exists())

    def test_exec_failure_is_recorded_and_blocks_dependents(self):
        self.source("A")
        self.source("B", "import A")
        self.compiler.unlink()
        self.assertEqual(self.build("A", "B").returncode, 1)
        receipt, = self.receipts()
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["not_built"], ["B"])
        self.assertIn("invocation failed", Path(receipt["results"]["A"]["log"]).read_text())
        self.assertEqual(list(self.output.glob("*.olean")), [])

    def test_source_change_rejected(self):
        self.source("A", "-- MUTATE")
        self.source("B", "import A")
        self.assertEqual(self.build("A", "B").returncode, 1)
        self.assertEqual(self.started(), ["A"])
        self.assertFalse((self.output / "A.olean").exists())
        receipt, = self.receipts()
        self.assertIn("Source changed", Path(receipt["results"]["A"]["log"]).read_text())

    def test_missing_output_rejected(self):
        self.source("A", "-- NO_OBJECT")
        self.source("B", "import A")
        self.assertEqual(self.build("A", "B").returncode, 1)
        self.assertEqual(self.started(), ["A"])
        receipt, = self.receipts()
        self.assertIn("no object", Path(receipt["results"]["A"]["log"]).read_text())

    def test_cycle_fails_without_reusing_stale_objects(self):
        self.source("A", "import B")
        self.source("B", "import A")
        self.assertEqual(self.build("A", "B").returncode, 1)
        self.assertEqual(self.started(), [])
        self.assertEqual(list(self.output.glob("*.olean")), [])
        receipt, = self.receipts()
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(receipt["not_built"], ["A", "B"])

    def test_run_is_not_an_object_build(self):
        self.source("A")
        self.assertEqual(self.build("A", extra=("--run",)).returncode, 0)
        self.assertEqual((self.output / "A.olean").read_text(), "stale")
        receipt, = self.receipts()
        self.assertTrue(receipt["run"])
        self.assertIsNone(receipt["results"]["A"]["object_sha256"])

    def test_overlapping_invocation_rejected_before_invalidation(self):
        self.source("A")
        with (self.base / "build.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            result = self.build("A")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("another global-orbit invocation", result.stderr)
        self.assertEqual((self.output / "A.olean").read_text(), "stale")
        self.assertEqual(self.started(), [])
        self.assertEqual(self.receipts(), [])


if __name__ == "__main__":
    unittest.main()
