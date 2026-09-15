"""Fail-closed receipt tests. Mock compilation; do not claim Lean verification."""

import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch


SPEC = importlib.util.spec_from_file_location(
    "builder", Path(__file__).with_name("build_calibration_rows.py"))
BUILDER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BUILDER)


class ReceiptTests(unittest.TestCase):
    def test_failed_rebuild_removes_old_success_and_partial_object(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "src"
            source.mkdir()
            (source / "QiushiCalibrationRowsTest.lean").write_text("-- fixture\n")
            environment = root / "input.json"
            environment.write_text(json.dumps({"lean": str(root / "compiler"),
                                              "lean_path": str(root / "inputs")}))
            out = root / "out"
            receipt = out / "QiushiCalibrationRowsTest.json"
            obj = out / "lib/QiushiCalibrationRowsTest.olean"
            argv = ["builder", "--environment", str(environment), "--output", str(out),
                    "QiushiCalibrationRowsTest.lean"]

            def compiler(returncode):
                def run(command, **kwargs):
                    self.assertFalse(receipt.exists())
                    self.assertFalse(obj.exists())
                    self.assertIn("-j1", command)
                    obj.write_bytes(b"complete" if returncode == 0 else b"partial")
                    return subprocess.CompletedProcess(command, returncode, "test output\n")
                return run

            with patch.object(BUILDER, "ROOT", source), patch.object(sys, "argv", argv):
                with patch.object(BUILDER.subprocess, "run", side_effect=compiler(0)):
                    self.assertEqual(BUILDER.main(), 0)
                self.assertTrue(receipt.exists())
                self.assertTrue(obj.exists())
                with patch.object(BUILDER.subprocess, "run", side_effect=compiler(1)):
                    self.assertEqual(BUILDER.main(), 1)
                self.assertFalse(receipt.exists())
                self.assertFalse(obj.exists())
                self.assertEqual((out / "QiushiCalibrationRowsTest.log").read_text(),
                                 "test output\n")

    def test_parallel_dependencies_block_checks_and_wait_for_running_jobs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "src"
            source.mkdir()
            names = ["QiushiCalibrationRows", "QiushiCalibrationRowsPlaneA",
                     "QiushiCalibrationRowsPlaneB", "QiushiCalibrationRowsChecks"]
            texts = ["-- root\n", f"import {names[0]}\n", f"import {names[0]}\n",
                     f"import {names[1]}\nimport {names[2]}\n"]
            out = root / "out"
            (out / "lib").mkdir(parents=True)
            for name, text in zip(names, texts):
                (source / (name + ".lean")).write_text(text)
                (out / (name + ".json")).write_text("old success")
                (out / "lib" / (name + ".olean")).write_bytes(b"old object")
            environment = root / "input.json"
            environment.write_text(json.dumps({"lean": str(root / "compiler"),
                                              "lean_path": str(root / "inputs")}))
            argv = ["builder", "--environment", str(environment), "--output", str(out),
                    "--jobs", "2", *[name + ".lean" for name in reversed(names)]]
            lock = threading.Lock()
            barrier = threading.Barrier(2, timeout=2)
            started, finished = [], []
            active, maximum = 0, 0

            def compiler(command, **kwargs):
                nonlocal active, maximum
                name = Path(command[-1]).stem
                with lock:
                    if name != names[0]:
                        self.assertIn(names[0], finished)
                    started.append(name)
                    active += 1
                    maximum = max(maximum, active)
                self.assertFalse((out / (name + ".json")).exists())
                self.assertFalse((out / "lib" / (name + ".olean")).exists())
                if name in names[1:3]:
                    barrier.wait()
                if name == names[2]:
                    time.sleep(0.05)
                (out / "lib" / (name + ".olean")).write_bytes(b"new or partial")
                with lock:
                    finished.append(name)
                    active -= 1
                return subprocess.CompletedProcess(command, int(name == names[1]), "")

            with patch.object(BUILDER, "ROOT", source), patch.object(sys, "argv", argv), \
                    patch.object(BUILDER.subprocess, "run", side_effect=compiler):
                self.assertEqual(BUILDER.main(), 1)
            self.assertEqual(maximum, 2)
            self.assertEqual(active, 0)
            self.assertCountEqual(started, names[:3])
            self.assertCountEqual(finished, names[:3])
            for name in (names[1], names[3]):
                self.assertFalse((out / (name + ".json")).exists())
                self.assertFalse((out / "lib" / (name + ".olean")).exists())
            self.assertTrue((out / (names[2] + ".json")).exists())


if __name__ == "__main__":
    unittest.main()
