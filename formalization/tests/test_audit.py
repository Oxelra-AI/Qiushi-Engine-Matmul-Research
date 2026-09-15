"""Run with python3 -m unittest -v test_audit from this directory."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import audit


BASE = Path(__file__).resolve().parent
class UnitTests(unittest.TestCase):
    def test_insufficient_stack_fails_before_loading_artifacts(self):
        args = SimpleNamespace(module=["Main"], root=["Result"])
        with patch.object(audit, "configure_process_stack", side_effect=RuntimeError("stack limit")):
            with self.assertRaisesRegex(audit.AuditError, "stack limit"):
                audit.audit(args, BASE, {"commands": []})

    def test_empty_duplicate_and_injected_names_rejected(self):
        for values in ([], ["X", "X"], ["X\naxiom evil : False"], ["X;"], ["--fresh"]):
            with self.subTest(values=values), self.assertRaises(audit.AuditError):
                audit.names(values)

    def test_axiom_parser_fails_closed(self):
        self.assertEqual(audit.parse_axioms("'X' does not depend on any axioms", "X"), [])
        for message in ("", "'Other' does not depend on any axioms", "'X' depends on axioms: []"):
            with self.subTest(message=message), self.assertRaises(audit.AuditError):
                audit.parse_axioms(message, "X")

    def test_empty_output_rejected(self):
        with self.assertRaises(audit.AuditError):
            audit.parse_output("", {1: ("record", "X"), 2: ("axioms", "X")})

    def test_fresh_replay_covers_every_probe_import(self):
        for modules in (["Main"], ["Main", "Extra"], ["Main", "Lean"],
                        ["Main", "Lean.Elab.Print"]):
            code, _ = audit.generate(modules, ["Result"])
            imported = [line.removeprefix("import ") for line in code.splitlines()
                        if line.startswith("import ")]
            self.assertEqual(audit.replay_targets(modules), imported)

    def test_probe_does_not_require_the_full_lean_umbrella(self):
        code, _ = audit.generate(["Main"], ["Result"])
        self.assertNotIn("import Lean\n", code)
        self.assertIn("import Lean.Elab.Print\n", code)

    def test_all_nonstandard_axioms_rejected(self):
        audit.axiom_policy([{"name": "X", "axioms": sorted(audit.ALLOWED)}])
        for axiom in ("sorryAx", "Lean.ofReduceBool", "FalseAx", "propext.fake"):
            with self.subTest(axiom=axiom), self.assertRaises(audit.AuditError):
                audit.axiom_policy([{"name": "X", "axioms": [axiom]}])

    def test_partial_duplicate_and_truncated_output_rejected(self):
        expected = {1: ("record", "X"), 2: ("axioms", "X")}
        record = {"name": "X", "module": "M", "universes": [], "type": "True", "axioms": []}

        def message(line, data):
            return json.dumps({"severity": "information", "pos": {"line": line}, "data": data})

        first = message(1, audit.MARKER + json.dumps(record))
        second = message(2, "'X' does not depend on any axioms")
        self.assertEqual(audit.parse_output(first + "\n" + second, expected)[0]["type"], "True")
        for raw in (first, first + "\n" + first + "\n" + second):
            with self.assertRaises(audit.AuditError):
                audit.parse_output(raw, expected)
        record["type"] = "True \u22ef"
        with self.assertRaises(audit.AuditError):
            audit.parse_output(message(1, audit.MARKER + json.dumps(record)) + "\n" + second, expected)

    def test_nonzero_checker_process_fails_closed(self):
        with tempfile.TemporaryDirectory(prefix="process-test-", dir=BASE) as directory:
            report = {"commands": []}
            with self.assertRaises(audit.AuditError):
                audit.run([sys.executable, "-c", "raise SystemExit(7)"], BASE,
                          os.environ.copy(), 10, Path(directory), "checker", report)
            self.assertEqual(report["commands"][0]["returncode"], 7)

    def test_root_replay_requires_identical_complete_acknowledgements(self):
        record = {"modules": ["Main"], "roots": ["Result"], "declarations": 10}
        start = "QIUSHI_REPLAY_BEGIN " + json.dumps(record)
        finish = "QIUSHI_REPLAY_PASS " + json.dumps(record)
        self.assertEqual(audit.parse_root_replay(start + "\n" + finish,
                                                ["Main"], ["Result"]), record)
        for raw in (start, finish, start + "\n" + start,
                    start + "\n" + finish + "\nextra"):
            with self.subTest(raw=raw), self.assertRaises(audit.AuditError):
                audit.parse_root_replay(raw, ["Main"], ["Result"])
        for key, value in (("modules", ["Other"]), ("roots", []),
                           ("declarations", 0), ("declarations", True),
                           ("declarations", 11)):
            broken = dict(record, **{key: value})
            with self.subTest(key=key, value=value), self.assertRaises(audit.AuditError):
                audit.parse_root_replay(start + "\nQIUSHI_REPLAY_PASS " + json.dumps(broken),
                                        ["Main"], ["Result"])



if __name__ == "__main__":
    unittest.main()
