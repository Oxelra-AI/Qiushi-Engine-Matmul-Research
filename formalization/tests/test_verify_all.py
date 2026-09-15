"""Wrapper tests with fake audit evidence/processes only; no Lean proof is run."""

import contextlib
import copy
import io
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import audit
import verify_all as verify


class VerifyTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="verify-unit-")
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        self.project = self.base / "project"
        (self.project / "tools").mkdir(parents=True)
        (self.project / "lib").mkdir()
        for name in ("audit.py", "lean_resources.py", "AuditCommands.lean.inc", "ReplayRoots.lean"):
            shutil.copyfile(TOOLS / name, self.project / "tools" / name)
        (self.project / "lean-toolchain").write_text(audit.PIN + "\n")
        toolchain = self.base / "toolchain"
        (toolchain / "bin").mkdir(parents=True)
        (toolchain / "lib/lean").mkdir(parents=True)
        (toolchain / "bin/lean").write_text("unit fixture, never executed\n")
        (toolchain / "bin/lean").chmod(0o755)
        self.environment = self.base / "environment.json"
        self.environment.write_text(json.dumps({"lean": "../toolchain/bin/lean", "lean_path": "lib"}))
        self.manifest = self.project / "verification.json"
        self.groups = [{"id": name, "title": name.upper(), "modules": ["Import." + name],
                        "roots": ["Qiushi.Test." + name]} for name in ("a", "b", "c")]
        self.write_manifest()
        self.output_index = 0
        self.events, self.live, self.max_live = [], set(), 0

    def write_manifest(self, value=None):
        self.manifest.write_text(json.dumps(value if value is not None else
                                            {"version": 1, "groups": self.groups}))

    def before(self):
        return verify.inputs(self.project, self.environment, self.manifest, audit)

    def emit_receipt(self, output, group, options):
        before = self.before()
        _, expected = audit.generate(group["modules"], group["roots"])
        lines = []
        axioms = options.get("axioms", [])
        for line, (kind, root) in expected.items():
            if kind == "record":
                data = audit.MARKER + json.dumps({"name": root, "module": "Origin.Module",
                    "type": "True", "universes": [], "axioms": axioms})
            else:
                data = (f"'{root}' depends on axioms: [" + ", ".join(axioms) + "]" if axioms else
                        f"'{root}' does not depend on any axioms")
            lines.append(json.dumps({"severity": "information", "pos": {"line": line}, "data": data}))
        raw = "\n".join(lines) + "\n"
        (output / "extract.stdout").write_text(raw)
        replay = {"modules": group["modules"], "roots": group["roots"], "declarations": 10}
        (output / "replay-roots.stdout").write_text(
            "QIUSHI_REPLAY_BEGIN " + json.dumps(replay) + "\nQIUSHI_REPLAY_PASS " + json.dumps(replay) + "\n")
        receipt = {key: before[key] for key in ("project", "lean", "lean_path")}
        receipt.update(status="pass", extraction_status="pass", axiom_policy_status="pass",
                       replay_status="pass", replay_scope="roots", replay_targets=group["modules"],
                       modules=group["modules"], roots=group["roots"], allowed_axioms=sorted(audit.ALLOWED),
                       declarations=audit.parse_output(raw, expected), root_replay=replay,
                       lean_version="Lean (version " + audit.VERSION + ", unit fixture)",
                       commands=[{"returncode": 0} for _ in range(3)])
        if "change" in options:
            options["change"](receipt)
        if not options.get("missing"):
            (output / "report.json").write_text("{" if options.get("malformed") else json.dumps(receipt))
        if "artifact_change" in options:
            options["artifact_change"](output)

    def factory(self, plan):
        owner = self

        class FakeProcess:
            def __init__(self, command, **kwargs):
                owner.assertEqual(command[1], str(owner.project / "tools/audit.py"))
                owner.assertTrue(kwargs["start_new_session"])
                owner.assertEqual(kwargs["cwd"], owner.project)
                owner.assertEqual(command[command.index("--replay-scope") + 1], "roots")
                owner.assertEqual(command[command.index("--lean-path") + 1], owner.before()["lean_path"])
                self.output = Path(command[command.index("--output") + 1])
                owner.assertFalse(self.output.exists())
                self.name = self.output.name
                self.options = plan.get(self.name, {})
                if self.options.get("launch_error"):
                    raise OSError("synthetic process launch failure")
                self.output.mkdir()
                self.remaining = self.options.get("polls", 1)
                self.returncode = None
                owner.live.add(self.name)
                owner.max_live = max(owner.max_live, len(owner.live))
                owner.events.append(("start", self.name))

            def poll(self):
                if self.returncode is None:
                    self.remaining -= 1
                    if self.remaining <= 0:
                        group = next(g for g in owner.groups if g["id"] == self.name)
                        owner.emit_receipt(self.output, group, self.options)
                        self.returncode = self.options.get("exit", 0)
                        owner.live.remove(self.name)
                        owner.events.append(("finish", self.name))
                        if "after" in self.options:
                            self.options["after"]()
                return self.returncode

            def wait(self):
                while self.poll() is None:
                    pass
                return self.returncode

            def send_signal(self, signum):
                owner.assertEqual(signum, signal.SIGINT)
                self.remaining = 0
                self.options = dict(self.options, exit=130)

        return FakeProcess

    def run_cli(self, extra=(), plan=None, default_output=False):
        self.output_index += 1
        output = self.base / ("out-" + str(self.output_index))
        argv = ["--project", str(self.project), "--environment", str(self.environment), *extra]
        if not default_output:
            argv += ["--output", str(output)]
        stdout = io.StringIO()
        with patch.object(verify.subprocess, "Popen", side_effect=self.factory(plan or {})), \
                patch.object(verify.time, "sleep"), contextlib.redirect_stdout(stdout):
            code = verify.main(argv)
        if default_output:
            output = next((self.project / ".local").glob("verify-*"))
        return code, json.loads((output / "report.json").read_text()), stdout.getvalue(), output

    def test_all_groups_pass_only_as_manifest_scope(self):
        code, report, stdout, output = self.run_cli(default_output=True)
        self.assertEqual(code, 0)
        self.assertTrue(report["full_manifest_pass"])
        self.assertEqual(report["selection"], "all_manifest_groups")
        self.assertEqual(report["requested_groups"], ["a", "b", "c"])
        self.assertEqual(report["inputs_before"], report["inputs_after"])
        self.assertEqual(report["jobs"], 2)
        self.assertEqual(report["timeout_per_subprocess"], 43200)
        self.assertIn("not full-project acceptance", stdout)
        for result in report["results"]:
            self.assertEqual(result["receipt_sha256"], audit.sha256(output / result["id"] / "report.json"))

    def test_selected_groups_are_explicitly_partial_and_names_are_unchanged(self):
        self.groups[0]["roots"] = ["Qiushi.CNF.finite_formula"]
        self.write_manifest()
        code, report, stdout, _ = self.run_cli(["--group", "a", "--jobs", "1", "--timeout", "2.5"])
        self.assertEqual(code, 0)
        self.assertFalse(report["full_manifest_pass"])
        self.assertEqual(report["selection"], "partial")
        self.assertEqual(report["manifest_groups"], ["a", "b", "c"])
        self.assertEqual(report["results"][0]["roots"], ["Qiushi.CNF.finite_formula"])
        self.assertIn("1/3 groups", stdout)

    def test_explicit_manifest_and_repeated_group_options(self):
        self.manifest.write_text("invalid default manifest\n")
        self.manifest = self.base / "other-manifest.json"
        self.write_manifest()
        code, report, _, _ = self.run_cli(["--manifest", str(self.manifest),
                                           "--group", "c", "--group", "a"])
        self.assertEqual(code, 0)
        self.assertEqual(report["requested_groups"], ["c", "a"])
        self.assertEqual(report["selection"], "partial")
        self.assertEqual(report["inputs_before"]["files"]["manifest"]["path"], str(self.manifest))

    def test_invalid_manifest_fails_before_output_or_process(self):
        invalid = [None, {}, {"version": True, "groups": self.groups}, {"version": 2, "groups": self.groups},
                   {"version": 1, "groups": []}]
        for field, value in (("id", "../escape"), ("title", ""), ("modules", []),
                             ("roots", ["Bad;name"]), ("roots", [2]), ("modules", "Main")):
            groups = copy.deepcopy(self.groups)
            groups[0][field] = value
            invalid.append({"version": 1, "groups": groups})
        for field in ("id", "roots"):
            groups = copy.deepcopy(self.groups)
            groups[1][field] = groups[0][field]
            invalid.append({"version": 1, "groups": groups})
        for value in invalid:
            with self.subTest(value=value):
                self.manifest.write_text(json.dumps(value))
                with self.assertRaises(SystemExit) as exc, contextlib.redirect_stderr(io.StringIO()):
                    self.run_cli()
                self.assertEqual(exc.exception.code, 2)
                self.assertFalse((self.base / ("out-" + str(self.output_index))).exists())
        self.assertEqual(self.events, [])

    def test_invalid_cli_values_and_selection_fail_before_running(self):
        for extra in (["--jobs", "0"], ["--jobs", "-1"], ["--timeout", "0"],
                      ["--timeout", "nan"], ["--timeout", "inf"], ["--timeout", "-2"],
                      ["--group", "missing"], ["--group", "a", "--group", "a"]):
            with self.subTest(extra=extra), self.assertRaises(SystemExit), \
                    contextlib.redirect_stderr(io.StringIO()):
                self.run_cli(extra)
        self.assertEqual(self.events, [])

    def test_bad_environment_and_pin_rejected_without_ambient_fallback(self):
        valid = self.environment.read_text()
        for config in ({}, {"lean": "../toolchain/bin/lean", "lean_path": ""},
                       {"lean": "../toolchain/bin/lean", "lean_path": "absent"},
                       {"lean": "../toolchain/bin/lean", "lean_path": "lib:lean-toolchain"},
                       {"lean": "../toolchain/bin/lean", "lean_path": "lib:"},
                       {"lean": "absent", "lean_path": "lib"}):
            self.environment.write_text(json.dumps(config))
            with self.subTest(config=config), self.assertRaises(SystemExit), \
                    contextlib.redirect_stderr(io.StringIO()), patch.dict(os.environ, LEAN_PATH="lib"):
                self.run_cli()
        self.environment.write_text(valid)
        (self.project / "lean-toolchain").write_text("leanprover/lean4:v0.0.0\n")
        with self.assertRaises(SystemExit), contextlib.redirect_stderr(io.StringIO()):
            self.run_cli()
        self.assertEqual(self.events, [])

    def test_unbuilt_optional_library_paths_are_preserved(self):
        config = json.loads(self.environment.read_text())
        config["lean_path"] = "unbuilt:lib:optional/.lake/build/lib/lean"
        self.environment.write_text(json.dumps(config))
        code, report, _, _ = self.run_cli(["--group", "a"])
        self.assertEqual(code, 0)
        self.assertEqual(report["status"], "pass")
        paths = report["inputs_before"]["lean_path"].split(os.pathsep)
        self.assertEqual(paths[:3], [str(self.project / part) for part in
                                    config["lean_path"].split(os.pathsep)])
        self.assertFalse((self.project / "unbuilt").exists())

    def test_nonzero_missing_or_malformed_receipts_fail_closed(self):
        for options in ({"exit": 7}, {"missing": True}, {"malformed": True}):
            with self.subTest(options=options):
                code, report, _, _ = self.run_cli(["--group", "a"], {"a": options})
                self.assertEqual(code, 1)
                self.assertFalse(report["full_manifest_pass"])
                self.assertEqual(report["results"][0]["status"], "fail")

    def test_receipt_stages_and_exact_identity(self):
        changes = [(key, "not_completed") for key in
                   ("status", "extraction_status", "axiom_policy_status", "replay_status")]
        changes += [("modules", ["Other"]), ("roots", ["Other"]), ("replay_targets", []),
                    ("replay_scope", "modules"), ("allowed_axioms", []),
                    ("allowed_axioms", sorted(audit.ALLOWED) + ["sorryAx"]),
                    ("project", "elsewhere"), ("lean", "elsewhere"), ("lean_path", "elsewhere"),
                    ("lean_version", "Lean (version 0.0.0, fixture)"), ("declarations", []),
                    ("root_replay", {}), ("commands", [{"returncode": 1}] * 3)]
        for key, value in changes:
            with self.subTest(key=key, value=value):
                code, report, _, _ = self.run_cli(["--group", "a"], {
                    "a": {"change": lambda receipt: receipt.update({key: value})}})
                self.assertEqual(code, 1)
                self.assertEqual(report["results"][0]["status"], "fail")

    def test_standard_axiom_subsets_pass_and_forbidden_axioms_fail(self):
        for axioms, expected in (([], 0), (["Quot.sound"], 0), (sorted(audit.ALLOWED), 0), (["sorryAx"], 1)):
            with self.subTest(axioms=axioms):
                code, _, _, _ = self.run_cli(["--group", "a"], {"a": {"axioms": axioms}})
                self.assertEqual(code, expected)

    def test_fresh_raw_outputs_must_match_the_receipt(self):
        for name in ("extract.stdout", "replay-roots.stdout"):
            with self.subTest(name=name):
                code, _, _, _ = self.run_cli(["--group", "a"], {
                    "a": {"artifact_change": lambda output: (output / name).write_text("")}})
                self.assertEqual(code, 1)

    def test_bad_structured_output_is_a_recorded_failure(self):
        for raw in ("[]\n", "null\n", '{"severity":"information","pos":null}\n'):
            with self.subTest(raw=raw):
                code, report, _, _ = self.run_cli(["--group", "a"], {
                    "a": {"artifact_change": lambda output: (output / "extract.stdout").write_text(raw)}})
                self.assertEqual(code, 1)
                self.assertEqual(report["results"][0]["status"], "fail")

    def test_unchanged_input_hashes_and_resolved_paths_are_required(self):
        for path in (self.manifest, self.environment, self.project / "tools/audit.py"):
            original = path.read_text()
            with self.subTest(path=path.name):
                code, report, _, _ = self.run_cli(["--group", "a"], {
                    "a": {"after": lambda: path.write_text(original + "\n")}})
                self.assertEqual(code, 1)
                self.assertIn("changed", report["error"])
            path.write_text(original)
        (self.project / "lib").rmdir()
        first, second = self.base / "first-lib", self.base / "second-lib"
        first.mkdir()
        second.mkdir()
        (self.project / "lib").symlink_to(first, target_is_directory=True)

        def retarget():
            (self.project / "lib").unlink()
            (self.project / "lib").symlink_to(second, target_is_directory=True)

        code, report, _, _ = self.run_cli(["--group", "a"], {"a": {"after": retarget}})
        self.assertEqual(code, 1)
        self.assertIn("changed", report["error"])

    def test_concurrency_is_bounded_and_failure_blocks_pending_but_waits_for_started(self):
        code, report, _, _ = self.run_cli(plan={"a": {"exit": 9}, "b": {"polls": 8}})
        self.assertEqual(code, 1)
        self.assertEqual(self.max_live, 2)
        self.assertEqual(self.events, [("start", "a"), ("start", "b"), ("finish", "a"), ("finish", "b")])
        self.assertEqual([r["status"] for r in report["results"]], ["fail", "pass", "not_started"])
        self.assertEqual(self.live, set())

    def test_serial_option_and_successful_parallel_queue(self):
        for jobs in (1, 2):
            self.events, self.max_live = [], 0
            code, _, _, _ = self.run_cli(["--jobs", str(jobs)], {"a": {"polls": 5}, "b": {"polls": 5}})
            self.assertEqual(code, 0)
            self.assertEqual(self.max_live, jobs)
            self.assertEqual(self.live, set())

    def test_launch_failure_does_not_abandon_a_started_group(self):
        code, report, _, _ = self.run_cli(plan={"a": {"polls": 8}, "b": {"launch_error": True}})
        self.assertEqual(code, 1)
        self.assertEqual([r["status"] for r in report["results"]], ["pass", "fail", "not_started"])
        self.assertEqual(self.events, [("start", "a"), ("finish", "a")])
        self.assertEqual(self.live, set())

    def test_existing_output_is_never_reused(self):
        output = self.base / "out-1"
        output.mkdir()
        old = output / "report.json"
        old.write_text('{"status":"pass"}\n')
        with self.assertRaises(SystemExit), contextlib.redirect_stderr(io.StringIO()):
            self.run_cli()
        self.assertEqual(old.read_text(), '{"status":"pass"}\n')
        self.assertEqual(self.events, [])

    def test_output_inside_toolchain_is_rejected(self):
        with self.assertRaises(SystemExit), contextlib.redirect_stderr(io.StringIO()):
            verify.main(["--project", str(self.project), "--environment", str(self.environment),
                         "--output", str(self.base / "toolchain/output")])
        self.assertFalse((self.base / "toolchain/output").exists())

    @unittest.skipUnless(os.name == "posix", "audit process groups require POSIX")
    def test_sigint_waits_for_audits_to_reap_nested_fake_lean_processes(self):
        # Execute the real audit.run cleanup with sleeping Python children, not Lean.
        script = f'''import sys
sys.path.insert(0, {str(TOOLS)!r})
from audit import *
if __name__ == "__main__":
    output = Path(sys.argv[sys.argv.index("--output") + 1])
    output.mkdir()
    (output / "audit.pid").write_text(str(os.getpid()))
    child = "import os,time; from pathlib import Path; Path(" + repr(str(output / "child.pid")) + ").write_text(str(os.getpid())); time.sleep(30)"
    try:
        run([sys.executable, "-c", child], output, os.environ.copy(), 15, output, "fake-lean", {{"commands": []}})
    except AuditError:
        (output / "cleaned").write_text("nested child reaped")
        sys.exit(1)
'''
        (self.project / "tools/audit.py").write_text(script)
        output = self.base / "interrupt-output"
        proc = subprocess.Popen([sys.executable, str(TOOLS / "verify_all.py"),
                                 "--project", str(self.project), "--environment", str(self.environment),
                                 "--output", str(output)], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                text=True, start_new_session=True)
        try:
            deadline = time.monotonic() + 10
            ready = [output / name / "child.pid" for name in ("a", "b")]
            while not all(path.exists() for path in ready) and time.monotonic() < deadline:
                if proc.poll() is not None:
                    self.fail("wrapper exited before both fake children started: " + str(proc.communicate()))
                time.sleep(0.02)
            self.assertTrue(all(path.exists() for path in ready))
            proc.send_signal(signal.SIGINT)
            stdout, stderr = proc.communicate(timeout=10)
            self.assertEqual(proc.returncode, 1, stdout + stderr)
            report = json.loads((output / "report.json").read_text())
            self.assertTrue(report["interrupted"])
            self.assertFalse(report["full_manifest_pass"])
            self.assertEqual(report["results"][2]["status"], "not_started")
            for path in ready:
                self.assertTrue((path.parent / "cleaned").exists())
                with self.assertRaises(ProcessLookupError):
                    os.kill(int(path.read_text()), 0)
        finally:
            if proc.poll() is None:
                proc.send_signal(signal.SIGINT)
                try:
                    proc.communicate(timeout=5)
                except subprocess.TimeoutExpired:
                    proc.kill()
                    proc.communicate()
            for path in output.glob("*/*.pid"):
                try:
                    os.kill(int(path.read_text()), signal.SIGKILL)
                except ProcessLookupError:
                    pass


if __name__ == "__main__":
    unittest.main()
