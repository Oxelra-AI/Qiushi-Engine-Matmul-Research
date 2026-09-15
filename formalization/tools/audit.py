#!/usr/bin/env python3
"""Audit already-built Lean 4.33.1 declarations without building the project."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time

from lean_resources import configure_process_stack


ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
VERSION = "4.33.1"
PIN = "leanprover/lean4:v" + VERSION
LEAN_FLAGS = ["--threads=1", "-s262144"]
PROBE_IMPORTS = ["Lean.Elab.ElabRules", "Lean.Elab.Print", "Lean.Util.CollectAxioms"]
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
MARKER = "MATMUL_AUDIT_JSON "


class AuditError(Exception):
    pass


def names(values):
    if not values or len(values) != len(set(values)):
        raise AuditError("supply a nonempty list of distinct names")
    if any(not NAME.fullmatch(value) for value in values):
        raise AuditError("only explicit, ordinary dotted ASCII Lean names are supported")
    return values


def sha256(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def run(command, cwd, env, timeout, output, label, report):
    stdout = output / (label + ".stdout")
    stderr = output / (label + ".stderr")
    entry = {"command": list(map(str, command)), "cwd": str(cwd),
             "stdout": str(stdout), "stderr": str(stderr)}
    report["commands"].append(entry)
    started = time.monotonic()
    with stdout.open("wb") as out, stderr.open("wb") as err:
        proc = subprocess.Popen(command, cwd=cwd, env=env, stdout=out, stderr=err,
                                start_new_session=True)
        try:
            proc.wait(timeout=timeout)
        except (subprocess.TimeoutExpired, KeyboardInterrupt):
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
            entry["timed_out_or_interrupted"] = True
            raise AuditError(f"{label}: timeout or interruption; no verification claim")
        finally:
            entry["seconds"] = round(time.monotonic() - started, 3)
            entry["returncode"] = proc.returncode
    if proc.returncode:
        raise AuditError(f"{label}: exit {proc.returncode}; see {stdout} and {stderr}")
    return stdout.read_text(encoding="utf-8")


def parse_axioms(message, root):
    if message == f"'{root}' does not depend on any axioms":
        return []
    prefix = f"'{root}' depends on axioms: ["
    if not message.startswith(prefix) or not message.endswith("]"):
        raise AuditError(f"missing or malformed #print axioms output: {root}")
    result = [part.strip() for part in message[len(prefix):-1].split(",")]
    names(result)
    return result


def parse_output(raw, expected):
    records, printed = {}, {}
    for line in raw.splitlines():
        msg = json.loads(line)
        if msg.get("severity") != "information":
            raise AuditError(f"Lean diagnostic: {msg.get('data', msg)}")
        line_number = msg.get("pos", {}).get("line")
        if line_number not in expected:
            raise AuditError("unexpected Lean output; refusing incomplete or ambiguous evidence")
        kind, root = expected[line_number]
        data = msg["data"]
        target = records if kind == "record" else printed
        if root in target:
            raise AuditError(f"duplicate {kind} output: {root}")
        if kind == "record":
            if not data.startswith(MARKER):
                raise AuditError(f"missing structured record: {root}")
            record = json.loads(data[len(MARKER):])
            if record.get("name") != root:
                raise AuditError(f"declaration identity mismatch: {root}")
            names([record["module"]])
            ty = record.get("type")
            if not isinstance(ty, str) or not ty.strip() or any(
                    mark in ty for mark in ("\u22ef", "\u2026")):
                raise AuditError(f"missing or elided type: {root}")
            axs = record.get("axioms")
            if not isinstance(axs, list) or any(not isinstance(a, str) for a in axs):
                raise AuditError(f"invalid axiom array: {root}")
            if axs:
                names(axs)
            target[root] = record
        else:
            target[root] = {"text": data, "axioms": parse_axioms(data, root)}
    roots = {root for _, root in expected.values()}
    if set(records) != roots or set(printed) != roots:
        raise AuditError("absent declaration, full type, or #print axioms result")
    for root, record in records.items():
        if set(record["axioms"]) != set(printed[root]["axioms"]):
            raise AuditError(f"axiom outputs disagree: {root}")
        record["print_axioms"] = printed[root]["text"]
    return list(records.values())


def axiom_policy(records):
    violations = {r["name"]: sorted(set(r["axioms"]) - ALLOWED) for r in records
                  if set(r["axioms"]) - ALLOWED}
    if violations:
        raise AuditError("forbidden axioms: " + json.dumps(violations, sort_keys=True))


def generate(modules, roots):
    lines = ["import " + module for module in replay_targets(modules)]
    lines += Path(__file__).with_name("AuditCommands.lean.inc").read_text().splitlines()
    expected = {}
    for root in roots:
        lines.append("audit_decl " + root)
        expected[len(lines)] = ("record", root)
        lines.append("set_option pp.universes false in")
        lines.append("#print axioms " + root)
        expected[len(lines)] = ("axioms", root)
    return "\n".join(lines) + "\n", expected


def replay_targets(modules):
    # Every audited declaration must be imported by the probe. Fresh replay
    # already checks each direct import's complete transitive closure.
    return list(dict.fromkeys([*modules, *PROBE_IMPORTS]))


def parse_root_replay(raw, modules, roots):
    lines = raw.splitlines()
    if len(lines) != 2:
        raise AuditError("incomplete or unexpected root replay output")
    records = []
    for line, marker in zip(lines, ("QIUSHI_REPLAY_BEGIN ", "QIUSHI_REPLAY_PASS ")):
        if not line.startswith(marker):
            raise AuditError("missing root replay acknowledgement")
        record = json.loads(line[len(marker):])
        if record.get("modules") != modules or record.get("roots") != roots:
            raise AuditError("root replay identity mismatch")
        count = record.get("declarations")
        if type(count) is not int or count < len(roots):
            raise AuditError("invalid dependency closure count")
        records.append(record)
    if records[0] != records[1]:
        raise AuditError("root replay acknowledgements disagree")
    return records[1]


def audit(args, output, report):
    modules, roots = names(args.module), names(args.root)
    try:
        report["process_stack"] = configure_process_stack()
    except RuntimeError as error:
        raise AuditError(str(error)) from error
    project = args.project.resolve(strict=True)
    toolchain = args.toolchain.resolve(strict=True)
    if output.is_relative_to(toolchain):
        raise AuditError("audit output must be outside the toolchain")
    if (project / "lean-toolchain").read_text().strip() != PIN:
        raise AuditError(f"project must pin exactly {PIN}")
    lean = (toolchain / "bin/lean").resolve(strict=True)
    checker = (toolchain / "bin/leanchecker").resolve(strict=True)
    if lean.parent != toolchain / "bin" or checker.parent != lean.parent:
        raise AuditError("Lean and leanchecker must be siblings in the pinned distribution")
    source = toolchain / "src/lean/LeanChecker.lean"
    if not source.is_file():
        raise AuditError("matching local LeanChecker.lean source is required")
    env = os.environ.copy()
    env["LEAN_SYSROOT"] = str(toolchain)
    search = args.lean_path if args.lean_path is not None else env.get("LEAN_PATH")
    if not search:
        raise AuditError("LEAN_PATH is required; invoke under the project's lake env")
    paths = [Path(p).resolve() if Path(p).is_absolute() else (project / p).resolve()
             for p in search.split(os.pathsep) if p]
    paths.append(toolchain / "lib/lean")
    paths = list(dict.fromkeys(paths))
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    report.update(project=str(project), lean_path=env["LEAN_PATH"], roots=roots,
                  modules=modules, lean=str(lean), leanchecker=str(checker),
                  lean_sha256=sha256(lean), leanchecker_sha256=sha256(checker),
                  leanchecker_source=str(source), leanchecker_source_sha256=sha256(source))
    version = run([lean, *LEAN_FLAGS, "--version"], project, env, args.timeout, output, "version", report)
    if not re.search(r"\bversion " + re.escape(VERSION) + r"(?:,|\))", version):
        raise AuditError(f"Lean version mismatch: {version.strip()}")
    report["lean_version"] = version.strip()
    # Snapshot available olean parts by identity/size/mtime/ctime. This detects ordinary
    # concurrent builds without hashing the entire mathlib distribution twice.
    def snapshot():
        result = {}
        for base in paths:
            if base.is_dir():
                for file in base.rglob("*.olean*"):
                    st = file.stat()
                    result[str(file)] = [st.st_dev, st.st_ino, st.st_size,
                                         st.st_mtime_ns, st.st_ctime_ns]
        return result
    before = snapshot()
    report["olean_artifact_count"] = len(before)
    (output / "olean-snapshot.json").write_text(json.dumps(before, indent=2) + "\n")
    code, expected = generate(modules, roots)
    probe = output / "Audit.lean"
    probe.write_text(code, encoding="utf-8")
    raw = run([lean, *LEAN_FLAGS, "--json", probe], project, env, args.timeout, output, "extract", report)
    report["declarations"] = parse_output(raw, expected)
    report["extraction_status"] = "pass"
    axiom_policy(report["declarations"])
    report["axiom_policy_status"] = "pass"
    scope = getattr(args, "replay_scope", "modules")
    targets = replay_targets(modules) if scope == "modules" else modules
    report["replay_scope"] = scope
    report["replay_targets"] = targets
    report["target_oleans"] = {}
    for index, module in enumerate(targets):
        relative = Path(*module.split(".")).with_suffix(".olean")
        artifact = next((base / relative for base in paths if (base / relative).is_file()), None)
        if artifact is None:
            raise AuditError(f"missing compiled module: {module}")
        report["target_oleans"][module] = {"path": str(artifact), "sha256": sha256(artifact)}
        if scope == "modules":
            raw = run([checker, "--fresh", "--verbose", module], project, env,
                      args.timeout, output, f"replay-{index:03}", report)
            if raw.strip() != f"replaying {module} with --fresh":
                raise AuditError(f"unexpected leanchecker acknowledgement: {module}")
    if scope == "roots":
        driver = Path(__file__).with_name("ReplayRoots.lean").resolve(strict=True)
        replay_source = toolchain / "src/lean/Lean/Replay.lean"
        report["replay_driver_sha256"] = sha256(driver)
        report["kernel_replay_source_sha256"] = sha256(replay_source)
        raw = run([lean, *LEAN_FLAGS, "--run", driver, ",".join(modules), *roots], project, env,
                  args.timeout, output, "replay-roots", report)
        report["root_replay"] = parse_root_replay(raw, modules, roots)
        if sha256(driver) != report["replay_driver_sha256"]:
            raise AuditError("replay driver changed during audit")
    if snapshot() != before:
        raise AuditError("olean artifacts changed during audit; rerun after builds finish")
    report["replay_status"] = "pass"
    report["status"] = "pass"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--module", action="append", required=True)
    parser.add_argument("--root", action="append", required=True)
    parser.add_argument("--lean-path", help="override inherited LEAN_PATH; relative entries use project")
    parser.add_argument("--replay-scope", choices=("modules", "roots"), default="modules",
                        help="modules: official leanchecker --fresh on all imports; roots: "
                             "official Environment.replay from empty on selected roots and dependencies")
    parser.add_argument("--timeout", type=float, default=300, help="seconds per subprocess")
    parser.add_argument("--output", type=Path, help="new directory outside project/toolchain")
    args = parser.parse_args()
    if not 0 < args.timeout < float("inf"):
        parser.error("--timeout must be positive and finite")
    if args.output:
        output = args.output.resolve()
        if output.is_relative_to(args.toolchain.resolve()):
            parser.error("output must be outside toolchain")
        output.mkdir(parents=True, exist_ok=False)
    else:
        local = args.project.resolve() / '.local'
        local.mkdir(exist_ok=True)
        output = Path(tempfile.mkdtemp(prefix="audit-", dir=local))
    report = {"status": "fail", "extraction_status": "not_completed",
              "axiom_policy_status": "not_completed", "replay_status": "not_completed",
              "replay_scope": args.replay_scope,
              "allowed_axioms": sorted(ALLOWED), "commands": [],
              "scope": "compiled declaration types/axioms and selected fresh replay scope; not premise discharge, "
                       "source freshness, independent kernel implementation, or hostile-code sandbox"}
    try:
        audit(args, output, report)
    except (AuditError, OSError, ValueError, KeyError, TypeError, KeyboardInterrupt) as exc:
        report["error"] = str(exc) or type(exc).__name__
    (output / "report.json").write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n")
    print(f"{report['status'].upper()}: {output / 'report.json'}")
    if report["status"] != "pass":
        print(report.get("error", "audit failed"), file=sys.stderr)
    return 0 if report["status"] == "pass" else 1


if __name__ == "__main__":
    sys.exit(main())
