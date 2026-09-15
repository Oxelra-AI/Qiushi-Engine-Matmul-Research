#!/usr/bin/env python3
"""Replay manifest root groups with the project's unchanged audit.py; never build."""

import argparse
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time


class VerificationError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def load_audit(project):
    path = project / "tools/audit.py"
    spec = importlib.util.spec_from_file_location("verification_audit", path)
    module = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(path.parent))
    try:
        spec.loader.exec_module(module)
    finally:
        sys.path.pop(0)
    return module


def validate_manifest(value, audit):
    require(isinstance(value, dict) and set(value) == {"version", "groups"},
            "manifest must contain version and groups")
    require(type(value["version"]) is int and value["version"] == 1,
            "unsupported manifest version")
    groups = value["groups"]
    require(isinstance(groups, list) and groups, "groups must be a nonempty array")
    ids, roots = set(), []
    for group in groups:
        require(isinstance(group, dict) and set(group) == {"id", "title", "modules", "roots"},
                "each group must contain id, title, modules, roots")
        name = group["id"]
        require(isinstance(name, str) and re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]*", name),
                "group id must be a safe ASCII filename component")
        require(name not in ids, "duplicate group id: " + name)
        ids.add(name)
        require(isinstance(group["title"], str) and group["title"].strip(), "empty group title")
        for key in ("modules", "roots"):
            values = group[key]
            require(isinstance(values, list) and all(isinstance(v, str) for v in values),
                    key + " must be an array of Lean names")
            audit.names(values)
        roots.extend(group["roots"])
    audit.names(roots)
    return groups


def inputs(project, environment, manifest, audit):
    files = {}

    def read(label, path):
        resolved = path.resolve(strict=True)
        raw = resolved.read_bytes()
        files[label] = {"path": str(path), "resolved": str(resolved),
                        "sha256": hashlib.sha256(raw).hexdigest()}
        return raw

    groups = validate_manifest(json.loads(read("manifest", manifest)), audit)
    config = json.loads(read("environment", environment))
    require(isinstance(config, dict), "environment must be an object")
    for key in ("lean", "lean_path"):
        require(isinstance(config.get(key), str) and config[key].strip(),
                "environment requires nonempty " + key)
    lean = (project / config["lean"]).resolve(strict=True)
    require(lean.is_file() and os.access(lean, os.X_OK)
            and lean.name == "lean" and lean.parent.name == "bin",
            "environment lean must resolve to the pinned distribution's bin/lean")
    toolchain = lean.parent.parent
    require(read("pin", project / "lean-toolchain").decode().strip() == audit.PIN,
            "project must pin exactly " + audit.PIN)
    entries = config["lean_path"].split(os.pathsep)
    require(all(entries), "lean_path must not contain empty entries")
    # Lake includes library paths for optional dependencies not yet built.
    paths = [(project / entry).resolve() for entry in entries]
    require(any(path.is_dir() for path in paths), "lean_path has no existing library directory")
    require(all(not path.exists() or path.is_dir() for path in paths),
            "existing lean_path entries must be directories")
    paths.append(toolchain / "lib/lean")
    require(paths[-1].is_dir(), "toolchain lib/lean must be an existing directory")
    for name in ("audit.py", "lean_resources.py", "AuditCommands.lean.inc", "ReplayRoots.lean"):
        read(name, project / "tools" / name)
    return {"files": files, "groups": groups, "project": str(project), "lean": str(lean),
            "toolchain": str(toolchain), "lean_path": os.pathsep.join(map(str, dict.fromkeys(paths)))}


def validate_receipt(output, group, before, audit):
    receipt = json.loads((output / "report.json").read_text())
    require(isinstance(receipt, dict), "receipt must be an object")
    for key in ("status", "extraction_status", "axiom_policy_status", "replay_status"):
        require(receipt.get(key) == "pass", "receipt " + key + " is not pass")
    expected = {key: before[key] for key in ("project", "lean", "lean_path")}
    expected.update(modules=group["modules"], roots=group["roots"], replay_scope="roots",
                    replay_targets=group["modules"], allowed_axioms=sorted(audit.ALLOWED))
    for key, value in expected.items():
        require(receipt.get(key) == value, "receipt mismatch: " + key)
    version = receipt.get("lean_version")
    require(isinstance(version, str) and re.search(
        r"\bversion " + re.escape(audit.VERSION) + r"(?:,|\))", version), "Lean version mismatch")
    commands = receipt.get("commands")
    require(isinstance(commands, list) and len(commands) == 3 and all(
        isinstance(cmd, dict) and type(cmd.get("returncode")) is int
        and cmd["returncode"] == 0 and not cmd.get("timed_out_or_interrupted") for cmd in commands),
        "incomplete or unsuccessful audit subprocesses")
    _, expected_lines = audit.generate(group["modules"], group["roots"])
    declarations = audit.parse_output((output / "extract.stdout").read_text(), expected_lines)
    require([record["name"] for record in declarations] == group["roots"],
            "declaration order or identity mismatch")
    require(receipt.get("declarations") == declarations, "declaration receipt mismatch")
    audit.axiom_policy(declarations)
    replay = audit.parse_root_replay((output / "replay-roots.stdout").read_text(),
                                    group["modules"], group["roots"])
    require(receipt.get("root_replay") == replay, "root replay receipt mismatch")
    return audit.sha256(output / "report.json")


def run_groups(groups, args, output, before, audit):
    results = [dict(id=g["id"], modules=g["modules"], roots=g["roots"], status="not_started")
               for g in groups]
    active, next_index, failed, interrupted, signalled = {}, 0, False, False, False

    def interrupt(_signum, _frame):
        nonlocal interrupted
        interrupted = True

    def notify_children():
        for proc in active:
            if proc.poll() is None:
                try:
                    proc.send_signal(signal.SIGINT)
                except ProcessLookupError:
                    pass

    previous = signal.signal(signal.SIGINT, interrupt)
    try:
        while active or (next_index < len(groups) and not failed):
            if interrupted and not signalled:
                failed, signalled = True, True
                notify_children()
            # Drain every completed result before admitting another group.
            for proc, (index, started) in list(active.items()):
                if proc.poll() is None:
                    continue
                result = results[index]
                result.update(returncode=proc.wait(), seconds=round(time.monotonic() - started, 3))
                del active[proc]
                try:
                    require(result["returncode"] == 0, "audit exited " + str(result["returncode"]))
                    result["receipt_sha256"] = validate_receipt(output / groups[index]["id"],
                                                                groups[index], before, audit)
                    result["status"] = "pass"
                except (VerificationError, audit.AuditError, OSError, ValueError,
                        KeyError, TypeError, AttributeError) as exc:
                    result.update(status="fail", error=str(exc))
                    failed = True
            while not failed and not interrupted and next_index < len(groups) and len(active) < args.jobs:
                index = next_index
                next_index += 1
                group, result = groups[index], results[index]
                child = output / group["id"]
                command = [sys.executable, str(args.project / "tools/audit.py"),
                           "--project", str(args.project), "--toolchain", before["toolchain"],
                           "--lean-path", before["lean_path"], "--replay-scope", "roots",
                           "--timeout", str(args.timeout), "--output", str(child)]
                for module in group["modules"]:
                    command += ["--module", module]
                for root in group["roots"]:
                    command += ["--root", root]
                result.update(command=command, receipt=str(child / "report.json"))
                try:
                    require(not child.exists(), "audit output already exists: " + str(child))
                    with (output / (group["id"] + ".stdout")).open("wb") as stdout, \
                            (output / (group["id"] + ".stderr")).open("wb") as stderr:
                        proc = subprocess.Popen(command, cwd=args.project, stdout=stdout, stderr=stderr,
                                                start_new_session=True)
                    active[proc] = (index, time.monotonic())
                    result["status"] = "running"
                except (VerificationError, OSError) as exc:
                    result.update(status="fail", error=str(exc))
                    failed = True
            if active:
                time.sleep(0.05)
    finally:
        # Audit owns its separate Lean process groups and cleans them on SIGINT.
        if active:
            notify_children()
            for proc in active:
                proc.wait()
        signal.signal(signal.SIGINT, previous)
    return results, interrupted


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--environment", type=Path, required=True,
                        help="current fresh-build JSON with lean and lean_path; relative entries use project")
    parser.add_argument("--manifest", type=Path, help="default: PROJECT/verification.json")
    parser.add_argument("--group", action="append", help="select a group; a subset is explicitly partial")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--timeout", type=float, default=43200,
                        help="positive finite seconds per audit subprocess, not whole-group wall time")
    parser.add_argument("--output", type=Path, help="new directory; default: PROJECT/.local/verify-*")
    args = parser.parse_args(argv)
    if args.jobs < 1 or not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error("--jobs must be positive; --timeout must be positive and finite")
    try:
        args.project = args.project.resolve(strict=True)
        args.environment = args.environment.absolute()
        args.manifest = (args.manifest or args.project / "verification.json").absolute()
        audit = load_audit(args.project)
        before = inputs(args.project, args.environment, args.manifest, audit)
        by_id = {group["id"]: group for group in before["groups"]}
        requested = args.group if args.group is not None else list(by_id)
        require(len(set(requested)) == len(requested), "duplicate --group")
        require(all(name in by_id for name in requested), "unknown --group")
        if args.output:
            output = args.output.resolve()
            require(not output.is_relative_to(Path(before["toolchain"])), "output is inside toolchain")
            output.mkdir(parents=True, exist_ok=False)
        else:
            local = args.project / ".local"
            require(not local.resolve().is_relative_to(Path(before["toolchain"])), "output is inside toolchain")
            local.mkdir(exist_ok=True)
            output = Path(tempfile.mkdtemp(prefix="verify-", dir=local))
    except Exception as exc:
        parser.error(str(exc))
    report = {"version": 1, "status": "fail", "full_manifest_pass": False,
              "selection": "all_manifest_groups" if set(requested) == set(by_id) else "partial",
              "manifest_groups": list(by_id), "requested_groups": requested, "inputs_before": before,
              "scope": "Only requested manifest roots and their dependencies are replayed. "
                       "Selected PASS is not full-project acceptance or evidence of source freshness.",
              "jobs": args.jobs, "timeout_per_subprocess": args.timeout}
    try:
        results, interrupted = run_groups([by_id[name] for name in requested], args, output, before, audit)
        report.update(results=results, interrupted=interrupted)
        after = inputs(args.project, args.environment, args.manifest, audit)
        report["inputs_after"] = after
        require(after == before, "manifest, environment, resolved paths, or audit inputs changed")
        require(not interrupted, "interrupted; no verification claim")
        require(all(result["status"] == "pass" for result in results), "not all requested groups passed")
        report["status"] = "pass"
        report["full_manifest_pass"] = report["selection"] == "all_manifest_groups"
    except (VerificationError, audit.AuditError, OSError, ValueError, KeyError, TypeError, KeyboardInterrupt) as exc:
        report["error"] = str(exc) or type(exc).__name__
    receipt = output / "report.json"
    receipt.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n")
    print(f"{report['status'].upper()} ({report['selection']}, {len(requested)}/{len(by_id)} groups): {receipt}")
    print(report["scope"])
    return 0 if report["status"] == "pass" else 1


if __name__ == "__main__":
    sys.exit(main())
