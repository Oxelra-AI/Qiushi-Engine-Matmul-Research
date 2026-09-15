#!/usr/bin/env python3
"""Build only CalibrationRows additions in an explicitly pinned environment."""

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--environment", required=True, type=Path)
    parser.add_argument("--output", type=Path, default=Path(".local/calibration-rows"))
    parser.add_argument("--library", action="append", type=Path, default=[],
                        help="explicit additional pinned library, before the clean core")
    parser.add_argument("--jobs", type=int, choices=(1, 2), default=1,
                        help="maximum simultaneous Lean processes (default: 1)")
    parser.add_argument("sources", nargs="+",
                        help="selected CalibrationRows sources; local imports determine build order")
    args = parser.parse_args()
    config_path = args.environment.resolve()
    config = json.loads(config_path.read_text())

    def resolve(value):
        path = Path(value).expanduser()
        return (path if path.is_absolute() else config_path.parent / path).resolve()

    compiler = resolve(config["lean"])
    entries = config["lean_path"].split(os.pathsep)
    if any(not entry for entry in entries):
        parser.error("LEAN_PATH entries must be explicit and nonempty")
    libraries = [path.resolve() for path in args.library] + [resolve(s) for s in entries]
    out = args.output.resolve()
    if any(out.is_relative_to(path) or path.is_relative_to(out) for path in libraries):
        parser.error("output must not overlap an input library")
    sources = [ROOT / source for source in args.sources]
    if len(set(sources)) != len(sources):
        parser.error("sources must not repeat")
    for path in sources:
        if (path.parent != ROOT or not path.name.startswith("QiushiCalibrationRows")
                or path.suffix != ".lean"):
            parser.error("only top-level QiushiCalibrationRows*.lean sources are allowed")
    selected = {path.stem: path for path in sources}
    dependencies = {}
    for name, path in selected.items():
        imports = re.findall(r"(?m)^import\s+([^\n]+)", path.read_text())
        modules = {module for line in imports for module in line.split("--", 1)[0].split()}
        dependencies[name] = modules & selected.keys()
    remaining = set(selected)
    while remaining:
        ready = {name for name in remaining if not dependencies[name] & remaining}
        if not ready:
            parser.error("selected local imports contain a dependency cycle")
        remaining -= ready
    lib = out / "lib"
    lib.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_NUM_THREADS="1",
               LEAN_PATH=os.pathsep.join(map(str, [lib, *libraries])))
    identity = {"input": config, "input_sha256": sha(config_path), "lean": str(compiler),
                "lean_path": env["LEAN_PATH"], "output": str(out), "jobs": args.jobs,
                "selected_dependencies": {name: sorted(deps) for name, deps in dependencies.items()}}
    (out / "environment.json").write_text(json.dumps(identity, indent=2) + "\n")
    # Clear blocked dependents too: a failed root must not leave old Checks receipts.
    for path in sources:
        (out / (path.stem + ".json")).unlink(missing_ok=True)
        (lib / (path.stem + ".olean")).unlink(missing_ok=True)

    def compile_one(path):
        receipt = out / (path.stem + ".json")
        object_path = lib / (path.stem + ".olean")
        digest = sha(path)
        start = time.monotonic()
        try:
            result = subprocess.run([str(compiler), "-j1", "-o", str(object_path), path.name],
                                    cwd=ROOT, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        except BaseException:
            object_path.unlink(missing_ok=True)
            raise
        (out / (path.stem + ".log")).write_text(result.stdout)
        if result.returncode:
            object_path.unlink(missing_ok=True)
            return result.returncode, result.stdout, time.monotonic() - start
        if digest != sha(path):
            object_path.unlink(missing_ok=True)
            raise RuntimeError("Source changed during compilation: " + path.name)
        record = {"source": path.name, "source_sha256": digest,
                  "olean_sha256": sha(lib / (path.stem + ".olean")),
                  "log_sha256": sha(out / (path.stem + ".log")), "exit_code": 0,
                  "private_environment_sha256": sha(out / "environment.json")}
        receipt.write_text(json.dumps(record, indent=2) + "\n")
        return 0, result.stdout, time.monotonic() - start

    status = {name: "pending" for name in selected}
    running = {}
    # The executor context waits for every running compiler, including after failures.
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        while any(value in ("pending", "running") for value in status.values()):
            for name in selected:
                if status[name] == "pending" and any(
                        status[dep] in ("failed", "blocked") for dep in dependencies[name]):
                    status[name] = "blocked"
                    print(f"{name}.lean: blocked by a failed dependency", flush=True)
            for name, path in selected.items():
                if len(running) == args.jobs:
                    break
                if status[name] == "pending" and all(
                        status[dep] == "passed" for dep in dependencies[name]):
                    status[name] = "running"
                    running[executor.submit(compile_one, path)] = name
            if not running:
                if any(value == "pending" for value in status.values()):
                    continue
                break
            completed, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in completed:
                name = running.pop(future)
                try:
                    code, output, seconds = future.result()
                except BaseException as error:
                    code, output, seconds = 1, f"{type(error).__name__}: {error}\n", 0
                    (lib / (name + ".olean")).unlink(missing_ok=True)
                    (out / (name + ".json")).unlink(missing_ok=True)
                    (out / (name + ".log")).write_text(output)
                status[name] = "passed" if code == 0 else "failed"
                print(output, end="", flush=True)
                print(f"{name}.lean: exit {code}, {seconds:.1f}s", flush=True)
    return 0 if all(value == "passed" for value in status.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
