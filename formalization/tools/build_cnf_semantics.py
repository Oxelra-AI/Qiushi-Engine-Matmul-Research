#!/usr/bin/env python3
"""Compile only the private semantics modules against a read-only pinned environment."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--environment", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("modules", nargs="+")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    out = args.output.resolve() if args.output else root / ".local" / "cnf-semantics"
    lib = out / "lib"
    logs = out / "logs"
    lib.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    environment = json.loads(args.environment.read_text())
    env = dict(os.environ, LEAN_PATH=str(lib) + ":" + environment["lean_path"])
    for module in args.modules:
        source = root / (module + ".lean")
        target = lib / (module + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        command = [environment["lean"], "-DwarningAsError=true", "-o", str(target), str(source)]
        result = subprocess.run(command, cwd=root, env=env, text=True, capture_output=True)
        log = logs / (module.replace("/", "_") + ".log")
        log.write_text(result.stdout + result.stderr)
        record = {"module": module, "command": command, "exit_code": result.returncode,
                  "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                  "environment": str(args.environment.resolve()), "lean_path": env["LEAN_PATH"]}
        if result.returncode == 0:
            record["olean_sha256"] = hashlib.sha256(target.read_bytes()).hexdigest()
        log.with_suffix(".json").write_text(json.dumps(record, indent=2) + "\n")
        print(module, "exit", result.returncode, flush=True)
        print(result.stdout + result.stderr, end="", flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
