#!/usr/bin/env python3
"""Compile private orbit modules against an explicitly supplied clean environment."""

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--environment", type=Path, required=True)
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--jobs", type=int, choices=(1, 2), default=1)
    parser.add_argument("files", nargs="*", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    output = root / ".local/finite-orbits/lib"
    output.mkdir(parents=True, exist_ok=True)
    config = json.loads(args.environment.read_text())
    env = dict(os.environ, LEAN_PATH=str(output) + ":" + config["lean_path"])
    files = sorted(root.glob("QiushiPlaneOrbit*.lean")) if args.all else args.files
    if not files:
        parser.error("supply files or --all")
    files = {file.stem: root / file for file in files}
    dependencies = {}
    for name, file in files.items():
        imports = {part for line in file.read_text().splitlines() if line.startswith("import ")
                   for part in line.split()[1:]}
        dependencies[name] = imports & files.keys()
    log_dir = output.parent / "logs"
    log_dir.mkdir(exist_ok=True)
    results = {}

    def compile_file(file):
        print(f"Checking {file}", flush=True)
        start = time.monotonic()
        result = subprocess.run(
            [config["lean"], "--root", str(file.parent),
             "-o", str(output / (file.stem + ".olean")), str(file)],
            cwd=root, env=env, text=True, capture_output=True,
        )
        elapsed = time.monotonic() - start
        (log_dir / (file.stem + ".log")).write_text(result.stdout + result.stderr)
        if result.stdout or result.stderr:
            print(result.stdout + result.stderr, flush=True)
        print(f"{'Checked' if result.returncode == 0 else 'FAILED'} {file.name} ({elapsed:.1f}s)", flush=True)
        return {"exit_code": result.returncode, "seconds": elapsed,
                "sha256": hashlib.sha256(file.read_bytes()).hexdigest()}

    pending = set(files)
    running = {}
    failed = False
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            if not failed:
                ready = sorted(name for name in pending if dependencies[name] <= results.keys())
                for name in ready[:args.jobs - len(running)]:
                    pending.remove(name)
                    running[pool.submit(compile_file, files[name])] = name
            if not running:
                break
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                name = running.pop(future)
                results[name] = future.result()
                failed |= results[name]["exit_code"] != 0
    receipt = {"environment": str(args.environment.resolve()),
               "environment_sha256": hashlib.sha256(args.environment.read_bytes()).hexdigest(),
               "jobs": args.jobs, "results": results, "not_built": sorted(pending)}
    receipt_text = json.dumps(receipt, indent=2) + "\n"
    (output.parent / f"build-{time.time_ns()}.json").write_text(receipt_text)
    (output.parent / "last-build.json").write_text(receipt_text)
    if failed or pending:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
