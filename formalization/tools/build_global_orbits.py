#!/usr/bin/env python3
"""Build global-orbit modules in independent output with pinned, read-only imports."""

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--environment", type=Path, required=True)
    parser.add_argument("--jobs", type=int, choices=range(1, 9), default=2)
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--run", action="store_true")
    parser.add_argument("files", nargs="*", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    base = root / ".local/global-orbits"
    base.mkdir(parents=True, exist_ok=True)
    with (base / "build.lock").open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            parser.error("another global-orbit invocation owns this output directory")
        build(args, root, base, parser)


def build(args, root, base, parser):
    output, logs = base / "lib", base / "logs"
    output.mkdir(parents=True, exist_ok=True)
    logs.mkdir(exist_ok=True)
    environment_bytes = args.environment.read_bytes()
    config = json.loads(environment_bytes)
    imports = [str(output), str(root / ".local/finite-orbits/lib"), config["lean_path"]]
    env = dict(os.environ, LEAN_PATH=":".join(imports), LEAN_NUM_THREADS="1")
    paths = sorted(root.glob("QiushiGlobalOrbit*.lean")) if args.all else args.files
    if not paths or (args.run and len(paths) != 1):
        parser.error("supply source files; --run requires exactly one")
    files = {p.stem: (root / p).resolve() for p in paths}
    if len(files) != len(paths):
        parser.error("source module names must be unique")
    source_bytes = {name: p.read_bytes() for name, p in files.items()}
    hashes = {name: hashlib.sha256(data).hexdigest() for name, data in source_bytes.items()}
    dependencies = {
        name: {part for line in data.decode().splitlines() if line.startswith("import ")
               for part in line.split()[1:]} & files.keys()
        for name, data in source_bytes.items()
    }
    invocation = f"{time.time_ns()}-{os.getpid()}"
    invocation_logs = logs / invocation
    invocation_logs.mkdir()
    receipt_path = base / f"build-{invocation}.json"
    receipt = {"invocation": invocation, "status": "running",
               "environment": str(args.environment.resolve()),
               "environment_sha256": hashlib.sha256(environment_bytes).hexdigest(),
               "imports": imports, "jobs": args.jobs, "lean_num_threads": 1,
               "run": args.run,
               "selected": {n: {"source": str(p), "sha256": hashes[n],
                                "dependencies": sorted(dependencies[n])}
                            for n, p in files.items()},
               "results": {}, "not_built": sorted(files)}

    def write_receipt():
        temporary = receipt_path.with_suffix(".tmp")
        temporary.write_text(json.dumps(receipt, indent=2) + "\n")
        temporary.replace(receipt_path)

    write_receipt()
    # Invalidate the entire selected set, including dependents never launched.
    # Unselected imports remain explicitly outside this invocation's replay scope.
    if not args.run:
        for name in files:
            (output / (name + ".olean")).unlink(missing_ok=True)

    def compile_file(p):
        print("Checking", p.name, flush=True)
        start = time.monotonic()
        artifact = output / (p.stem + ".olean")
        command = [config["lean"], "--root", str(p.parent)]
        command += ["--run"] if args.run else ["-o", str(artifact)]
        try:
            result = subprocess.run(command + [str(p)], cwd=root, env=env,
                                    text=True, capture_output=True)
            exit_code = result.returncode
            content = result.stdout + result.stderr
            if hashlib.sha256(p.read_bytes()).hexdigest() != hashes[p.stem]:
                exit_code = 1
                content += "\nSource changed during invocation; result rejected.\n"
            if exit_code == 0 and not args.run and not artifact.is_file():
                exit_code = 1
                content += "\nCompiler produced no object; result rejected.\n"
        except OSError as error:
            exit_code, content = 1, f"Compiler invocation failed: {error}\n"
        if exit_code != 0 and not args.run:
            artifact.unlink(missing_ok=True)
        log_path = invocation_logs / (p.stem + ".log")
        log_path.write_text(content)
        # Keep the legacy convenience path; receipts bind the immutable run log.
        (logs / (p.stem + ".log")).write_text(content)
        if content and not args.run:
            print(content, flush=True)
        elapsed = time.monotonic() - start
        print("Checked" if exit_code == 0 else "FAILED", p.name,
              f"({elapsed:.1f}s)", flush=True)
        return {"exit_code": exit_code, "seconds": elapsed,
                "source": str(p), "sha256": hashes[p.stem], "log": str(log_path),
                "object_sha256": hashlib.sha256(artifact.read_bytes()).hexdigest()
                if exit_code == 0 and not args.run else None}

    pending, running, results = set(files), {}, {}
    failed = False
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            if not failed:
                succeeded = {n for n, result in results.items() if result["exit_code"] == 0}
                ready = sorted(n for n in pending if dependencies[n] <= succeeded)
                for n in ready[:args.jobs - len(running)]:
                    pending.remove(n)
                    running[pool.submit(compile_file, files[n])] = n
            if not running:
                break
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                name = running.pop(future)
                results[name] = future.result()
                failed |= results[name]["exit_code"] != 0
            receipt.update(results=results, not_built=sorted(pending))
            write_receipt()
    receipt.update(status="failed" if failed or pending else "succeeded",
                   results=results, not_built=sorted(pending))
    write_receipt()
    print("Receipt", receipt_path, flush=True)
    if failed or pending:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
