"""Compile generated frozen bindings against an immutable clean core library.

At most four one-thread Lean processes run concurrently. Outputs and resumable
content-bound receipts are private; no Lake build or parent output is modified.
"""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--core-build", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--module", action="append")
    args = parser.parse_args()
    if not 1 <= args.jobs <= 4 or args.out.resolve().is_relative_to(args.core_build.resolve()):
        parser.error("require 1..4 jobs and a private output directory")
    manifest = json.loads(args.manifest.read_text())
    modules = manifest["modules"]
    core = json.loads((args.core_build / "environment.json").read_text())
    if core["objects"] != str(args.core_build / "lib"):
        raise ValueError("clean core identity mismatch")
    lean_version = subprocess.check_output([core["lean"], "--version"], text=True).strip()
    lib = args.out / "lib"
    lib.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=f"{lib}:{core['lean_path']}")
    external, keys, wanted = {}, {}, set()

    def visit(name):
        if name in keys:
            return keys[name]
        if name not in modules:
            path = args.core_build / "lib" / (name.replace(".", "/") + ".olean")
            external[name] = sha(path)
            return external[name]
        wanted.add(name)
        path = args.source / f"{name}.lean"
        source_hash = sha(path)
        if source_hash != modules[name]["sha256"]:
            raise ValueError(f"source changed after generation: {name}")
        payload = [source_hash, core["lean"], env["LEAN_PATH"],
                   [(dep, visit(dep)) for dep in modules[name]["imports"]]]
        keys[name] = hashlib.sha256(json.dumps(payload).encode()).hexdigest()
        return keys[name]

    for name in args.module or ["QiushiFrozenWangAudit"]:
        if name not in modules:
            raise ValueError(f"unknown generated module: {name}")
        visit(name)
    (args.out / "environment.json").write_text(json.dumps({
        "lean": core["lean"], "lean_path": env["LEAN_PATH"], "jobs": args.jobs,
        "core_build": str(args.core_build), "external_olean_sha256": external,
        "manifest_sha256": sha(args.manifest)}, indent=2) + "\n")
    completed, results = set(), {}
    for name in sorted(wanted):
        receipt = args.out / f"{name}.result.json"
        obj = lib / f"{name}.olean"
        log = args.out / f"{name}.log"
        if receipt.exists() and obj.exists() and log.exists():
            result = json.loads(receipt.read_text())
            if (result.get("key") == keys[name] and result["returncode"] == 0
                    and result["object_sha256"] == sha(obj)
                    and result["log_sha256"] == sha(log)):
                completed.add(name)
                results[name] = result
    print(f"Modules: {len(wanted)}; verified cached: {len(completed)}", flush=True)

    def run(name):
        start = time.monotonic()
        obj, log = lib / f"{name}.olean", args.out / f"{name}.log"
        cmd = [core["lean"], "-j1", "-o", str(obj), f"{name}.lean"]
        with log.open("w") as stream:
            proc = subprocess.run(cmd, cwd=args.source, env=env, stdout=stream, stderr=subprocess.STDOUT)
        result = {"key": keys[name], "command": cmd, "returncode": proc.returncode,
                  "seconds": round(time.monotonic() - start, 3), "log_sha256": sha(log)}
        if proc.returncode == 0:
            result["object_sha256"] = sha(obj)
        (args.out / f"{name}.result.json").write_text(json.dumps(result, indent=2) + "\n")
        return result

    remaining, running, failures = wanted - completed, {}, []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while remaining or running:
            ready = sorted(name for name in remaining
                           if all(dep not in wanted or dep in completed for dep in modules[name]["imports"]))
            if not failures:
                for name in ready[:args.jobs - len(running)]:
                    remaining.remove(name)
                    running[pool.submit(run, name)] = name
            if not running:
                break
            done, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in done:
                name = running.pop(future)
                result = results[name] = future.result()
                if result["returncode"]:
                    failures.append(name)
                    print(f"FAIL {name}: {(args.out / (name + '.log')).read_text()[-8000:]}", flush=True)
                else:
                    completed.add(name)
                    print(f"PASS {len(completed)}/{len(wanted)} {name} {result['seconds']}s", flush=True)
    summary = {"modules": len(wanted), "ok": len(completed), "failed": failures,
               "blocked": sorted(remaining)}
    if "QiushiFrozenWangAudit" in completed:
        log = (args.out / "QiushiFrozenWangAudit.log").read_text()
        axioms = [line for line in log.splitlines() if "depends on axioms:" in line]
        expected = {f"QiushiMatmul.FrozenWang.plane{plane}_{kind}"
                    for plane in range(484, 492) for kind in ("source", "dead")}
        summary["axiom_audit_pass"] = len(axioms) == 16 and all(
            line.endswith("depends on axioms: [propext, Classical.choice, Quot.sound]") for line in axioms
        ) and {line.split("'")[1] for line in axioms} == expected
        if not summary["axiom_audit_pass"]:
            summary["failed"].append("axiom_audit")
        elif not failures and not remaining:
            source_hashes = {name: sha(args.source / f"{name}.lean") for name in sorted(wanted)}
            if any(value != modules[name]["sha256"] for name, value in source_hashes.items()):
                raise ValueError("source changed during compilation")
            inputs = {}
            for path, value in manifest["inputs"].items():
                path = Path(path)
                key = f"certificates/{path.parent.name}/tables.json" if path.name == "tables.json" else path.name
                inputs[key] = value
            verification = {"status": "pass", "modules": len(wanted),
                            "compiler_process_limit": args.jobs, "lean_threads_per_process": 1,
                            "lean_version": lean_version, "external_olean_sha256": external,
                            "package_revisions": {p["name"]: p["rev"] for p in core["manifest"]["packages"]},
                            "source_tree_sha256": hashlib.sha256(json.dumps(source_hashes, sort_keys=True).encode()).hexdigest(),
                            "source_sha256": source_hashes, "inputs_sha256": inputs,
                            "certificate_sha256": manifest["certificate_sha256"],
                            "source_rows": manifest["source_rows"], "dead_rows": manifest["dead_rows"],
                            "total_rows": manifest["total_rows"], "rows_per_plane": manifest["rows_per_plane"],
                            "unique_spaces": manifest["unique_spaces"],
                            "audited_declarations": sorted(expected),
                            "axioms": ["propext", "Classical.choice", "Quot.sound"],
                            "warning_count": sum((args.out / f"{name}.log").read_text().count(": warning:") for name in wanted),
                            "scope": manifest["scope"]}
            (args.out / "verification.json").write_text(json.dumps(verification, indent=2) + "\n")
    (args.out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary), flush=True)
    return int(bool(summary["failed"] or summary["blocked"]))


if __name__ == "__main__":
    raise SystemExit(main())
