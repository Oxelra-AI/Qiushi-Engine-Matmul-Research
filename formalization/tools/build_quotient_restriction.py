#!/usr/bin/env python3
"""Compile quotient/restriction additions using a supplied clean-build environment."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
from datetime import datetime, timezone


ROOT = Path(__file__).resolve().parents[1]
SOURCES = ["QiushiQuotientRestriction.lean", "tests/QuotientRestriction.lean"]
DEPENDENCIES = ("QiushiDefs", "QiushiBilinearSemantics")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def config_path(value, base):
    path = Path(value).expanduser()
    return (path if path.is_absolute() else base / path).resolve()


def load_environment(path):
    config = json.loads(path.read_text())
    compiler = config_path(config["lean"], path.parent)
    entries = config["lean_path"].split(os.pathsep)
    if not entries or any(not entry for entry in entries):
        raise ValueError("lean_path must contain explicit, nonempty library paths")
    libraries = [config_path(entry, path.parent) for entry in entries]
    objects = config_path(config["objects"], path.parent)
    snapshot = config_path(config["source_snapshot"], path.parent)
    if not compiler.is_file() or not snapshot.is_dir():
        raise ValueError("Compiler or clean source snapshot does not exist")
    if objects not in libraries or not objects.is_dir():
        raise ValueError("lean_path must include the clean object directory")
    revisions = [p.get("rev") for p in config["manifest"]["packages"]
                 if p.get("name") == "mathlib"]
    if len(revisions) != 1 or not re.fullmatch(r"[0-9a-f]{40,64}", revisions[0] or ""):
        raise ValueError("manifest must identify one pinned Mathlib revision")
    for name in DEPENDENCIES:
        resolved = next((library / (name + ".olean") for library in libraries
                         if (library / (name + ".olean")).is_file()), None)
        if resolved != objects / (name + ".olean"):
            raise ValueError(f"Clean dependency missing or shadowed: {name}")
    return config, compiler, libraries, objects, snapshot, revisions[0]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--environment", type=Path, required=True,
                        help="environment.json from a clean source build")
    parser.add_argument("--output", type=Path, default=Path(".local/quotient-restriction"),
                        help="private output directory (relative to the current directory)")
    parser.add_argument("sources", nargs="*", metavar="SOURCE",
                        help="optional selection of the module or its exact-type test")
    args = parser.parse_args()
    sources = args.sources or SOURCES
    if any(source not in SOURCES for source in sources) or len(set(sources)) != len(sources):
        parser.error("sources must be a non-repeating selection of " + ", ".join(SOURCES))
    environment_path = args.environment.resolve()
    config, compiler, libraries, objects, snapshot, mathlib_rev = load_environment(environment_path)
    out = args.output.resolve()
    if any(out.is_relative_to(path) or path.is_relative_to(out)
           for path in [snapshot, *libraries]) or environment_path == out / "environment.json":
        parser.error("output must be separate from input libraries, snapshot and environment")
    lib = out / "lib"
    if any((lib / (name + ".olean")).exists() for name in DEPENDENCIES):
        parser.error("private output must not shadow clean dependency objects")
    lib.mkdir(parents=True, exist_ok=True)
    (out / "receipt.json").unlink(missing_ok=True)
    env = dict(os.environ, LEAN_NUM_THREADS="1",
               LEAN_PATH=os.pathsep.join(map(str, [lib, *libraries])))
    version_text = subprocess.check_output([str(compiler), "--version"], text=True).strip()
    version = re.fullmatch(r"Lean \(version ([0-9][\w.+-]*), ([\w.-]+), "
                           r"commit ([0-9a-f]+), ([\w -]+)\)", version_text)
    if not version:
        raise ValueError("Unrecognized Lean version output; refusing to publish raw text")
    input_files = [environment_path, compiler]
    input_files += [objects / (name + ".olean") for name in DEPENDENCIES]
    input_files += [snapshot / (name + ".lean") for name in DEPENDENCIES]
    input_hashes = {path: sha(path) for path in input_files}
    environment = {"input": config, "input_environment": str(environment_path),
                   "lean": str(compiler), "lean_version": version_text,
                   "lean_path": env["LEAN_PATH"], "output": str(out), "jobs": 1}
    (out / "environment.json").write_text(json.dumps(environment, indent=2) + "\n")
    records = []
    for source in sources:
        name = Path(source).stem
        command = [str(compiler), "-j1", "-o", str(lib / (name + ".olean")), source]
        source_hash = sha(ROOT / source)
        start = time.monotonic()
        result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / (name + ".log")).write_text(result.stdout)
        print(result.stdout, end="", flush=True)
        print(f"{source}: exit {result.returncode}", flush=True)
        if result.returncode:
            return result.returncode
        if sha(ROOT / source) != source_hash:
            raise RuntimeError(f"Source changed during compilation: {source}")
        records.append({"source": source, "source_sha256": source_hash,
                        "olean_sha256": sha(lib / (name + ".olean")),
                        "log_sha256": sha(out / (name + ".log")),
                        "seconds": time.monotonic() - start, "exit_code": 0})
    if any(sha(path) != digest for path, digest in input_hashes.items()):
        raise RuntimeError("Build inputs changed during compilation")
    if sources == SOURCES:
        log = (out / "QuotientRestriction.log").read_text()
        guard = re.search(r"Standard-axiom guard passed for (\d+) declarations\.", log)
        if not guard:
            raise RuntimeError("Missing standard-axiom guard result")
        printed = {name: [dep.strip() for dep in deps.split(",")]
                   for name, deps in
                   re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log)}
        receipt = {"schema_version": 2,
                   "verified_at_utc": datetime.now(timezone.utc).isoformat(),
                   "toolchain": {"version": version[1], "target": version[2],
                                 "commit": version[3], "mode": version[4],
                                 "compiler_sha256": input_hashes[compiler]},
                   "mathlib_rev": mathlib_rev,
                   "manifest_canonical_sha256": hashlib.sha256(json.dumps(
                       config["manifest"], sort_keys=True, separators=(",", ":")).encode()).hexdigest(),
                   "input_environment_sha256": input_hashes[environment_path],
                   "private_environment_sha256": sha(out / "environment.json"),
                   "core_object_sha256": {name: input_hashes[objects / (name + ".olean")]
                                          for name in DEPENDENCIES},
                   "dependency_source_sha256": {name: input_hashes[snapshot / (name + ".lean")]
                                                for name in DEPENDENCIES},
                   "builds": records, "exact_type_tests_passed": True,
                   "axiom_guard_declarations": int(guard[1]), "printed_axioms": printed,
                   "builder_sha256": sha(Path(__file__)),
                   "scope": "Arbitrary matrix subspace quotient/restriction equivalence only"}
        (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
