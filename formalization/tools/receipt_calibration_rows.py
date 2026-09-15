#!/usr/bin/env python3
"""Verify completed CalibrationRows build receipts and emit a path-free summary."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, required=True)
    parser.add_argument("--output", type=Path,
                        default=ROOT / "QiushiCalibrationRowsVerification.json")
    args = parser.parse_args()
    records = []
    for source in sorted(ROOT.glob("QiushiCalibrationRows*.lean")):
        record = json.loads((args.build / (source.stem + ".json")).read_text())
        paths = {"source_sha256": source,
                 "olean_sha256": args.build / "lib" / (source.stem + ".olean"),
                 "log_sha256": args.build / (source.stem + ".log")}
        if record["source"] != source.name or record["exit_code"] != 0:
            raise ValueError("No successful build for " + source.name)
        for field, path in paths.items():
            if sha(path) != record[field]:
                raise ValueError("Changed artifact: " + source.name + " " + field)
        records.append(record)
    guards = {}
    printed = {}
    for name, expected in (("QiushiCalibrationRowsChecks", 21),
                           ("QiushiCalibrationRowsAllChecks", 40)):
        log = (args.build / (name + ".log")).read_text()
        if f"Standard-axiom guard passed for {expected} declarations." not in log:
            raise ValueError("Missing expected axiom guard: " + name)
        guards[name] = expected
        for declaration, dependencies in re.findall(
                r"'([^']+)' depends on axioms: \[([^]]*)\]", log):
            axioms = [dependency.strip() for dependency in dependencies.split(",")]
            if not set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}:
                raise ValueError("Forbidden axiom in " + declaration)
            printed[declaration] = axioms
    environment = json.loads((args.build / "environment.json").read_text())
    compiler = Path(environment["lean"])
    version = subprocess.check_output([str(compiler), "--version"], text=True).strip()
    match = re.fullmatch(r"Lean \(version ([0-9][\w.+-]*), ([\w.-]+), "
                         r"commit ([0-9a-f]+), ([\w -]+)\)", version)
    if not match:
        raise ValueError("Unrecognized compiler version; refusing raw public output")
    manifest = environment["input"]["manifest"]
    mathlib = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    result = {"schema_version": 1, "result": "PASS", "compiled_modules": records,
              "module_count": len(records), "axiom_guards": guards, "printed_axioms": printed,
              "toolchain": {"version": match[1], "target": match[2], "commit": match[3],
                            "mode": match[4], "compiler_sha256": sha(compiler)},
              "mathlib_rev": mathlib,
              "manifest_sha256": hashlib.sha256(json.dumps(
                  manifest, sort_keys=True, separators=(",", ":")).encode()).hexdigest(),
              "scope": "29210 checked quotient rows, exact coverage and masses for eight planes; "
                       "stored-label equality interface only, not its numerical instantiation"}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Verified {len(records)} module receipts and both standard-axiom guards.")


if __name__ == "__main__":
    main()
