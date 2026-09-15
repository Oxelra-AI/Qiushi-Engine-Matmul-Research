#!/usr/bin/env python3
"""Check completed private build receipts and publish bounded semantic evidence."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys


MODULES = ["QiushiBooleanCopies", "QiushiSequentialCounter", "QiushiCNFDisjoint",
           "QiushiCardinalityCNF", "QiushiExactPrefixCNF", "QiushiOccupationCNF"]
TESTS = ["tests/CNFEncodingSamples", "tests/CNFSemanticsAxioms"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--build-dir", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    build = args.build_dir.resolve()
    sources = {}
    expected = set()
    for module in MODULES + TESTS:
        source = root / (module + ".lean")
        receipt = json.loads((build / "logs" / (module.replace('/', '_') + ".json")).read_text())
        assert receipt["exit_code"] == 0, module
        assert receipt["source_sha256"] == sha(source), (module, "source changed after build")
        assert receipt["olean_sha256"] == sha(build / "lib" / (module + ".olean")), module
        sources[str(source.relative_to(root))] = sha(source)
        if module in MODULES:
            text = source.read_text()
            assert not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", text), module
            expected.update("Qiushi.CNF." + name for name in
                            re.findall(r"^(?:@\[[^\]]+\] )?theorem (\w+)", text, re.M))
    log_path = build / "logs/tests_CNFSemanticsAxioms.log"
    log = log_path.read_text()
    audited = {}
    for line in log.splitlines():
        match = re.fullmatch(r"'([^']+)' depends on axioms: \[(.*)\]", line)
        if match:
            deps = re.sub(r"\.\{[^}]*\}", "", match[2]).split(", ")
            assert set(deps) <= {"propext", "Classical.choice", "Quot.sound"}, (match[1], deps)
            assert match[1] not in audited
            audited[match[1]] = deps
        match = re.fullmatch(r"'([^']+)' does not depend on any axioms", line)
        if match:
            assert match[1] not in audited
            audited[match[1]] = []
    assert set(audited) == expected, (expected - set(audited), set(audited) - expected)
    assert len(expected) == 67, len(expected)
    test = subprocess.run([sys.executable, str(root / "tests/test_cnf_semantics.py"),
                           "--lean-log", str(build / "logs/tests_CNFEncodingSamples.log")],
                          check=True, capture_output=True, text=True)
    comparison = json.loads(test.stdout)
    environment = json.loads(Path(receipt["environment"]).read_text())
    version = subprocess.run([environment["lean"], "--version"], check=True,
                             capture_output=True, text=True).stdout.strip()
    mathlib = next(p for p in environment["manifest"]["packages"] if p["name"] == "mathlib")
    evidence = root / "evidence/cnf-semantics"
    evidence.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(log_path, evidence / "statements-and-axioms.log")
    encoders = ["proof/assets/occupation/scripts/dim2_cnf_cert.py",
                "proof/assets/structural/scripts/transparent_unary_dim2_cnf.py",
                "reports/en/main.tex"]
    result = {"verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "lean": version, "mathlib_rev": mathlib["rev"], "theorems_audited": len(expected),
              "axiom_union": sorted({axiom for deps in audited.values() for axiom in deps}),
              "source_sha256": sources, "read_source_sha256": {p: sha(root.parent / p) for p in encoders},
              "statement_axiom_log_sha256": sha(evidence / "statements-and-axioms.log"),
              "encoder_comparison": comparison,
              "scope": "Generic Boolean-copy and explicit prefix-counter semantics only",
              "pysat_cxx_implementation_formally_verified": False,
              "frozen_dimacs_identity_verified": False, "original_drat_replayed": False,
              "parent_main_certificate_rebuilt": False}
    (evidence / "verification.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
