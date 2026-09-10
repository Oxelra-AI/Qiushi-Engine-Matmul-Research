#!/usr/bin/env python3
"""Run positive-control and small ladder tests for wang_domain_dfs_safe.

The positive-control part forces known A-supports through the native enumerator.
For a known length-N support, --force-only requires the exact support to be
accepted at full depth by the same selection, counter, and propagation code.
This catches false deletion of known solutions.
"""
from __future__ import annotations

import json, subprocess, sys
from pathlib import Path

ROOT = Path("research/research_record")
BIN = ROOT / "workspace/scripts/wang_domain_dfs_safe"
OUTDIR = ROOT / "workspace/data/wang_native/ladder_safe"
CTRL = ROOT / "workspace/data/wang_native/controls"
OUTDIR.mkdir(parents=True, exist_ok=True)


def run(cmd, timeout=300):
    p = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    return {"cmd": cmd, "returncode": p.returncode, "stdout": p.stdout, "stderr": p.stderr}


def support_prefix(path: Path):
    data = json.loads(path.read_text())
    ds = sorted(set(int(x) for x in data["a_multiset"] if int(x) > 0))
    return ds, data


def native_force(name, cons, target, support_path, timeout=120):
    ds, data = support_prefix(support_path)
    out = OUTDIR / f"{name}.json"
    used = OUTDIR / f"{name}.used_rows.json"
    cmd = [str(BIN), "--constraints", str(cons), "--target", str(target), "--force-prefix", ",".join(map(str, ds)), "--force-only", "--timeout", str(timeout), "--output", str(out), "--used-output", str(used)]
    res = run(cmd, timeout=timeout+30)
    parsed = None
    if out.exists():
        parsed = json.loads(out.read_text())
    return {"name": name, "support_kind": data.get("kind"), "support_path": str(support_path), "distinct_prefix_size": len(ds), "native_result": parsed, "process": {"returncode": res["returncode"], "stderr_tail": res["stderr"][-2000:]}}


def main():
    summary = {"status": "ok", "tests": []}
    # Compile binary first.
    comp = run(["g++", "-O3", "-march=native", "-std=c++17", "-o", str(BIN), str(ROOT / "workspace/scripts/wang_domain_dfs_safe.cpp")], timeout=120)
    summary["compile"] = {"returncode": comp["returncode"], "stderr_tail": comp["stderr"][-2000:]}
    if comp["returncode"] != 0:
        summary["status"] = "compile_failed"
        print(json.dumps(summary, indent=2)); return

    # Controls expected to exist after extract_known_supports.py.
    e11_len21_cons = ROOT / "workspace/data/wang_native/e11_ladder/e11_wang_cap5_len21.bin"
    full_len23_cons = ROOT / "workspace/data/wang_native/full_tensor/full_wang512_cap5_len23_all_dim9.bin"
    tests = []
    if e11_len21_cons.exists():
        tests.append(native_force("e11_poolrow0_len21_force", e11_len21_cons, 21, CTRL / "e11_poolrow0_support.json"))
        tests.append(native_force("e11_poolrow304_len21_force", e11_len21_cons, 21, CTRL / "e11_poolrow304_support.json"))
    else:
        summary["missing_e11_len21_constraints"] = str(e11_len21_cons)
    if full_len23_cons.exists() and (CTRL / "full_rank23_flipcpd_text_support.json").exists():
        tests.append(native_force("full_rank23_len23_force", full_len23_cons, 23, CTRL / "full_rank23_flipcpd_text_support.json"))
    else:
        summary["missing_full_len23_or_control"] = [str(full_len23_cons), str(CTRL / "full_rank23_flipcpd_text_support.json")]
    summary["tests"] = tests
    summary["all_forced_accept"] = all(t.get("native_result") and t["native_result"].get("forced_reached_target") and t["native_result"].get("solutions", 0) >= 1 for t in tests)
    (OUTDIR / "forced_ladder_summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
