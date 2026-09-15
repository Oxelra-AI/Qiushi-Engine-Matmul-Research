"""Replay reserved certificate data; compiled Lean theorems remain authoritative."""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT / "tools"), str(ROOT / "tests")]
from generate_certificate import emit_checks, emit_data, finish, span
from global_orbit_unused_certificate import transport, word_code
from test_certificate import check_ray

EXPECTED = {
    398: [161, 96, 20, 10],
    399: [164, 96, 20, 10],
    401: [261, 96, 20, 10],
    402: [391, 96, 20, 10],
    403: [304, 161, 68, 10],
    404: [309, 162, 68, 10],
    406: [276, 179, 68, 10],
    407: [257, 163, 84, 10],
    408: [262, 163, 84, 10],
}


def check_paths(meta, cert):
    leaves = {leaf["path"]: leaf for leaf in cert["branch"]["certs"]}
    assert len(leaves) == len(cert["branch"]["certs"])
    visited = set()

    def visit(node, path, lower, upper):
        assert node["path"] == path
        if node["type"] == "leaf":
            leaf = leaves[path]
            assert leaf["lower"] == lower and leaf["upper"] == upper
            for row in leaf["used_rows"]:
                if row["type"] in ("branch_upper", "branch_lower"):
                    bounds = upper if row["type"] == "branch_upper" else lower
                    assert bounds[str(row["label"] - 1)] == row["bound"]
            visited.add(path)
        else:
            assert node["type"] == "branch"
            label, floor = node["label"] - 1, node["floor"]
            assert label in meta["live_list"] and isinstance(floor, int)
            visit(node["left"], path + "L", lower, dict(upper, **{str(label): floor}))
            visit(node["right"], path + "R", dict(lower, **{str(label): floor + 1}), upper)

    visit(cert["branch"]["tree"], "", {}, {})
    assert visited == set(leaves)


def verify(node):
    directory = ROOT / "certificates" / f"global-unused{node}"
    data = {name: json.loads((directory / (name + ".json")).read_text())
            for name in ("tables", "branch", "sources", "transport-witnesses", "generation")}
    meta, cert, ledger = data["tables"], data["branch"], data["sources"]
    assert (meta["plane"], meta["basis"], meta["target"]) == (node, EXPECTED[node], 16)
    assert cert["basis"] == meta["basis"]
    witnesses = {int(k): v for k, v in data["transport-witnesses"].items()}
    rows = meta["source_rows"]
    assert [row["idx"] for row in rows] == list(range(meta["n_occ"]))
    assert set(witnesses) == set(range(meta["n_occ"]))
    assert set(ledger["entries"]) == {str(row["orbit"]) for row in rows}
    for row in rows:
        source = row["source"]
        entry = ledger["entries"][str(row["orbit"])]
        assert row["orbit"] not in EXPECTED
        assert row["lb"] <= source["bound"]
        assert entry == dict(orbit=row["orbit"], lb=source["bound"],
                             basis_codes=source["basis"], theorem=source["theorem"],
                             module=source["module"])
        assert source["module"] not in ("FrozenRegistry.UnusedAdapters", "FrozenRegistry.Checked")
        assert set(row["preimages"]) <= span(source["basis"])
        assert [word_code(row["word"], c) for c in row["preimages"]] == row["basis"]
        assert json.loads(json.dumps(transport(row))) == witnesses[row["idx"]]
    assert len(meta["dead_witnesses"]) == meta["n_dead"]
    for dead in meta["dead_witnesses"]:
        source = rows[dead["witness_source_idx"]]
        assert dead["basis"] == source["basis"] and source["lb"] == meta["target"]
    killed = set().union(*(span(d["basis"]) for d in meta["dead_witnesses"]))
    free = sorted(set(range(9)) - {c.bit_length() - 1 for c in meta["basis"]})
    sections = [sum(((q >> j) & 1) << bit for j, bit in enumerate(free))
                for q in range(1 << len(free))]
    assert meta["live_list"] == [q - 1 for q, c in enumerate(sections) if c not in killed]
    check_paths(meta, cert)
    for leaf in cert["branch"]["certs"]:
        check_ray(meta, leaf)
        broken = copy.deepcopy(leaf)
        broken["used_rows"][0]["multiplier"] += 1
        try:
            check_ray(meta, broken)
        except ValueError:
            pass
        else:
            raise AssertionError("Corrupted multiplier accepted")
    with tempfile.TemporaryDirectory() as temporary:
        out = Path(temporary)
        emit_data(meta, out)
        finish(meta, cert, ledger, out, transports=witnesses)
        prefix = f"QiushiGlobalOrbitUnused{node}"
        for field in ("Section", "Dead", "Source", "DeadSource", "Indicator"):
            for path in out.glob(prefix + field + "Block*.lean"):
                path.unlink()
        emit_checks(meta, out, width=data["generation"]["check_width"])
        generated = sorted(out.glob(prefix + "*.lean"))
        assert len(generated) == data["generation"]["generated_modules"]
        for path in generated:
            assert path.read_bytes() == (ROOT / path.name).read_bytes(), path.name
        assert (out / "source-modules.json").read_bytes() == (directory / "source-modules.json").read_bytes()
    result = dict(node=node, scope="exact certificate data and deterministic Lean emission; not a rank theorem receipt",
                  checks=dict(exact_target=True, source_ledger_without_registry_aggregate=True,
                              explicit_transports=True, dead_bounds_and_live_partition=True,
                              complete_branch_paths=True, farkas_leaves=True,
                              corrupt_multiplier_rejected=True, byte_identical_generated_lean=True),
                  generated_module_count=len(generated),
                  predecessors=sorted({row["orbit"] for row in rows}),
                  leaf_rhs=[leaf["rhs"] for leaf in cert["branch"]["certs"]],
                  certificate_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                      for p in sorted(directory.glob("*.json"))
                                      if not p.name.startswith("verification")})
    (directory / f"verification{node}.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"{node}: 8 data checks passed; {len(generated)} generated modules", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("nodes", nargs="+", type=int, choices=sorted(EXPECTED))
    args = parser.parse_args()
    for node in args.nodes:
        verify(node)
