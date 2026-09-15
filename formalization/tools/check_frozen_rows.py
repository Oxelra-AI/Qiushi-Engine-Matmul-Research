"""Compare the eight generated instances with the report's frozen quotient table.

This is a data correspondence check, not a Lean proof or a table soundness proof.
"""
import argparse
import hashlib
import json
from pathlib import Path
import pickle

from generate_certificate import rref


class PrimitiveUnpickler(pickle.Unpickler):
    def find_class(self, module, name):
        raise pickle.UnpicklingError("only primitive table data is accepted")


def check(project, proof):
    relative = "assets/quotients/data/wang_f2_lb20/wang_subspace_lut.pkl"
    manifest = json.loads((proof / "manifest.json").read_text())
    entries = [row for row in manifest["files"] if row["path"] == relative]
    if len(entries) != 1:
        raise ValueError("frozen table must occur exactly once in the proof manifest")
    path = proof / relative
    with path.open("rb") as stream:
        if stream.read(43).startswith(b"version https://git-lfs.github.com/spec/"):
            raise ValueError("fetch the LFS table object before this check")
        stream.seek(0)
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
        if digest != entries[0]["sha256"]:
            raise ValueError("table bytes do not match the proof manifest")
        stream.seek(0)
        data = PrimitiveUnpickler(stream).load()
        if stream.read(1):
            raise ValueError("trailing data after the frozen table")
    lut = data["lut"] if "lut" in data else data
    if not isinstance(lut, dict) or not lut:
        raise ValueError("expected a nonempty quotient table")
    checked, mismatches = {}, []
    for index in range(484, 492):
        tables = json.loads((project / "certificates" / str(index) / "tables.json").read_text())
        rows = tables["source_rows"] + tables["dead_witnesses"]
        if not rows:
            raise ValueError(f"instance {index} has no rows")
        for row in rows:
            basis = rref(row["basis"])
            key = (sum(code << (9 * j) for j, code in enumerate(basis)) << 4) | len(basis)
            frozen = lut.get(key)
            if type(frozen) is not int or frozen != row["lb"]:
                mismatches.append({"instance": index, "basis": list(basis),
                                   "lean_input": row["lb"], "frozen": frozen})
        checked[str(index)] = len(rows)
    return {"status": "fail" if mismatches else "pass", "rows_per_instance": checked,
            "total_rows": sum(checked.values()), "table_entries": len(lut),
            "table_sha256": digest, "mismatches": mismatches,
            "scope": "exact selected-row agreement; not formal table or CNF verification"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--proof", type=Path, required=True)
    args = parser.parse_args()
    result = check(args.project, args.proof)
    print(json.dumps(result, indent=2))
    return int(result["status"] != "pass")


if __name__ == "__main__":
    raise SystemExit(main())
