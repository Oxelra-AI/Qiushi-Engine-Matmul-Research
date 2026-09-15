#!/usr/bin/env python3
"""Export exact RowsAll basis order for arbitrary-query orbit transports.

This is a data exporter, not a numeric-label proof. It does not RREF-reduce,
reorder generators, read a lookup-table pickle, or generate positive controls.
"""

import argparse
import hashlib
import json
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def linear_code(images, code):
    result = 0
    for bit, image in enumerate(images):
        if (code >> bit) & 1:
            result ^= image
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--catalogue", type=Path, required=True)
    parser.add_argument("--summary", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    catalogue = json.loads(args.catalogue.read_text())
    charts = sorted(json.loads(args.summary.read_text())["results"], key=lambda r: r["cert_index"])
    rows = catalogue["rows"]
    assert len(rows) == catalogue["row_count"] == 29210
    assert all(a["mask"] < b["mask"] for a, b in zip(rows, rows[1:]))
    assert [chart["cert_index"] for chart in charts] == list(range(484, 492))
    count = 0
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w") as output:
        for chart in charts:
            orbit = chart["cert_index"]
            base = chart["W_basis_from_orbit"]
            free = chart["row_records"]["18"]["meta"]["free_bits"]
            assert len(base) == 2 and len(free) == 7
            images = [1 << bit for bit in free] + [base[1], base[0]]
            for index, row in enumerate(rows):
                assert all(0 < q < 128 for q in row["basis"])
                basis = [linear_code(images, c) for c in [256, 128, *row["basis"]]]
                expected = base + [sum(((q >> k) & 1) << bit for k, bit in enumerate(free))
                                   for q in row["basis"]]
                assert basis == expected
                output.write(json.dumps({"orbit": orbit, "row_index": index,
                                         "mask": row["mask"], "basis": basis},
                                        separators=(",", ":")) + "\n")
                count += 1
    assert count == 233680
    receipt = {"rows": count, "rows_per_orbit": 29210, "orbits": list(range(484, 492)),
               "catalogue_sha256": sha(args.catalogue), "summary_sha256": sha(args.summary),
               "export_sha256": sha(args.output), "exporter_sha256": sha(Path(__file__)),
               "row_order": "ascending mask, shared by all eight orbits",
               "basis_order": "[W[0], W[1]] ++ quotientBasis.map(lift_q)",
               "numeric_labels": "not consumed or asserted"}
    args.output.with_suffix(args.output.suffix + ".receipt.json").write_text(
        json.dumps(receipt, indent=2) + "\n")
    print(f"Exported {count} rows; sha256={receipt['export_sha256']}")


if __name__ == "__main__":
    main()
