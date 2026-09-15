"""Extract the report's 496 frozen orbit representatives using protobuf parsing."""
import argparse
import hashlib
import json
from pathlib import Path
import struct

from google.protobuf import descriptor_pb2, descriptor_pool, message_factory, text_format

from generate_certificate import rref


def read_representatives(path):
    schema = descriptor_pb2.FileDescriptorProto(name="frozen_table.proto", syntax="proto3")
    row = schema.message_type.add(name="Row")
    for name, number, kind in [("index", 1, 13), ("constraints", 2, 12),
                               ("rank_lower_bound", 3, 13)]:
        row.field.add(name=name, number=number, type=kind, label=1)
    root = schema.message_type.add(name="Certificate")
    for number, name in enumerate(["problem_name", "characteristic", "extension_degree",
                                   "na", "nb", "nc"], 1):
        root.field.add(name=name, number=number, type=9 if number == 1 else 13, label=1)
    root.field.add(name="constrained_tensors", number=7, type=11, label=3, type_name=".Row")
    pool = descriptor_pool.DescriptorPool()
    pool.Add(schema)
    certificate = message_factory.GetMessageClass(pool.FindMessageTypeByName("Certificate"))()
    raw = path.read_bytes()
    # Proof payloads are not interpreted here; their bounds are not accepted as theorems.
    text_format.Parse(raw.decode(), certificate, allow_unknown_field=True)
    if (certificate.problem_name, certificate.characteristic, certificate.extension_degree,
            certificate.na, certificate.nb, certificate.nc) != ("matrix_q02_n333", 2, 1, 9, 9, 9):
        raise ValueError("wrong tensor or coefficient field")
    rows = []
    for item in certificate.constrained_tensors:
        if len(item.constraints) % 2:
            raise ValueError("matrix codes must be little-endian uint16 values")
        codes = list(struct.unpack("<" + "H" * (len(item.constraints) // 2), item.constraints))
        if any(code >= 512 for code in codes) or item.rank_lower_bound > 27:
            raise ValueError("invalid matrix code or lower-bound value")
        basis = list(rref(codes))
        if len(basis) != len(codes):
            raise ValueError("dependent representative basis")
        rows.append({"index": item.index, "basis": basis, "lb": item.rank_lower_bound})
    rows.sort(key=lambda item: item["index"])
    if [item["index"] for item in rows] != list(range(496)):
        raise ValueError("expected exactly one representative for each index 0..495")
    return rows, hashlib.sha256(raw).hexdigest()


def emit(rows):
    lines = ["import QiushiFrozenOrbitTable", "", "namespace QiushiMatmul", ""]
    for name, typ, values in [
            ("frozenWangBasis", "List Nat", [str(row["basis"]) for row in rows]),
            ("frozenWangLower", "Nat", [str(row["lb"]) for row in rows])]:
        lines += [f"def {name} (i : Fin 496) : {typ} :=", "  match i.val / 32 with"]
        for start in range(0, len(values), 32):
            lines += [f"  | {start // 32} =>", "    match i.val % 32 with"]
            lines += [f"    | {j} => {value}" for j, value in enumerate(values[start:start + 32])]
            lines.append(f"    | _ => {values[start]}")
        lines += [f"  | _ => {values[0]}", ""]
    lines += ["def frozenWangTable : FrozenOrbitTable where", "  basis := frozenWangBasis",
              "  lower := frozenWangLower", "", "end QiushiMatmul", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    rows, digest = read_representatives(args.certificate)
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "representatives.json").write_text(json.dumps({
        "certificate_sha256": digest, "rows": rows}, indent=2) + "\n")
    (args.out / "QiushiFrozenWangData.lean").write_text(emit(rows))
    print(json.dumps({"representatives": len(rows), "certificate_sha256": digest}))


if __name__ == "__main__":
    main()
