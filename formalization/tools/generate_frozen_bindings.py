"""Generate exact frozen-orbit numeric bounds for planes 484 through 491.

Witness search is untrusted. Lean checks both span containments, matrix facts,
selected frozen-table values, and the existing config's selected row values.
No quotient-rank theorem or historical-pickle equality is assumed or generated.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

from generate_certificate import actions, find_transports, literal, rref, span


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def gather(project, representatives):
    if [r["index"] for r in representatives] != list(range(496)):
        raise ValueError("expected exactly 496 indexed frozen representatives")
    spaces, by_basis, metadata, inputs = [], {}, {}, {}
    for plane in range(484, 492):
        path = project / "certificates" / str(plane) / "tables.json"
        meta = json.loads(path.read_text())
        inputs[str(path)] = digest(path)
        if meta["plane"] != plane or len(rref(meta["basis"])) != 2:
            raise ValueError("wrong plane identity or dimension")
        for kind, count, key in [("source_rows", "n_occ", "idx"),
                                 ("dead_witnesses", "n_dead", "d_idx")]:
            rows = meta[kind]
            if [row[key] for row in rows] != list(range(meta[count])):
                raise ValueError(f"nonexhaustive {plane} {kind} indices")
            for row in rows:
                basis, orbit = tuple(row["basis"]), row["orbit"]
                if basis != rref(basis) or not 3 <= len(basis) <= 8:
                    raise ValueError("expected canonical actual bases of dimension 3..8")
                rep = representatives[orbit]
                if rep["lb"] != row["lb"] or len(rep["basis"]) != len(basis):
                    raise ValueError("frozen representative label/dimension mismatch")
                if kind == "dead_witnesses" and row["lb"] < meta["target"]:
                    raise ValueError("dead label is below target")
                if basis not in by_basis:
                    by_basis[basis] = len(spaces)
                    spaces.append({"idx": len(spaces), "basis": list(basis),
                                   "orbit": orbit, "lb": row["lb"]})
                uid = by_basis[basis]
                if (spaces[uid]["orbit"], spaces[uid]["lb"]) != (orbit, row["lb"]):
                    raise ValueError("inconsistent duplicate actual space")
                row["space_id"] = uid
        metadata[plane] = meta
    return metadata, spaces, inputs


def validate_witnesses(spaces, reps, witnesses):
    ps, qs, qis, table, trans = actions()
    indices = {(int(p), int(q)): i for i, (p, q) in enumerate(zip(ps, qs))}
    if set(witnesses) != {row["idx"] for row in spaces}:
        raise ValueError("incomplete witness cache")
    for row in spaces:
        w = witnesses[row["idx"]]
        idx = indices[w["P"], w["Q"]]
        if w["Qinv"] != int(qis[idx]) or type(w["flip"]) is not bool:
            raise ValueError("invalid inverse or transpose choice")
        source = reps[row["orbit"]]["basis"]
        pairs = w["pairs"]
        if [a for a, _ in pairs] != row["basis"]:
            raise ValueError("target basis does not match witness")
        preimages = [b for _, b in pairs]
        forward = table[idx, trans] if w["flip"] else table[idx]
        if any(b not in span(source) or int(forward[b]) != a for a, b in pairs):
            raise ValueError("invalid forward membership or image")
        if any(c not in span(preimages) for c in source):
            raise ValueError("missing reverse span coverage")
        if rref(forward[source]) != tuple(row["basis"]):
            raise ValueError("transport is not exact")


def emit(metadata, spaces, reps, witnesses, out, data, width):
    modules = {}

    def write(name, imports, body):
        imports = list(dict.fromkeys(imports))
        lines = [*(f"import {s}" for s in imports), "",
                 "-- Generated numeric bindings; no tensor-rank or pickle theorem.",
                 "set_option maxHeartbeats 8000000", "set_option maxRecDepth 100000",
                 "namespace QiushiMatmul.FrozenWang", "", *body,
                 "", "end QiushiMatmul.FrozenWang", ""]
        path = out / f"{name}.lean"
        path.write_text("\n".join(lines))
        modules[name] = {"imports": imports, "sha256": digest(path)}

    modules["QiushiFrozenOrbitTable"] = {
        "imports": ["QiushiCodeSpanBridgeCore", "QiushiOrbitTransport", "QiushiTransposeTransport"],
        "sha256": digest(out / "QiushiFrozenOrbitTable.lean")}
    path = out / "QiushiFrozenWangData.lean"
    path.write_bytes(data.read_bytes())
    modules["QiushiFrozenWangData"] = {
        "imports": ["QiushiFrozenOrbitTable"], "sha256": digest(path)}

    common = []
    for orbit in sorted({r["orbit"] for r in spaces}):
        rep = reps[orbit]
        common += [f"theorem basis{orbit} : frozenWangTable.basis {orbit} = {literal(rep['basis'])} := by decide",
                   f"theorem lower{orbit} : frozenWangTable.lower {orbit} = {rep['lb']} := by decide", ""]
    matrices = sorted({w[k] for w in witnesses.values() for k in ("P", "Q")})
    for code in matrices:
        common += [f"theorem det{code} : (codeMat {code}).det ≠ 0 := by decide +kernel"]
    inverses = {w["Q"]: w["Qinv"] for w in witnesses.values()}
    for code, inverse in sorted(inverses.items()):
        common += [f"theorem inv{code} : (codeMat {code}).transpose *",
                   f"    (codeMat {inverse}).transpose = (1 : Mat3) := by decide +kernel"]
    write("QiushiFrozenWangChecks", ["QiushiFrozenWangData"], common)

    space_modules = {}
    for start in range(0, len(spaces), width):
        name = f"QiushiFrozenWangSpaces{start // width:03d}"
        body = []
        for row in spaces[start:start + width]:
            uid, orbit, basis = row["idx"], row["orbit"], literal(row["basis"])
            w = witnesses[uid]
            pairs = "[" + ", ".join(f"({a}, {b})" for a, b in w["pairs"]) + "]"
            body += [f"theorem space{uid:04d}_orbit :",
                     f"    frozenWangTable.OrbitImage {orbit} (spanCodes {basis}) := by",
                     f"  exact frozenOrbitImage_of_code_transport frozenWangTable {orbit} {pairs}",
                     f"    (codeMat {w['P']}) (codeMat {w['Q']}) (codeMat {w['Qinv']}) {str(w['flip']).lower()}",
                     f"    det{w['P']} det{w['Q']} inv{w['Q']}",
                     f"    (by rw [basis{orbit}]; decide +kernel)",
                     f"    (by rw [basis{orbit}]; decide +kernel)", "",
                     f"theorem space{uid:04d}_lower : {row['lb']} ≤ frozenWangTable.L0 (spanCodes {basis}) := by",
                     f"  have h := frozenWangTable.lower_le_L0 {orbit} space{uid:04d}_orbit",
                     f"  simpa only [lower{orbit}] using h", ""]
            space_modules[uid] = name
        write(name, ["QiushiFrozenWangChecks"], body)

    plane_modules = []
    for plane, meta in metadata.items():
        cfg, prefix = f"plane{plane}GenConfig", f"plane{plane}Gen"
        groups = {}
        for kind, key, size in [("source", "source_rows", meta["n_occ"]),
                                ("dead", "dead_witnesses", meta["n_dead"])]:
            binding_modules = []

            def prop(index):
                if kind == "source":
                    return f"{cfg}.sourceLb {index} ≤ frozenWangTable.L0 ({cfg}.sourceU {index})"
                return f"{cfg}.target ≤ frozenWangTable.L0 ({cfg}.deadU {index})"

            for start in range(0, size, width):
                block = start // width
                name = f"QiushiFrozenWangPlane{plane}{kind.title()}{block:03d}"
                binding_modules.append(name)
                rows = meta[key][start:start + width]
                imports = [f"QiushiPlane{plane}GenData"]
                imports += sorted({space_modules[r["space_id"]] for r in rows})
                body = []
                for index, row in enumerate(rows, start):
                    numeral = f"({index} : Fin {size})"
                    basis, lb = literal(row["basis"]), row["lb"]
                    body += [f"theorem plane{plane}_{kind}{index:04d} : {prop(numeral)} := by"]
                    if kind == "source":
                        body += [f"  change {prefix}SourceLb {numeral} ≤",
                                 f"    frozenWangTable.L0 (spanCodes ({prefix}SourceBasis {numeral}))",
                                 f"  rw [show {prefix}SourceLb {numeral} = {lb} by decide,",
                                 f"      show {prefix}SourceBasis {numeral} = {basis} by decide]",
                                 f"  exact space{row['space_id']:04d}_lower", ""]
                    else:
                        body += [f"  change {meta['target']} ≤ frozenWangTable.L0 (spanCodes ({prefix}DeadBasis {numeral}))",
                                 f"  rw [show {prefix}DeadBasis {numeral} = {basis} by decide]",
                                 f"  exact Nat.le_trans (by decide : {meta['target']} ≤ {lb}) space{row['space_id']:04d}_lower", ""]
                body += [f"theorem plane{plane}_{kind}Block{block:03d} (offset : Fin {width})",
                         f"    (hlt : {block} * {width} + offset.val < {size}) :",
                         f"    {prop(f'(Fin.mk ({block} * {width} + offset.val) hlt)')} := by",
                         "  revert hlt", "  match offset with"]
                for offset in range(len(rows)):
                    body += [f"  | ⟨{offset}, _⟩ => intro hlt; exact plane{plane}_{kind}{start + offset:04d}"]
                body += [f"  | ⟨k + {len(rows)}, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega"]
                write(name, imports, body)
            groups[kind] = binding_modules

        body = []
        for kind, size in [("source", meta["n_occ"]), ("dead", meta["n_dead"])]:
            field = "nOcc" if kind == "source" else "nDead"
            p = (f"{cfg}.sourceLb i ≤ frozenWangTable.L0 ({cfg}.sourceU i)" if kind == "source"
                 else f"{cfg}.target ≤ frozenWangTable.L0 ({cfg}.deadU i)")
            blocks = len(groups[kind])
            body += [f"theorem plane{plane}_{kind} : ∀ i : Fin {cfg}.{field},", f"    {p} := by",
                     f"  apply forall_fin_of_blocks (blocks := {blocks}) (width := {width})",
                     "    (by decide) (by decide)", "  intro block", "  match block with"]
            body += [f"  | ⟨{block}, _⟩ => exact plane{plane}_{kind}Block{block:03d}" for block in range(blocks)]
            body += [f"  | ⟨k + {blocks}, h⟩ => omega", ""]
        name = f"QiushiFrozenWangPlane{plane}"
        write(name, ["QiushiFiniteBlocks", *groups["source"], *groups["dead"]], body)
        plane_modules.append(name)
    write("QiushiFrozenWangBindings", plane_modules, [])
    audit = []
    for plane in metadata:
        for kind in ("source", "dead"):
            audit += [f"#print axioms plane{plane}_{kind}", f"#check plane{plane}_{kind}"]
    write("QiushiFrozenWangAudit", ["QiushiFrozenWangBindings"], audit)
    return modules


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--frozen-dir", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--width", type=int, default=32)
    args = parser.parse_args()
    if args.out.resolve() == args.project.resolve() or args.width < 1:
        parser.error("use an isolated output directory and positive block width")
    reps_path = args.frozen_dir / "representatives.json"
    data_path = args.frozen_dir / "QiushiFrozenWangData.lean"
    representatives = json.loads(reps_path.read_text())
    reps = representatives["rows"]
    metadata, spaces, inputs = gather(args.project, reps)
    inputs.update({str(reps_path): digest(reps_path), str(data_path): digest(data_path),
                   str(Path(__file__).with_name("generate_certificate.py")):
                       digest(Path(__file__).with_name("generate_certificate.py"))})
    rows_per_plane = {p: m["n_occ"] + m["n_dead"] for p, m in metadata.items()}
    if sum(rows_per_plane.values()) != 5917:
        raise ValueError("expected all 5917 selected source/dead rows")
    args.work_dir.mkdir(parents=True, exist_ok=True)
    cache = args.work_dir / "witnesses.json"
    cached = json.loads(cache.read_text()) if cache.exists() else None
    if cached and cached["inputs"] == inputs:
        witnesses = {int(k): v for k, v in cached["witnesses"].items()}
    else:
        entries = {r["index"]: {"basis_codes": r["basis"]} for r in reps}
        witnesses = find_transports(spaces, entries)
    validate_witnesses(spaces, reps, witnesses)
    cache.write_text(json.dumps({"inputs": inputs, "spaces": spaces, "witnesses": witnesses}, indent=2) + "\n")
    args.out.mkdir(parents=True, exist_ok=True)
    modules = emit(metadata, spaces, reps, witnesses, args.out, data_path, args.width)
    manifest = {"inputs": inputs, "generator_sha256": digest(Path(__file__)),
                "certificate_sha256": representatives["certificate_sha256"],
                "rows_per_plane": rows_per_plane, "total_rows": 5917,
                "source_rows": sum(m["n_occ"] for m in metadata.values()),
                "dead_rows": sum(m["n_dead"] for m in metadata.values()),
                "unique_spaces": len(spaces), "dimensions": dict(Counter(len(r["basis"]) for r in spaces)),
                "width": args.width, "modules": modules,
                "scope": "Selected-row frozen orbit-expansion bounds, not whole-pickle equality or tensor rank."}
    (args.work_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({k: manifest[k] for k in ("rows_per_plane", "total_rows", "unique_spaces")}))


if __name__ == "__main__":
    main()
