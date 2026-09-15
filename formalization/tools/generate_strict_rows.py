"""Generate kernel-checked strict-containment witnesses for occupation rows."""
import argparse
import json
from pathlib import Path

from generate_certificate import span


def witnesses(lower, upper):
    small, large = set(span(lower)), set(span(upper))
    if not small < large or len(large) == 512:
        raise ValueError("row must strictly contain the plane and be proper")
    x = next(c for c in upper if c not in small)
    d = next(c for c in range(1, 512)
             if all((c & b).bit_count() % 2 == 0 for b in lower)
             and (c & x).bit_count() % 2 == 1)
    e = next(c for c in range(1, 512)
             if all((c & b).bit_count() % 2 == 0 for b in upper))
    y = e & -e
    return x, d, e, y


def emit_instance(meta, out, width=32):
    index, lower = meta["plane"], meta["basis"]
    config = f"plane{index}GenConfig"
    stem = f"QiushiPlane{index}Strict"
    lines = [f"import QiushiPlane{index}GenData", "import QiushiStrictSpanWitness",
             "import QiushiFiniteBlocks", "", "namespace QiushiMatmul", ""]
    groups = [("Source", "sourceBasis", meta["source_rows"]),
              ("Dead", "deadBasis", meta["dead_witnesses"])]
    for kind, field, rows in groups:
        name = f"plane{index}{kind}Strict"
        key = "idx" if kind == "Source" else "d_idx"
        if [row[key] for row in rows] != list(range(len(rows))):
            raise ValueError("row order must match the indexed Lean basis function")
        values = [witnesses(lower, r["basis"]) for r in rows]
        if not values:
            raise ValueError("expected nonempty source and dead rows")
        lines += [f"def {name}Witness (i : Fin {len(rows)}) : Nat × Nat × Nat × Nat :=",
                  f"  match i.val / {width} with"]
        for start in range(0, len(values), width):
            lines += [f"  | {start // width} =>", f"    match i.val % {width} with"]
            lines += [f"    | {j} => {v}" for j, v in enumerate(values[start:start + width])]
            lines += [f"    | _ => {values[start]}"]
        lines += [f"  | _ => {values[0]}", "",
                  f"def {name}Check (i : Fin {len(rows)}) : Bool :=",
                  f"  let w := {name}Witness i",
                  f"  strictSpanCheck {config}.planeBasis ({config}.{field} i)",
                  "    w.1 w.2.1 w.2.2.1 w.2.2.2", ""]
    lines += ["end QiushiMatmul", ""]
    (out / f"{stem}Data.lean").write_text("\n".join(lines))
    block_modules, final = [], []
    for kind, field, rows in groups:
        name = f"plane{index}{kind}Strict"
        blocks = (len(rows) + width - 1) // width
        for block in range(blocks):
            module = f"{stem}{kind}{block}"
            block_modules.append(module)
            content = [f"import {stem}Data", "set_option maxHeartbeats 80000000",
                       "set_option maxRecDepth 100000", "namespace QiushiMatmul",
                       f"theorem {name}Block{block} : ∀ offset : Fin {width},",
                       f"    ∀ hlt : {block} * {width} + offset.val < {len(rows)},",
                       f"    {name}Check ⟨{block} * {width} + offset.val, hlt⟩ = true := by",
                       "  decide +kernel", "end QiushiMatmul", ""]
            (out / f"{module}.lean").write_text("\n".join(content))
        final += [f"theorem {name}Checks : ∀ i, {name}Check i = true := by",
                  f"  apply forall_fin_of_blocks (blocks := {blocks}) (width := {width})",
                  "    (by decide) (by decide)", "  intro block", "  match block with"]
        final += [f"  | ⟨{b}, _⟩ => exact {name}Block{b}" for b in range(blocks)]
        final += [f"  | ⟨k + {blocks}, h⟩ => omega"]
        bound = "sourceU" if kind == "Source" else "deadU"
        hle = (f"planeLeSource_of_bool (plane{index}GenBool.hPlaneLeSource i)"
               if kind == "Source" else
               f"planeLeDead_of_bool (plane{index}GenBool.hPlaneLeDead i)")
        final += ["", f"theorem {name} : ∀ i, {config}.W < {config}.{bound} i ∧",
                  f"    {config}.{bound} i < ⊤ := by", "  intro i",
                  f"  exact strictSpanCheck_sound _ _ _ _ _ _ ({hle}) ({name}Checks i)", ""]
    content = [f"import {module}" for module in block_modules]
    content += [f"import QiushiPlane{index}GenBool", "namespace QiushiMatmul"]
    content += final + ["end QiushiMatmul", ""]
    (out / f"{stem}Final.lean").write_text("\n".join(content))
    return len(meta["source_rows"]) + len(meta["dead_witnesses"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--plane", type=int, action="append")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    counts = {}
    for index in args.plane or range(484, 492):
        meta = json.loads((args.project / "certificates" / str(index) / "tables.json").read_text())
        if meta["plane"] != index:
            raise ValueError("instance identity mismatch")
        counts[index] = emit_instance(meta, args.out)
    print(json.dumps({"rows": counts, "total": sum(counts.values())}))


if __name__ == "__main__":
    main()
