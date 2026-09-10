#!/usr/bin/env python3
"""Write the research_record toy counterexample as E11WANG1 constraints.

Rows: {1,2} cap 1 and {2,3} cap 2.  Target 2 has feasible support {1,3}.
The analysis unsound remain<cap-count rule falsely killed this branch after
selecting 1 and propagating removal of 2.
"""
import json, struct
from pathlib import Path
OUT = Path("data/wang_native/toy")
OUT.mkdir(parents=True, exist_ok=True)
rows = [
    (1, 1, [1, 2]),
    (2, 2, [2, 3]),
]
bin_path = OUT / "toy_upper_bound.e11wang1.bin"
with open(bin_path, "wb") as f:
    f.write(b"E11WANG1")
    f.write(struct.pack("<I", len(rows)))
    for cap, dim, pts in rows:
        words = [0, 0, 0, 0]
        for p in pts:
            words[p >> 6] |= 1 << (p & 63)
        f.write(struct.pack("<BBHQQQQ", cap, dim, 0, *words))
meta = {"binary_path": str(bin_path), "rows": [{"cap": c, "dim": d, "pts": p} for c,d,p in rows], "known_feasible_support": [1,3], "target": 2}
(OUT / "toy_upper_bound.meta.json").write_text(json.dumps(meta, indent=2) + "\n")
print(json.dumps(meta, indent=2))
