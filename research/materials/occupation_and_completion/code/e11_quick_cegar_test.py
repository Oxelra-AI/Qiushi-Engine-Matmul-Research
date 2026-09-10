#!/usr/bin/env python3
"""Quick E11 CEGAR test: can we find admissible supports at n=19?"""
import struct, time, json
from pathlib import Path
from collections import Counter
from ortools.sat.python import cp_model


def load_rows(path):
    raw = path.read_bytes()
    assert raw[:8] == b"E11WANG1"
    nrows = int.from_bytes(raw[8:16], "little")
    masks, caps = [], []
    off = 16
    for _ in range(nrows):
        m = int.from_bytes(raw[off:off+32], "little")
        c = int.from_bytes(raw[off+32:off+36], "little", signed=True)
        masks.append(m); caps.append(c)
        off += 36
    return masks, caps


def mask_pts(m):
    pts = []; x = m
    while x:
        b = (x & -x).bit_length() - 1
        pts.append(b); x ^= 1 << b
    return pts


def main():
    p = Path("data/wang_native/quotient_binaries/e11_all_n19.bin")
    masks, caps = load_rows(p)
    print(f"Total rows: {len(masks)}")
    print(f"Cap hist: {dict(sorted(Counter(caps).items()))}")

    # Multiplicity bounds
    mult_bound = {q: 19 for q in range(256)}
    mult_bound[0] = 0
    for m, c in zip(masks, caps):
        for pt in mask_pts(m):
            if pt >= 1 and c < mult_bound[pt]:
                mult_bound[pt] = c
    print(f"Mult bound hist: {dict(sorted(Counter(mult_bound[q] for q in range(1,256)).items()))}")

    # CEGAR: start with cap<=2, iterate
    init_idx = set(i for i, c in enumerate(caps) if 0 < c <= 2)
    active_idx = set(init_idx)
    print(f"Cap<=2 rows: {len(init_idx)}")

    for rnd in range(20):
        model = cp_model.CpModel()
        m = {q: model.new_int_var(0, min(mult_bound[q], 2), f"m{q}") for q in range(1, 256)}
        model.add(sum(m.values()) == 19)
        kept = 0
        for i in active_idx:
            pts = [p for p in mask_pts(masks[i]) if p >= 1]
            if pts and caps[i] < 19:
                model.add(sum(m[p] for p in pts) <= int(caps[i]))
                kept += 1
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = 60
        solver.parameters.num_workers = 8
        solver.parameters.random_seed = 42 + rnd
        solver.parameters.randomize_search = True
        t0 = time.time()
        st = solver.solve(model)
        elapsed = time.time() - t0
        print(f"\nRound {rnd}: status={solver.status_name(st)}, time={elapsed:.1f}s, rows={kept}")

        if st == cp_model.INFEASIBLE:
            print("INFEASIBLE with these constraints!")
            break
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            print("No solution found in time limit")
            break

        sup = []
        for q in range(1, 256):
            v = solver.value(m[q])
            sup.extend([q] * v)
        cnt = Counter(sup)
        repeats = {q: c for q, c in cnt.items() if c > 1}
        print(f"  Support: {len(sup)} terms, {len(set(sup))} distinct, repeats={repeats}")

        # Check all rows
        viols = []
        for i, (mask, cap) in enumerate(zip(masks, caps)):
            s = sum(cnt[pt] for pt in mask_pts(mask) if pt in cnt)
            if s > cap:
                viols.append(i)
        print(f"  Violations: {len(viols)}")
        if not viols:
            print(f"  FULLY ADMISSIBLE! Support: {sorted(set(sup))}")
            json.dump({"support": sup, "distinct": sorted(set(sup)),
                       "repeats": repeats, "round": rnd},
                      open("data/construction_pipeline/e11_quick_cegar.json", "w"),
                      indent=2)
            break
        for vi in viols:
            active_idx.add(vi)
        print(f"  Added {len(viols)} rows, total active: {len(active_idx)}")


if __name__ == "__main__":
    main()
