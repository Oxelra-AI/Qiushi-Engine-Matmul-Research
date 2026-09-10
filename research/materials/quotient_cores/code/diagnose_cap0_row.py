#!/usr/bin/env python3
"""Diagnose the cap=0 row in the E11 binary and test its effect on known supports.

Key question: the full quotient space (dim8=8) has LB=19, cap19=0. If this row
is in the binary with mask covering all 255 points, the DFS should immediately
reject any support at target 19 (since count=19 > 0=cap after all points selected).
But the safe DFS explored 104K nodes at max depth 16. Why?
"""
import struct, json, os

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
SESSION = os.path.dirname(os.path.dirname(SCRIPT_DIR))
BIN_PATH = os.path.join(SESSION, "workspace/data/wang_native/e11_wang_cap5.bin")
OUT_DIR = os.path.join(SESSION, "workspace/data/wang_native/diagnostics")
os.makedirs(OUT_DIR, exist_ok=True)

def read_e11_binary(path):
    """Read E11WANG1 binary and return all rows."""
    rows = []
    with open(path, "rb") as f:
        magic = f.read(8)
        assert magic == b"E11WANG1", f"Bad magic: {magic}"
        nrows = struct.unpack("<I", f.read(4))[0]
        for i in range(nrows):
            cap, dim8, reserved = struct.unpack("<BBH", f.read(4))
            words = struct.unpack("<4Q", f.read(32))
            # Count points in mask
            npts = sum(bin(w).count('1') for w in words)
            rows.append({
                'idx': i, 'cap': cap, 'dim8': dim8,
                'npts': npts, 'words': words
            })
    return rows

def check_support_against_rows(rows, support_points):
    """Check a support (set of quotient points) against all rows."""
    # Convert support to bitset
    s_words = [0, 0, 0, 0]
    for p in support_points:
        s_words[p >> 6] |= 1 << (p & 63)
    
    violations = []
    for r in rows:
        occ = sum(bin(r['words'][w] & s_words[w]).count('1') for w in range(4))
        if occ > r['cap']:
            violations.append({
                'row_idx': r['idx'], 'cap': r['cap'], 'dim8': r['dim8'],
                'npts': r['npts'], 'occupancy': occ, 'excess': occ - r['cap']
            })
    return violations

def main():
    print(f"Reading {BIN_PATH}")
    rows = read_e11_binary(BIN_PATH)
    print(f"Total rows: {len(rows)}")
    
    # Find all cap=0 rows
    cap0_rows = [r for r in rows if r['cap'] == 0]
    print(f"\n=== CAP=0 ROWS ({len(cap0_rows)}) ===")
    for r in cap0_rows:
        print(f"  idx={r['idx']}, dim8={r['dim8']}, npts={r['npts']}, "
              f"mask_words=[{','.join(hex(w) for w in r['words'])}]")
    
    # Also show cap=1 rows
    cap1_rows = [r for r in rows if r['cap'] == 1]
    print(f"\n=== CAP=1 ROWS ({len(cap1_rows)}) ===")
    for r in cap1_rows[:10]:
        print(f"  idx={r['idx']}, dim8={r['dim8']}, npts={r['npts']}")
    if len(cap1_rows) > 10:
        print(f"  ... ({len(cap1_rows)} total)")
    
    # Check: which rows have npts >= 200?
    big_mask = [r for r in rows if r['npts'] >= 200]
    print(f"\n=== ROWS WITH npts >= 200 ({len(big_mask)}) ===")
    for r in big_mask:
        print(f"  idx={r['idx']}, cap={r['cap']}, dim8={r['dim8']}, npts={r['npts']}")
    
    # Verify: if cap=0 row has mask with ALL 255 points, ANY selection violates it
    if cap0_rows:
        r = cap0_rows[0]
        all_pts = set()
        for w_idx in range(4):
            word = r['words'][w_idx]
            while word:
                b = word & (-word)  # lowest set bit
                p = w_idx * 64 + b.bit_length() - 1
                all_pts.add(p)
                word ^= b
        print(f"\n=== CAP=0 ROW ANALYSIS ===")
        print(f"  Points in mask: {len(all_pts)}")
        print(f"  Min point: {min(all_pts)}, Max point: {max(all_pts)}")
        print(f"  Contains all 1..255: {all_pts == set(range(1, 256))}")
    
    # Check a known rank-21 support against all cap<=5 rows
    # Use pool row 146 (all distinct, 21 quotient directions)
    ctrl_path = os.path.join(SESSION, 
        "workspace/data/wang_native/controls/e11_poolrow146_distinct21_support.json")
    if os.path.exists(ctrl_path):
        with open(ctrl_path) as f:
            ctrl = json.load(f)
        support = ctrl.get("support") or ctrl.get("quotient_support")
        if support:
            print(f"\n=== RANK-21 SUPPORT CHECK (pool row 146, {len(support)} points) ===")
            violations = check_support_against_rows(rows, support)
            print(f"  Violations at cap19: {len(violations)}")
            for v in violations[:5]:
                print(f"    row_idx={v['row_idx']}, cap={v['cap']}, dim8={v['dim8']}, "
                      f"npts={v['npts']}, occ={v['occupancy']}, excess={v['excess']}")
    
    # Summary
    result = {
        "total_rows": len(rows),
        "cap0_count": len(cap0_rows),
        "cap0_rows": [{k: v for k, v in r.items() if k != 'words'} for r in cap0_rows],
        "cap1_count": len(cap1_rows),
        "big_mask_count": len(big_mask),
    }
    if cap0_rows:
        r = cap0_rows[0]
        result["cap0_mask_covers_all_255"] = len(all_pts) == 255
    
    out_path = os.path.join(OUT_DIR, "cap0_diagnostic.json")
    with open(out_path, "w") as f:
        json.dump(result, f, indent=2)
    print(f"\nSaved {out_path}")

if __name__ == "__main__":
    main()
