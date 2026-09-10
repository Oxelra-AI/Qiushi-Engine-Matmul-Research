#!/usr/bin/env python3
"""Check existence of 4-arc in F2^8 (= [n,11,>=5] code for the dual).

A 4-arc is a set of nonzero points where no 3 and no 4 sum to zero.
"""
import time, json
from pathlib import Path

OUT = Path("data/wang_validation")
OUT.mkdir(parents=True, exist_ok=True)

def check_4arc(target_size, time_limit=120.0):
    t0 = time.time()
    selected = []
    pair_xors = set()
    found = [None]
    calls = [0]
    
    def add_point(v):
        new_pairs = set()
        for s in selected:
            new_pairs.add(v ^ s)
        pair_xors.update(new_pairs)
        selected.append(v)
        return new_pairs
    
    def remove_point(v, added_pairs):
        selected.pop()
        pair_xors.difference_update(added_pairs)
    
    def is_feasible(v):
        # Cap check: v must not equal a^b for any pair in selected
        if v in pair_xors:
            return False
        # Sidon check: for each s in selected, v^s must not equal any pair_xor
        # Because v^s = a^b means v+s+a+b = 0 (4-sum violation)
        for s in selected:
            xs = v ^ s
            if xs == 0:
                continue
            if xs in pair_xors:
                return False
        return True
    
    def dfs(min_val, depth):
        calls[0] += 1
        if calls[0] % 2000000 == 0:
            if time.time() - t0 > time_limit:
                return -1
        if depth == target_size:
            found[0] = list(selected)
            return 1
        remaining = 255 - min_val + 1
        if remaining < target_size - depth:
            return 0
        for v in range(min_val, 256):
            if not is_feasible(v):
                continue
            added = add_point(v)
            result = dfs(v + 1, depth + 1)
            remove_point(v, added)
            if result != 0:
                return result
        return 0
    
    result = dfs(1, 0)
    elapsed = time.time() - t0
    return {
        "target_size": target_size,
        "found": result == 1,
        "timeout": result == -1,
        "exhausted": result == 0,
        "example": sorted(found[0]) if found[0] else None,
        "calls": calls[0],
        "elapsed_sec": elapsed,
    }

def verify_4arc(S):
    """Independently verify no 3-sum and no 4-sum zero."""
    S = set(S)
    for a in S:
        for b in S:
            if b <= a: continue
            c = a ^ b
            if c in S and c != a and c != b:
                return False, f"3-sum: {a}+{b}+{c}=0"
            for d in S:
                if d <= b: continue
                if d == c: continue
                e = a ^ b ^ d  # = c ^ d
                if e in S and e != a and e != b and e != d:
                    return False, f"4-sum: {a}+{b}+{d}+{e}=0"
    return True, "verified"

def main():
    print("=== 4-ARC EXISTENCE CHECK IN F2^8 (CORRECTED) ===")
    print("Looking for sets of k nonzero points with no 3-sum and no 4-sum zero.\n")
    
    results = {}
    max_found = 0
    
    for k in range(10, 24):
        tl = 30.0 if k <= 18 else 60.0
        r = check_4arc(k, time_limit=tl)
        status = "FOUND" if r["found"] else ("TIMEOUT" if r["timeout"] else "EXHAUSTED")
        print(f"  k={k:2d}: {status}, calls={r['calls']:>12,}, time={r['elapsed_sec']:.2f}s")
        if r["found"] and r["example"]:
            ok, msg = verify_4arc(r["example"])
            print(f"         Example: {r['example']}")
            print(f"         Verify: {msg}")
            if ok:
                max_found = k
        results[k] = r
        if r["exhausted"]:
            print(f"\n  => Maximum 4-arc size in F2^8 is {max_found}")
            break
        if r["timeout"]:
            print(f"         (timed out, cannot determine if {k}-arc exists)")
    
    # Conclusion for the research
    if max_found >= 19:
        print(f"\n  CONCLUSION: A 19-point 4-arc EXISTS in F2^8.")
        print(f"  This means [19,11,>=5] code EXISTS.")
        print(f"  Sidon structure does NOT force collinear triples in all 19-point supports.")
    elif max_found < 19 and any(results.get(k, {}).get("exhausted") for k in range(19, 24)):
        print(f"\n  CONCLUSION: Maximum 4-arc is {max_found} < 19.")
        print(f"  Every 19-point support MUST contain a collinear triple or zero-sum quadruple.")
    else:
        print(f"\n  INCONCLUSIVE: max found = {max_found}, some larger sizes timed out.")
    
    out = {
        "status": "ok",
        "max_4arc_found": max_found,
        "results": {str(k): v for k, v in results.items()},
    }
    outpath = OUT / "e11_sidon_4arc_check.json"
    with open(outpath, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
    print(f"\nSaved {outpath}")

if __name__ == "__main__":
    main()
