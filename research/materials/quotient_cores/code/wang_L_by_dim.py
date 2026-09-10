#!/usr/bin/env python3
"""analysis: Characterize L>=12 Wang rows by dimension."""
import pickle, json, time
from pathlib import Path
from collections import Counter, defaultdict

WDIR = Path("research/research_record/workspace")
ODIR = WDIR / "data" / "pencil_wang_comparison"
ODIR.mkdir(parents=True, exist_ok=True)

t0 = time.time()
with open(WDIR / "data/wang_f2_lb20/wang_subspace_lut.pkl", "rb") as f:
    payload = pickle.load(f)
lut = payload["lut"]

dim_L = defaultdict(lambda: Counter())
total_by_dim = Counter()
for key, L in lut.items():
    dim = key & 0xF
    dim_L[dim][L] += 1
    total_by_dim[dim] += 1

print("Full-tensor dimension -> L distribution:")
print(f"{'Dim':>4s}  {'Total':>8s}  {'L>=12':>8s}  L distribution")
print("-" * 80)
for dim in sorted(dim_L.keys()):
    dist = dim_L[dim]
    total = total_by_dim[dim]
    ge12 = sum(v for k, v in dist.items() if k >= 12)
    top = sorted(dist.items(), key=lambda x: -x[0])[:6]
    top_str = ", ".join(f"L={k}:{v}" for k, v in top)
    print(f"{dim:4d}  {total:8d}  {ge12:8d}  {top_str}")

# Near-miss violations at core dims 5,6 = full dims 6,7
print("\nViolation-relevant dimensions:")
for fdim in [6, 7]:
    cdim = fdim - 1
    total = total_by_dim[fdim]
    print(f"  Full dim {fdim} (core dim {cdim}): {total} subspaces")
    for L in sorted(dim_L[fdim].keys()):
        cnt = dim_L[fdim][L]
        print(f"    L={L}: {cnt} ({100*cnt/total:.1f}%)")

# How many rows have L >= 12 across all dimensions?
total_ge12 = sum(v for dim in dim_L for k, v in dim_L[dim].items() if k >= 12)
total_all = sum(total_by_dim.values())
print(f"\nTotal L>=12 rows: {total_ge12:,} / {total_all:,} ({100*total_ge12/total_all:.1f}%)")

results = {k: {str(L): v for L, v in sorted(dim_L[k].items())} for k in sorted(dim_L.keys())}
out = ODIR / "wang_L_by_dimension.json"
with open(out, 'w') as f:
    json.dump(results, f, indent=2)
print(f"Saved: {out}")
print(f"Elapsed: {time.time()-t0:.1f}s")
