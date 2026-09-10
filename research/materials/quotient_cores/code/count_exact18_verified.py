#!/usr/bin/env python3
"""Count all DRAT-verified exact-18 pair proofs."""
import json
from pathlib import Path

verified = 0; max7 = 0; max9 = 0; sat_max7 = []

# Earlier pairs 0-6
for d in [
    Path('data/rank1_fixed_high_filtered_cnf'),
    Path('data/rank1_pair_filtered_proof_batch/pilot_005_006'),
]:
    for pd in sorted(d.iterdir()) if d.exists() else []:
        if pd.is_dir() and pd.name.startswith('pair_') and 'exact18' in pd.name:
            for sf in pd.glob('*.status.json'):
                data = json.loads(sf.read_text())
                if data.get('drat_trim_log_parse', {}).get('verified'):
                    verified += 1
                    if 'max7' in str(pd): max7 += 1
                    elif 'max9' in str(pd): max9 += 1

# Batch 7-68
bdir = Path('data/rank1_pair_filtered_proof_batch/batch_007_068')
for pd in sorted(bdir.iterdir()):
    if pd.is_dir() and pd.name.startswith('pair_') and 'exact18' in pd.name:
        for sf in pd.glob('*.status.json'):
            data = json.loads(sf.read_text())
            if data.get('cadical_exit') == 10:
                sat_max7.append(pd.name)
            if data.get('drat_trim_log_parse', {}).get('verified'):
                verified += 1
                if 'max7' in str(pd): max7 += 1
                elif 'max9' in str(pd): max9 += 1

print(f'Total verified: {verified}  (max7={max7}, max9={max9})')
print(f'max7 SAT cases (needed max9): {len(sat_max7)}')
for x in sat_max7: print(f'  {x}')
print(f'Expected 69 -> {"✓ ALL VERIFIED" if verified >= 69 else f"MISSING {69-verified}"}')
