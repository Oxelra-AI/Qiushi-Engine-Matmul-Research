#!/usr/bin/env python3
"""Select exact row-orbit tiers for the next rep2 promotion pilot."""
from __future__ import annotations
import json
from collections import Counter
from pathlib import Path

inp = Path('data/corrected_strategy/rep2_common_violation_orbits_full.json')
out = Path('data/corrected_strategy/rep2_orbit_promotion_tiers.json')
out.parent.mkdir(parents=True, exist_ok=True)
obj = json.loads(inp.read_text())
orbits = obj['top_orbits']

def key_fields(e):
    return {
        'canonical_key_hex': e['canonical_key_hex'],
        'dim': e['dim'],
        'lb': e['lb'],
        'cap_for_s20': e['cap_for_s20'],
        'prefix_occ': e['prefix_occ'],
        'residual_after_prefix': e['residual_after_prefix'],
        'hit_model_count': e['hit_model_count'],
        'hit_rounds': e['hit_rounds'],
        'row_count_seen_in_models': e['row_count_seen'],
        'orbit_size_under_prefix_stabilizer': e.get('orbit_size_under_prefix_stabilizer'),
        'per_model_row_counts': e['per_model_row_counts'],
        'per_model_max_excess': e['per_model_max_excess'],
        'representative_basis': e['representative_basis'],
    }

all5 = [e for e in orbits if e['hit_model_count'] == 5]
hit4plus = [e for e in orbits if e['hit_model_count'] >= 4]
# Priority tier: recurrent and strong-capacity rows; exact definition recorded here.
strong4plus = [e for e in hit4plus if e['lb'] >= 14 and e['residual_after_prefix'] <= 5]
# If too many, keep deterministic order already sorted by hit count and raw row count.
strong4plus_top40 = strong4plus[:40]
# A slightly broader but still manageable tier includes all hit>=4 rows with residual<=7 and lb>=12.
broad4plus = [e for e in hit4plus if e['lb'] >= 12 and e['residual_after_prefix'] <= 7]

hist = Counter((e['hit_model_count'], e['dim'], e['lb'], e['residual_after_prefix']) for e in orbits)
result = {
    'schema': 'rep2_orbit_promotion_tiers_v1',
    'source': str(inp),
    'warning': 'tiers are research targets for exact promotion tests, not mathematical conclusions',
    'prefix': obj['prefix'],
    'setwise_stabilizer_order': obj['setwise_stabilizer_order'],
    'available_orbits': len(orbits),
    'tier1_all5_count': len(all5),
    'tier2_hit4plus_count': len(hit4plus),
    'tier2_strong4plus_lb_ge14_res_le5_count': len(strong4plus),
    'tier2_broad4plus_lb_ge12_res_le7_count': len(broad4plus),
    'type_hist_top': [
        {'count': c, 'hit_model_count': k[0], 'dim': k[1], 'lb': k[2], 'residual_after_prefix': k[3]}
        for k, c in hist.most_common(40)
    ],
    'tier1_all5': [key_fields(e) for e in all5],
    'tier2_strong4plus_top40': [key_fields(e) for e in strong4plus_top40],
    'tier2_all_hit4plus': [key_fields(e) for e in hit4plus],
}
out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(json.dumps({
    'out': str(out),
    'tier1_all5': len(all5),
    'hit4plus': len(hit4plus),
    'strong4plus': len(strong4plus),
    'broad4plus': len(broad4plus),
}, sort_keys=True))
