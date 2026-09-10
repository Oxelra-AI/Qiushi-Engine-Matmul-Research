#!/usr/bin/env python3
"""analysis: demonstrate the independent transaction-underflow failure mode.

This is not a model of Wang mathematics. It is a minimal reproduction of the
control-flow pattern in the peer e11_domain_dfs.cpp: select_point may return
false during propagation before all incident row counters for p have been
incremented; restore_counts(p) then decrements every incident counter of p.
For uint8_t counters, any untouched counter becomes 255.
"""
from __future__ import annotations
import json
from dataclasses import dataclass
from pathlib import Path

OUT = Path("data/domain_dfs_soundness")

@dataclass
class Row:
    pts: tuple[int, ...]
    cap: int


def simulate():
    # Row order matters exactly as in pt_small_rows[p]. p=1 is incident to row0 and row1.
    # Processing row0 saturates it and removes q=2. Removing q touches row2 and triggers
    # the invalid small_remain < cap-count test. select_point returns false before row1
    # has been incremented, but restore_counts(1) decrements both row0 and row1.
    rows = [
        Row((1, 2), 1),  # row0: selecting 1 saturates and removes 2
        Row((1, 3), 1),  # row1: contains selected point but is not reached before false return
        Row((2, 3), 2),  # row2: false small_remain test after 2 removed
    ]
    pt_rows = {1:[0,1], 2:[0,2], 3:[1,2]}
    small_count = [0,0,0]
    small_remain = [len(r.pts) for r in rows]
    domain = {1: True, 2: True, 3: True}
    undo = []
    events=[]

    def remove_point_propagate(q):
        if not domain[q]: return True
        domain[q]=False; undo.append(q)
        for ri in pt_rows[q]:
            small_remain[ri] -= 1
            bad = small_remain[ri] < rows[ri].cap - small_count[ri]
            events.append({
                'event':'remove_touch','removed_point':q,'row':ri,'pts':rows[ri].pts,
                'cap':rows[ri].cap,'count':small_count[ri],'remain':small_remain[ri],
                'rhs_cap_minus_count':rows[ri].cap-small_count[ri], 'returns_false_here':bad,
            })
            if bad: return False
        return True

    # mimic select_point(1)
    p=1
    domain[p]=False; undo.append(p)
    returned_false=False
    incremented=[]
    for ri in pt_rows[p]:
        small_count[ri] = (small_count[ri] + 1) & 255
        incremented.append(ri)
        events.append({'event':'increment_selected_row','selected':p,'row':ri,'count_after_increment':small_count[ri]})
        if small_count[ri] == rows[ri].cap:
            for q in rows[ri].pts:
                if domain[q]:
                    ok = remove_point_propagate(q)
                    if not ok:
                        returned_false=True
                        events.append({'event':'select_point_returns_false_before_remaining_incident_rows','selected':p,'incremented_rows':incremented.copy(),'all_incident_rows':pt_rows[p]})
                        break
        if returned_false:
            break
    before_restore = small_count.copy()
    # mimic restore_counts(p): decrements all incident rows, even row1 which was not incremented.
    for ri in pt_rows[p]:
        small_count[ri] = (small_count[ri] - 1) & 255
    after_restore = small_count.copy()
    return {
        'rows':[r.__dict__ for r in rows],
        'pt_rows':pt_rows,
        'returned_false':returned_false,
        'counts_before_restore_counts':before_restore,
        'counts_after_restore_counts_uint8':after_restore,
        'underflow_rows':[ri for ri,(a,b) in enumerate(zip(before_restore,after_restore)) if a==0 and b==255],
        'events':events,
        'interpretation':'row1 contains selected point 1 but was never incremented; restore_counts decrements it from 0 to 255, corrupting later cap tests.',
    }


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    result={'schema':'s0908_flawed_transaction_underflow_v1','simulation':simulate()}
    out=OUT/'flawed_transaction_underflow.json'
    out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
