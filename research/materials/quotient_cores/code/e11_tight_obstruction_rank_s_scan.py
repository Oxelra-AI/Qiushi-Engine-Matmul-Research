#!/usr/bin/env python3
"""Scan tight row/column-space obstruction at several residual budgets for S0.

Input is the analysis S-free per-V file.  For selected or all orbits, rescan the
bare quotient-slice space S0 at every residual size s from the minimum cover
size up to 19 - flattening lower bound, or until the first cover not blocked by
the tight row/column-space necessary test appears.
"""
from __future__ import annotations
import argparse, json, sys, time
from collections import Counter
from pathlib import Path

SCRIPTS = Path('scripts')
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import e11_sfree_v_obstruction_scan as sf  # noqa: E402


def scan_orbit(prefix, flat_lb, max_cover_scan=0):
    Q, ann, phis, Rcoords = sf.sc.quotient_base_residual(prefix)
    S0 = sf.s0_basis_from_Q(Q)
    Rphi = sf.build_Rphi_masks(Rcoords)
    m, mininfo = sf.mininfo_for_S0(S0, Rphi)
    mt = tuple(m[p] for p in range(1,16))
    s_min = sf.exact_cover_minimum(mt)
    s_max = 19 - int(flat_lb)
    by_s = []
    first_survivor = None
    all_s_blocked = True
    for s in range(s_min, s_max+1):
        count=0; blocked=0; surv=None
        for cov in sf.iter_exact_covers(mt, s, cap=max_cover_scan):
            count += 1
            br = sf.cover_block_record(cov, m, mininfo)
            if br['blocked']:
                blocked += 1
            elif surv is None:
                surv = {'cover': list(cov), **br}
                # We only need existence to show S-free obstruction fails at this budget.
                break
        truncated = bool(max_cover_scan and count >= max_cover_scan and surv is None)
        status = 'HAS_SURVIVING_COVER' if surv else ('ALL_SCANNED_COVERS_BLOCKED' if truncated else 'ALL_COVERS_BLOCKED')
        by_s.append({'s': int(s), 'covers_scanned': int(count), 'blocked': int(blocked), 'truncated': truncated, 'status': status, 'first_survivor': surv})
        if surv is not None:
            first_survivor = {'s': int(s), **surv}
            all_s_blocked = False
            break
        if truncated:
            all_s_blocked = None
            break
    return {'s_min': int(s_min), 's_max_from_flattening': int(s_max), 'all_budgets_blocked_until_smax': all_s_blocked, 'first_survivor': first_survivor, 'by_s': by_s}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--input', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--orbit-ids', default='', help='comma separated orbit ids; empty means all')
    ap.add_argument('--max-orbits', type=int, default=0)
    ap.add_argument('--max-cover-scan', type=int, default=0)
    args=ap.parse_args(); t0=time.time()
    data=json.loads(args.input.read_text())
    wanted=None
    if args.orbit_ids.strip(): wanted={int(x) for x in args.orbit_ids.split(',') if x.strip()}
    records=[]; status_counter=Counter(); first_survivor_s=Counter()
    for rec in data['records']:
        if wanted is not None and int(rec['orbit_id']) not in wanted: continue
        if args.max_orbits and len(records)>=args.max_orbits: break
        scan=scan_orbit([int(x) for x in rec['prefix']], rec['flat_lb'], max_cover_scan=args.max_cover_scan)
        out={k:rec[k] for k in ['orbit_id','orbit_size','prefix','flat_lb','sum_m','exact_min_residual_s_for_S0_cover','status'] if k in rec}
        out.update(scan)
        records.append(out)
        if scan['all_budgets_blocked_until_smax'] is True:
            status_counter['ALL_BUDGETS_BLOCKED']+=1
        elif scan['all_budgets_blocked_until_smax'] is False:
            status_counter['HAS_SURVIVING_BUDGET']+=1
            first_survivor_s[scan['first_survivor']['s']]+=1
        else:
            status_counter['TRUNCATED_UNRESOLVED']+=1
        if len(records)<=10 or scan['all_budgets_blocked_until_smax'] is True or len(records)%100==0:
            print(f"{len(records)} orbit={rec['orbit_id']} smin={scan['s_min']} smax={scan['s_max_from_flattening']} allblocked={scan['all_budgets_blocked_until_smax']} first={None if not scan['first_survivor'] else scan['first_survivor']['s']}", flush=True)
    result={'purpose':'rescan S0 tight obstruction at residual budgets through s_max=19-flat_lb','meaning':'A surviving cover only shows that this S-free row/column-space obstruction is insufficient; it does not construct a tensor decomposition. ALL_BUDGETS_BLOCKED is still a bare S0 statement, not stable under enlarging S unless separately proven.','input':str(args.input),'orbits_scanned':len(records),'status_counts':dict(status_counter),'first_survivor_s_distribution':{str(k):int(v) for k,v in sorted(first_survivor_s.items())},'elapsed_sec':time.time()-t0,'records':records}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2,sort_keys=True,default=int)+'\n')
    print(json.dumps({k:result[k] for k in ['orbits_scanned','status_counts','first_survivor_s_distribution','elapsed_sec']},indent=2,sort_keys=True))
    print('wrote',args.out)
if __name__=='__main__': main()
