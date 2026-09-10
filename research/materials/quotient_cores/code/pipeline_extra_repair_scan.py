#!/usr/bin/env python3
"""analysis: residual-space scan adding extra B-repair slots to peer A-swap candidates.

The first residual test allowed B changes only in the slots where the peer's
Wang hill-climber changed A relative to a rank-23 deletion seed.  Those blocks
all had d>k.  Here we retain the same final A-list but add one or two extra
unchanged slots whose B-factors may also change.  When d=k the subspace
independent-transversal test is exact; a Hall-success immediately gives a full
candidate after linear C completion.
"""
from __future__ import annotations
import itertools, json, sys, time
from collections import Counter
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
import residual_repair_geometry as rg  # type: ignore

OUTDIR = Path('data/residual_repair')
PIPE = Path('data/pipeline_results/pipeline_summary.json')


def main():
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    D_cols = rg.D_columns_as_ints()
    sources = rg.load_sources()
    pipe = json.load(open(PIPE))
    records = []
    witnesses = []
    status_hist = Counter()
    exact_hist = Counter()

    for rec in pipe.get('results', []):
        if rec.get('status') not in ('BRENT_UNSAT', 'TRACE_REJECTED', 'BRENT_UNKNOWN'):
            continue
        if 'seed' not in rec or 'final_multiset' not in rec:
            continue
        seed_A = [int(x) for x in rec['seed']]
        final_A = [int(x) for x in rec['final_multiset']]
        changed = [i for i,(s,f) in enumerate(zip(seed_A, final_A)) if s != f]
        if not changed:
            continue
        for sname, terms in sources.items():
            for del_idx in rg.deletion_matches(terms, seed_A):
                seed_terms = list(terms[:del_idx] + terms[del_idx+1:])
                unchanged = [i for i in range(22) if i not in changed]
                cand = {
                    'name': rec.get('name'),
                    'peer_status': rec.get('status'),
                    'source': sname,
                    'delete_index': del_idx,
                    'deleted_A': int(terms[del_idx][0]),
                    'changed_slots': changed,
                    'changed_pairs': [{'slot': i, 'old_A': seed_A[i], 'new_A': final_A[i]} for i in changed],
                    'extra_scans': {},
                }
                for extra_count in [0, 1, 2]:
                    hist = Counter(); examples=[]; total=0
                    combos = [()] if extra_count == 0 else itertools.combinations(unchanged, extra_count)
                    for extra in combos:
                        block = tuple(sorted(changed + list(extra)))
                        res = rg.repair_test_from_slots(seed_terms, final_A, block, D_cols)
                        total += 1
                        status = res.get('status')
                        hist[status] += 1
                        status_hist[status] += 1
                        if res.get('d') == res.get('k'):
                            exact_hist['d_eq_k'] += 1
                            if res.get('hall_ok'):
                                exact_hist['hall_ok'] += 1
                            else:
                                exact_hist['hall_fail'] += 1
                        elif res.get('d') > res.get('k'):
                            exact_hist['d_gt_k'] += 1
                        else:
                            exact_hist['d_lt_k'] += 1
                        interesting = (status == 'REPAIR_FOUND') or (res.get('d') == res.get('k')) or (res.get('d') < res.get('k'))
                        if interesting and len(examples) < 30:
                            examples.append({
                                'extra_slots': list(extra),
                                'block': list(block),
                                'status': status,
                                'k': res.get('k'),
                                'd': res.get('d'),
                                'rank_L': res.get('rank_L'),
                                'H_dims': res.get('H_dims'),
                                'H_total_rank': res.get('H_total_rank'),
                                'H_tag_counts': res.get('H_tag_counts'),
                                'hall_ok': res.get('hall_ok'),
                                'hall_failure': res.get('hall_failure'),
                                'basis_cover_found': res.get('basis_cover_found'),
                                'chosen': res.get('chosen'),
                                'brent_diff': res.get('brent_diff'),
                            })
                        if status == 'REPAIR_FOUND':
                            wp = OUTDIR / f"rank22_extra_{rec.get('name')}_{sname}_del{del_idx}_extra{'_'.join(map(str,extra))}.json"
                            wp.write_text(json.dumps(res, indent=2, sort_keys=True) + '\n')
                            witnesses.append(str(wp))
                    cand['extra_scans'][str(extra_count)] = {'total': total, 'hist': dict(hist), 'examples': examples}
                records.append(cand)

    out = {
        'schema': 's0908_pipeline_extra_repair_scan_v1',
        'meaning': 'Local residual-space scan near peer A-swap candidates, allowing one/two extra unchanged B-slots to change; d=k cases are exact Hall/transversal tests, d<k cases are not excluded.',
        'candidate_records': records,
        'aggregate_status_hist': dict(status_hist),
        'aggregate_exact_hist': dict(exact_hist),
        'rank22_witnesses': witnesses,
        'elapsed_sec': time.time() - t0,
    }
    op = OUTDIR / 'pipeline_extra_repair_scan.json'
    op.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status':'ok','out':str(op),'records':len(records),'witnesses':witnesses,'status_hist':dict(status_hist),'exact_hist':dict(exact_hist),'elapsed_sec':out['elapsed_sec']}, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
