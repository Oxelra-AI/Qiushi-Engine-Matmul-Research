#!/usr/bin/env python3
"""analysis: measure reuse of minimized cover-conflict clauses on a saved frontier.

A minimized clause from cover_conflict_minimize has form
  OR_{p in A} not x_p OR OR_{q in E} x_q,
so it blocks any frontier prefix whose forced set contains A and whose explicit
numeric-order excluded set contains E.  This script counts how many frontier
records are blocked by such learned clauses, separating records already dead by
`avail < need` from records live after that elementary cardinality test.
"""
from __future__ import annotations
import argparse, json, time
from pathlib import Path
from collections import Counter, defaultdict
ROOT=Path('research/research_record')
DEFAULT_FRONTIER=ROOT/'workspace/data/domain_dfs_soundness/branch1_prefix_d10_frontier.jsonl'
DEFAULT_CLAUSES=ROOT/'workspace/data/domain_dfs_soundness/conflict_min_branch1_first500.json'
OUT=ROOT/'workspace/data/domain_dfs_soundness/learned_clause_coverage.json'

def load_clauses(path):
    obj=json.loads(path.read_text())
    clauses=[]
    for k,m in enumerate(obj.get('minimized_head',[])):
        A=tuple(m['minimized']['A']); E=tuple(m['minimized']['E'])
        clauses.append({'id':k,'A':A,'E':E,'kind':m.get('kind'),'rows':m.get('rows'),'literal_count':len(A)+len(E),'source_idx':m.get('source_idx')})
    return clauses

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--frontier',type=Path,default=DEFAULT_FRONTIER); ap.add_argument('--clauses',type=Path,default=DEFAULT_CLAUSES); ap.add_argument('--max-records',type=int,default=0); ap.add_argument('--out',type=Path,default=OUT)
    args=ap.parse_args(); t0=time.time(); clauses=load_clauses(args.clauses)
    stats=Counter(); hit_by_clause=Counter(); live_hit_by_clause=Counter(); card_hit_by_clause=Counter(); first_hits=[]; overlap_hist=Counter(); examples_unblocked_live=[]
    total=0
    with args.frontier.open() as f:
        for line in f:
            if args.max_records and total>=args.max_records: break
            rec=json.loads(line); total+=1
            force=set(rec['force']); excl=set(rec.get('exclude_lt_next',[]))
            live = rec['avail'] >= rec['need']
            stats['total']+=1; stats['live_after_cardinality' if live else 'cardinality_dead']+=1
            hits=[]
            for c in clauses:
                if all(p in force for p in c['A']) and all(q in excl for q in c['E']):
                    hits.append(c['id']); hit_by_clause[c['id']]+=1
                    if live: live_hit_by_clause[c['id']]+=1
                    else: card_hit_by_clause[c['id']]+=1
            if hits:
                stats['blocked_by_any']+=1
                if live: stats['live_blocked_by_any']+=1
                else: stats['cardinality_dead_blocked_by_any']+=1
                overlap_hist[str(min(len(hits),10))]+=1
                if len(first_hits)<30:
                    first_hits.append({'idx':total-1,'force':rec['force'],'need':rec['need'],'avail':rec['avail'],'hits':hits})
            elif live:
                stats['live_not_blocked']+=1
                if len(examples_unblocked_live)<30:
                    examples_unblocked_live.append({'idx':total-1,'force':rec['force'],'need':rec['need'],'avail':rec['avail'],'next_min':rec.get('next_min')})
    out={'schema':'s0908_learned_clause_coverage_v1','frontier':str(args.frontier),'clauses_path':str(args.clauses),'records_read':total,'clause_count':len(clauses),'clauses':clauses,'stats':dict(stats),'hit_by_clause':dict(hit_by_clause),'live_hit_by_clause':dict(live_hit_by_clause),'cardinality_dead_hit_by_clause':dict(card_hit_by_clause),'overlap_hist':dict(overlap_hist),'first_hits':first_hits,'examples_unblocked_live':examples_unblocked_live,'elapsed_sec':time.time()-t0}
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
