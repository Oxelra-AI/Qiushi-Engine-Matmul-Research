#!/usr/bin/env python3
"""Generic coverage counter for minimized learned clauses from analysis files."""
from __future__ import annotations
import argparse,json,time
from pathlib import Path
from collections import Counter
ROOT=Path('research/research_record')
DEFAULT_FRONTIER=ROOT/'workspace/data/domain_dfs_soundness/branch1_prefix_d10_frontier.jsonl'
OUT=ROOT/'workspace/data/domain_dfs_soundness/generic_clause_coverage.json'

def extract_clauses(path):
    obj=json.loads(path.read_text()); clauses=[]
    seq=obj.get('minimized_head') or obj.get('minimized') or []
    for k,m in enumerate(seq):
        mini=m.get('minimized',m)
        A=tuple(int(x) for x in mini.get('A',[])); E=tuple(int(x) for x in mini.get('E',[]))
        if not A and not E: continue
        clauses.append({'id':k,'A':A,'E':E,'literal_count':len(A)+len(E),'kind':m.get('kind') or mini.get('certificate',{}).get('kind'),'rows':m.get('rows') or mini.get('certificate',{}).get('rows'),'source_idx':m.get('source_idx') or m.get('source',{}).get('idx')})
    return clauses

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--frontier',type=Path,default=DEFAULT_FRONTIER); ap.add_argument('--clauses',type=Path,required=True); ap.add_argument('--max-records',type=int,default=50000); ap.add_argument('--out',type=Path,default=OUT)
    args=ap.parse_args(); clauses=extract_clauses(args.clauses); t0=time.time(); stats=Counter(); hit=Counter(); livehit=Counter(); cardhit=Counter(); first=[]; unblocked=[]; overlap=Counter(); total=0
    with args.frontier.open() as f:
        for line in f:
            if args.max_records and total>=args.max_records: break
            rec=json.loads(line); total+=1; force=set(rec['force']); excl=set(rec.get('exclude_lt_next',[])); live=rec['avail']>=rec['need']
            stats['total']+=1; stats['live_after_cardinality' if live else 'cardinality_dead']+=1
            hs=[]
            for c in clauses:
                if all(p in force for p in c['A']) and all(q in excl for q in c['E']):
                    hs.append(c['id']); hit[c['id']]+=1; livehit[c['id']]+=int(live); cardhit[c['id']]+=int(not live)
            if hs:
                stats['blocked_by_any']+=1; stats['live_blocked_by_any']+=int(live); stats['cardinality_dead_blocked_by_any']+=int(not live); overlap[str(min(len(hs),10))]+=1
                if len(first)<40: first.append({'idx':total-1,'force':rec['force'],'need':rec['need'],'avail':rec['avail'],'hits':hs})
            elif live:
                stats['live_not_blocked']+=1
                if len(unblocked)<20: unblocked.append({'idx':total-1,'force':rec['force'],'need':rec['need'],'avail':rec['avail'],'next_min':rec.get('next_min')})
    out={'schema':'s0908_generic_clause_coverage_v1','frontier':str(args.frontier),'clauses_path':str(args.clauses),'records_read':total,'clause_count':len(clauses),'clauses':clauses,'stats':dict(stats),'hit_by_clause':dict(hit),'live_hit_by_clause':dict(livehit),'cardinality_dead_hit_by_clause':dict(cardhit),'overlap_hist':dict(overlap),'first_hits':first,'examples_unblocked_live':unblocked,'elapsed_sec':time.time()-t0}
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
