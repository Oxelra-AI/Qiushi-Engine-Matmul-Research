#!/usr/bin/env python3
"""Targeted minimization of genuine two-row cover certificates.

This focuses only on prefixes live after elementary cardinality where no one-row
cover from the selected row set closes the node, but an exact two-row cover does.
It reuses the analysis replayer/minimizer to see whether such pair conflicts have
small reusable learned clauses or depend on nearly the whole prefix/order state.
"""
from __future__ import annotations
import argparse, importlib.util, json, time
from pathlib import Path
ROOT=Path('research/research_record')
MOD=ROOT/'workspace/scripts/cover_conflict_minimize.py'
DEFAULT_FRONTIER=ROOT/'workspace/data/domain_dfs_soundness/branch1_prefix_d10_frontier.jsonl'
DEFAULT_COVER=ROOT/'workspace/data/domain_dfs_soundness/e11_wang_cap67_first512_cover.bin'
OUT=ROOT/'workspace/data/domain_dfs_soundness/pair_extra_minimize.json'

def load_mod():
    spec=importlib.util.spec_from_file_location('cmin', MOD)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--frontier',type=Path,default=DEFAULT_FRONTIER); ap.add_argument('--cover',type=Path,default=DEFAULT_COVER); ap.add_argument('--max-records',type=int,default=500); ap.add_argument('--pair-limit',type=int,default=64); ap.add_argument('--target-limit',type=int,default=6); ap.add_argument('--rounds',type=int,default=3); ap.add_argument('--out',type=Path,default=OUT)
    args=ap.parse_args(); t0=time.time(); m=load_mod(); rows5=m.load_rows(m.ROWS5); cover=m.load_rows(args.cover); repl=m.Replayer(rows5,cover)
    found=[]; minimized=[]; total=0; live=0; carddead=0
    with args.frontier.open() as f:
        for line in f:
            if total>=args.max_records or len(found)>=args.target_limit: break
            rec=json.loads(line); total+=1
            force=[int(x) for x in rec['force']]; excl=m.explicit_exclusions(rec)
            rep=repl.replay(force,excl)
            if rep['status']!='ok': continue
            need=19-len(set(force)); avail=m.pop(rep['dom'])
            if avail<need:
                carddead+=1; continue
            live+=1; rep['need']=need
            bs,bp=m.best_single_pair(rep,cover,args.pair_limit)
            sprune=bs is not None and bs[-1]<0; pprune=bp is not None and bp[13]<0
            if pprune and not sprune:
                rec0={'idx':total-1,'force':force,'exclude_size':len(excl),'need':need,'avail':avail,'single_best':bs,'pair_best':bp}
                found.append(rec0)
                rows=(bp[0],bp[1])
                mini=m.minimize_fixed(repl,force,excl,'two',rows,rounds=args.rounds,seed=3000+total)
                rrep=repl.replay(mini['A'],mini['E']) if mini else {'status':'no_mini'}
                s2=p2=None
                if mini and rrep['status']=='ok':
                    rrep['need']=19-len(set(mini['A']))
                    s2,p2=m.best_single_pair(rrep,cover,args.pair_limit)
                minimized.append({'source':rec0,'rows':list(rows),'minimized':mini,'best_single_after_min':s2,'best_pair_after_min':p2,'learned_clause':None if not mini else ' OR '.join([f'not x{p}' for p in mini['A']]+[f'x{q}' for q in mini['E']])})
    out={'schema':'s0908_pair_extra_minimize_v1','frontier':str(args.frontier),'cover':str(args.cover),'records_scanned':total,'live_seen':live,'cardinality_dead_seen':carddead,'pair_limit':args.pair_limit,'found_count':len(found),'found':found,'minimized':minimized,'elapsed_sec':time.time()-t0}
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()
