#!/usr/bin/env python3
"""CEGAR-style support search for full T333 length 20 Wang constraints.

Start with the low-dimensional rows that enable domain propagation, run the safe
DFS to get one candidate support, check it against the complete Wang LUT using a
fast membership test, add violated high-dimensional rows, and repeat.  If a
selected subset eventually has no support, that subset is a compact candidate
certificate skeleton; if supports remain, their violations identify where the
real pruning force lies.
"""
from __future__ import annotations

import argparse, json, struct, subprocess, sys, time
from collections import Counter
from pathlib import Path

S04 = Path("scripts")
if str(S04) not in sys.path:
    sys.path.insert(0, str(S04))
from wang_capacity_lazy import unpack_basis  # type: ignore
from core_capacity_from_wang_lut import load_lut  # type: ignore

ROOT = Path("research/research_record")
LUT_PATH = Path("data/wang_f2_lb20/wang_subspace_lut.pkl")
BIN = ROOT / "workspace/scripts/wang_domain_dfs_safe"
OUTDIR = ROOT / "workspace/data/wang_native/full_tensor_cegar"
MAGIC = b"WANG512\x01"


def points_from_basis(basis):
    pts=[]; d=len(basis)
    for m in range(1,1<<d):
        v=0
        for i,b in enumerate(basis):
            if (m>>i)&1: v ^= int(b)
        pts.append(v)
    return pts


def mask_words_from_basis(basis):
    words=[0]*8
    for p in points_from_basis(basis):
        words[p>>6] |= 1 << (p&63)
    return words


def rref_basis_for_membership(basis):
    # unpack_basis already returns RREF-like rows. Build pivot map by highest bit.
    piv={}
    for b in basis:
        x=int(b)
        if x:
            piv[x.bit_length()-1]=x
    return piv


def in_span(x, piv):
    x=int(x)
    while x:
        p=x.bit_length()-1
        b=piv.get(p)
        if b is None: return False
        x ^= b
    return True


def write_binary(row_records, selected, path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path,'wb') as f:
        f.write(MAGIC)
        f.write(struct.pack('<I', len(selected)))
        for idx in sorted(selected):
            rec=row_records[idx]
            f.write(struct.pack('<BBH', rec['cap'], rec['dim'], 0))
            for w in rec['words']:
                f.write(struct.pack('<Q', w))


def run_dfs(bin_path, target, timeout, out_path, used_path):
    cmd=[str(BIN),'--constraints',str(bin_path),'--target',str(target),'--timeout',str(timeout),'--max-solutions','1','--output',str(out_path),'--used-output',str(used_path)]
    try:
        p=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=timeout+60)
        data=json.loads(out_path.read_text()) if out_path.exists() else None
        return {'returncode':p.returncode,'stderr_tail':p.stderr[-2000:],'stdout':p.stdout,'json':data,'subprocess_timeout':False}
    except subprocess.TimeoutExpired as e:
        data=json.loads(out_path.read_text()) if out_path.exists() else None
        return {'returncode':None,'stderr_tail':(e.stderr or '')[-2000:] if isinstance(e.stderr, str) else '', 'stdout':(e.stdout or '') if isinstance(e.stdout, str) else '', 'json':data, 'subprocess_timeout':True}


def check_complete(row_records, support, length, max_add):
    viol=[]
    for rec in row_records:
        cap=rec['cap']
        if cap>=length: continue
        occ=0
        piv=rec['piv']
        for p in support:
            if in_span(p,piv): occ += 1
        if occ>cap:
            viol.append({'row_index':rec['row_index'],'key9':rec['key9'],'lb':rec['lb'],'cap':cap,'dim':rec['dim'],'occ':occ,'margin':occ-cap})
    viol.sort(key=lambda r:(-r['margin'], r['dim'], r['cap'], r['row_index']))
    return viol[:max_add], len(viol)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--length',type=int,default=20)
    ap.add_argument('--iterations',type=int,default=6)
    ap.add_argument('--timeout',type=int,default=120)
    ap.add_argument('--add-per-iter',type=int,default=50)
    ap.add_argument('--initial-max-dim',type=int,default=3)
    ap.add_argument('--initial-max-cap',type=int,default=5)
    args=ap.parse_args()
    OUTDIR.mkdir(parents=True,exist_ok=True)
    t0=time.time()
    lut,_=load_lut(LUT_PATH)
    row_records=[]
    initial=set()
    cap_hist=Counter(); dim_hist=Counter()
    for ri,(key9,lb0) in enumerate(lut.items()):
        key9=int(key9); lb=int(lb0); dim=key9&0xF; cap=args.length-lb
        basis=list(unpack_basis(key9))
        piv=rref_basis_for_membership(basis)
        words=mask_words_from_basis(basis)
        rec={'row_index':ri,'key9':key9,'lb':lb,'cap':cap,'dim':dim,'basis':basis,'piv':piv,'words':words}
        row_records.append(rec)
        if 0 <= cap <= args.initial_max_cap and dim <= args.initial_max_dim and any(words):
            initial.add(ri); cap_hist[cap]+=1; dim_hist[dim]+=1
    selected=set(initial)
    summary={'status':'running','length':args.length,'initial_rows':len(initial),'initial_cap_hist':dict(cap_hist),'initial_dim_hist':dict(dim_hist),'iterations':[],'elapsed_sec':None}
    for it in range(args.iterations):
        bin_path=OUTDIR/f'iter{it:02d}_rows{len(selected)}.bin'
        out_path=OUTDIR/f'iter{it:02d}_dfs.json'
        used_path=OUTDIR/f'iter{it:02d}_used_rows.json'
        write_binary(row_records, selected, bin_path)
        res=run_dfs(bin_path,args.length,args.timeout,out_path,used_path)
        entry={'iteration':it,'selected_rows':len(selected),'binary':str(bin_path),'dfs':res['json'],'stderr_tail':res['stderr_tail']}
        if not res['json']:
            entry['status']='dfs_failed'
            summary['iterations'].append(entry); break
        dfsj=res['json']
        if dfsj.get('solutions',0)==0:
            if dfsj.get('complete') is True and dfsj.get('timeout') is False and dfsj.get('early_solution_stop') is False and not res.get('subprocess_timeout'):
                entry['status']='complete_empty_on_selected_rows'
                summary['status']='selected_subset_excludes'
            else:
                entry['status']='unfinished_no_solution_seen'
                summary['status']='unfinished_no_solution_seen'
            summary['iterations'].append(entry); break
        sol=res['json']['solutions_head'][0]
        added,total_viol=check_complete(row_records,sol,args.length,args.add_per_iter)
        entry['status']='candidate_found'
        entry['candidate_support']=sol
        entry['complete_wang_total_violations']=total_viol
        entry['added_rows']=added
        entry['added_count']=len(added)
        summary['iterations'].append(entry)
        if total_viol==0:
            summary['status']='complete_wang_candidate_found'
            break
        before=len(selected)
        for v in added: selected.add(v['row_index'])
        if len(selected)==before:
            summary['status']='no_new_violated_rows_added'
            break
    summary['final_selected_rows']=len(selected)
    summary['elapsed_sec']=time.time()-t0
    if summary['status']=='running': summary['status']='iteration_limit_reached'
    (OUTDIR/'cegar_summary.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+"\n")
    print(json.dumps({'status':summary['status'],'iterations':len(summary['iterations']),'final_selected_rows':summary['final_selected_rows'],'elapsed_sec':summary['elapsed_sec'],'last':summary['iterations'][-1] if summary['iterations'] else None},indent=2,sort_keys=True))

if __name__=='__main__': main()
