#!/usr/bin/env python3
"""Force-test zero-violation supports from wang_hillclimb through wang_domain_dfs_safe."""
from __future__ import annotations
import argparse, json, subprocess
from pathlib import Path

SESSION = Path("research/research_record")
BIN = SESSION / "workspace/scripts/wang_domain_dfs_safe"

def run_force(name, constraints, hill_json, target, outdir):
    data=json.loads(Path(hill_json).read_text())
    supp=data.get('best_support',[])
    force=','.join(str(int(x)) for x in sorted(supp))
    out=Path(outdir)/f"{name}_force_dfs.json"
    cmd=[str(BIN),'--constraints',str(constraints),'--target',str(target),'--force-prefix',force,'--force-only','--max-solutions','1','--output',str(out),'--timeout','30']
    cp=subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    res={"name":name,"cmd":cmd,"returncode":cp.returncode,"stdout":cp.stdout,"stderr":cp.stderr,"support":sorted(supp),"out":str(out)}
    if out.exists():
        try: res['dfs_json']=json.loads(out.read_text())
        except Exception as e: res['dfs_read_error']=str(e)
    return res

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--outdir',default=str(SESSION/'workspace/data/wang_native/stochastic_min/force_controls'))
    args=ap.parse_args()
    od=Path(args.outdir); od.mkdir(parents=True,exist_ok=True)
    jobs=[
        ('e11_n21_hill_zero', SESSION/'workspace/data/wang_native/quotient_binaries/e11_all_n21.bin', SESSION/'workspace/data/wang_native/stochastic_min/hillclimb_e11_n21_pilot.json', 21),
        ('rank2_n22_hill_zero', SESSION/'workspace/data/wang_native/quotient_binaries/rank2_all_n22.bin', SESSION/'workspace/data/wang_native/stochastic_min/hillclimb_rank2_n22_pilot.json', 22),
    ]
    records=[]
    for j in jobs:
        records.append(run_force(*j, outdir=od))
    summary={"status":"ok","records":records}
    sp=od/'force_hillclimb_supports_summary.json'
    sp.write_text(json.dumps(summary,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":"ok","out":str(sp),"records":[{"name":r['name'],"returncode":r['returncode'],"dfs":r.get('dfs_json')} for r in records]},indent=2,sort_keys=True))

if __name__=='__main__': main()
