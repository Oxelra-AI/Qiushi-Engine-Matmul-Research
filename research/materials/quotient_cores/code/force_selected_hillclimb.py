#!/usr/bin/env python3
from __future__ import annotations
import argparse,json,subprocess
from pathlib import Path
ap=argparse.ArgumentParser(); ap.add_argument('--name',required=True); ap.add_argument('--constraints',required=True); ap.add_argument('--hill',required=True); ap.add_argument('--target',type=int,required=True); ap.add_argument('--outdir',default='data/wang_native/stochastic_min/force_controls')
args=ap.parse_args(); od=Path(args.outdir); od.mkdir(parents=True,exist_ok=True)
h=json.loads(Path(args.hill).read_text()); supp=sorted(map(int,h['best_support'])); force=','.join(map(str,supp)); out=od/(args.name+'_force_dfs.json')
cmd=['scripts/wang_domain_dfs_safe','--constraints',args.constraints,'--target',str(args.target),'--force-prefix',force,'--force-only','--max-solutions','1','--output',str(out),'--timeout','30']
cp=subprocess.run(cmd,capture_output=True,text=True,timeout=60)
res={'name':args.name,'support':supp,'cmd':cmd,'returncode':cp.returncode,'stdout':cp.stdout,'stderr':cp.stderr,'out':str(out)}
if out.exists(): res['dfs_json']=json.loads(out.read_text())
sp=od/(args.name+'_force_summary.json'); sp.write_text(json.dumps(res,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'ok','out':str(sp),'returncode':cp.returncode,'dfs':res.get('dfs_json')},indent=2,sort_keys=True))
