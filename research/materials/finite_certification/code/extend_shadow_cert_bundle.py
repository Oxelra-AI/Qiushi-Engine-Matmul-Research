#!/usr/bin/env python3
"""Create an extended analysis shadow-certificate bundle including the fresh analysis certificate."""
from __future__ import annotations
import json
from pathlib import Path
BASE=Path('data/shadow_certificate/shadow_certificate_analysis.json')
analysis=Path('data/shadow_certificate/target_certificate.json')
OUT=Path('data/shadow_certificate/shadow_certificate_extended_bundle.json')
base=json.loads(BASE.read_text())
st=json.loads(analysis.read_text())
cert=st['certificate']
cert['name']='min4'
entry={'certificate':cert,'classification':st['classification'],'applications':st['applications']}
# Replace if rerun
base['certificates']=[e for e in base['certificates'] if e['certificate'].get('name')!='min4']+[entry]
base['schema']='s0908_shadow_certificate_extended_bundle_v1'
base['added_min4_from']=str(analysis)
OUT.write_text(json.dumps(base,indent=2,sort_keys=True)+'\n')
print(json.dumps({'out':str(OUT),'certificate_names':[e['certificate'].get('name') for e in base['certificates']]},indent=2,sort_keys=True))
