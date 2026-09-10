#!/usr/bin/env python3
"""Smoke test: can essential scripts resolve imports from manifested files alone?"""
import json, tempfile, os, shutil

m = json.load(open('research/research_record/deliverables/report/proof_manifest.json'))

with tempfile.TemporaryDirectory() as td:
    for a in m['artifacts']:
        if a['role'] in ('verification_source_script',
                         'verification_transitive_dependency',
                         'peer_corroboration_script'):
            src = a['path']
            dst = os.path.join(td, src)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copy2(src, dst)

    results = {}
    for a in m['artifacts']:
        if a['role'] not in ('verification_source_script',
                             'verification_transitive_dependency',
                             'peer_corroboration_script'):
            continue
        sp = a['path']
        name = os.path.basename(sp)
        with open(sp) as f:
            lines = f.readlines()
        local_imports = [l.strip() for l in lines
                         if ('import wang_capacity' in l
                             or 'import analysis' in l
                             or 'from analysis' in l)
                         and not l.strip().startswith('#')]
        if not local_imports:
            results[name] = 'no_local_imports'
            continue
        for imp_line in local_imports:
            mod_name = imp_line.split('import ')[1].split(' as ')[0].split('(')[0].strip()
            found = False
            for root, _dirs, files in os.walk(td):
                if mod_name + '.py' in files:
                    found = True
                    break
            results[f"{name} -> {mod_name}"] = "FOUND" if found else "MISSING"

    all_ok = True
    for k, v in sorted(results.items()):
        ok = v != "MISSING"
        if not ok:
            all_ok = False
        print(f"  {'OK' if ok else 'FAIL'} {k}: {v}")
    print(f"\nAll resolved: {all_ok}")
