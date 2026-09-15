"""Private frozen-496 registry: discovery is untrusted; emitted Lean checks bindings."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


def span(basis):
    values = {0}
    for code in basis:
        values |= {x ^ (code & 511) for x in tuple(values)}
    return frozenset(values)


def literal(values):
    return '[' + ', '.join(map(str, values)) + ']'


def generate(root, representatives, out, extra_candidates=None, transports=None):
    candidates = []
    for line in (out / 'logs/FrozenRegistry.Inspect.log').read_text().splitlines():
        if line.startswith('REGISTRY_CANDIDATE '):
            candidates.append(json.loads(line.removeprefix('REGISTRY_CANDIDATE ')))
    if not candidates:
        raise ValueError('Inspector returned no candidates; do not infer an empty proof inventory')
    if extra_candidates:
        candidates += json.loads(extra_candidates.read_text())
    transport_rows = ({r['index']: r for r in json.loads(transports.read_text()) if 'witness' in r}
                      if transports else {})
    prior_path = root / 'FrozenRegistry/checked.json'
    prior = ({r['index']: r for r in json.loads(prior_path.read_text())['entries']}
             if prior_path.exists() else {})
    for i, row in prior.items():
        if row['method'] == 'orbit_containment':
            transport_rows.setdefault(i, dict(row, candidate=row['source']))
    reps = json.loads(representatives.read_text())['rows']
    assert len(reps) == 496 and [r['index'] for r in reps] == list(range(496))
    available = [c for c in candidates if c['basis'] is not None]
    available.append({'basis': [], 'bound': 21, 'module': 'FrozenRegistry.Bridge',
                      'theorem': 'QiushiMatmul.FrozenRegistry.zero_quotient_bound'})
    by_space = {}
    for candidate in available:
        key = span(candidate['basis'])
        old = by_space.get(key)
        score = (candidate['bound'], -len(candidate['theorem']), candidate['theorem'])
        if old is None or score > old[0]:
            by_space[key] = (score, candidate)
    lines = ['import FrozenRegistry.Bridge']
    if transport_rows:
        lines += ['import FrozenRegistry.TransportBindings']
    lines += ['',
             'set_option maxHeartbeats 16000000', 'set_option maxRecDepth 100000', '',
             'namespace QiushiMatmul.FrozenRegistry', '']
    registry = []
    for rep in reps:
        key = span(rep['basis'])
        direct = by_space.get(key)
        choices = [(source, 'equal_span') for source in [direct[1]]
                   if source['bound'] >= rep['lb']] if direct else []
        if not choices:
            choices = [(entry[1], 'contained_span') for space, entry in by_space.items()
                       if key <= space and entry[1]['bound'] >= rep['lb']]
            choices.sort(key=lambda pair: (len(span(pair[0]['basis'])), -pair[0]['bound'], pair[0]['theorem']))
        previous = prior.get(rep['index'])
        if previous and previous['method'] in ['equal_span', 'contained_span', 'zero_quotient_adapter']:
            choices = [(previous['source'], 'equal_span' if previous['method'] == 'zero_quotient_adapter'
                        else previous['method'])]
        elif previous and previous['method'] == 'orbit_containment':
            choices = []
        row = dict(rep, status='unbound', best_same_span=direct[1] if direct else None)
        if choices or rep['lb'] == 0 or rep['index'] == 416 or rep['index'] in transport_rows:
            name = f'rep{rep["index"]:03}'
            row.update(status='pending_kernel_check', declaration='QiushiMatmul.FrozenRegistry.' + name)
            lines += [f'theorem {name} :',
                      f'    QuotientRankAtLeast (spanCodes (frozenWangTable.basis {rep["index"]}))',
                      f'      (frozenWangTable.lower {rep["index"]}) := by',
                      f'  rw [show frozenWangTable.basis {rep["index"]} = {literal(rep["basis"])} by decide,',
                      f'      show frozenWangTable.lower {rep["index"]} = {rep["lb"]} by decide]']
            if rep['lb'] == 0:
                row['method'] = 'zero_bound'
                lines += ['  intro r hr', '  omega', '']
            elif rep['index'] == 416:
                row.update(method='reversed_exact_orbit', candidate={
                    'theorem': 'QiushiMatmul.step113_orbit416_lb17',
                    'module': 'QiushiBranch416Extraction', 'basis': [272, 4, 1], 'bound': 17})
                lines += ['  exact bound416', '']
            elif not choices and rep['index'] in transport_rows:
                transport = transport_rows[rep['index']]
                row.update(method='orbit_containment', candidate=transport['candidate'],
                           witness=transport['witness'])
                lines += [f'  exact Transport.bound{rep["index"]:03}', '']
            else:
                candidate, method = choices[0]
                row.update(candidate=candidate, method=(
                    'zero_quotient_adapter' if rep['index'] == 495 else method))
                lines += [f'  have h := {candidate["theorem"]}',
                          f'  change QuotientRankAtLeast (spanCodes {literal(candidate["basis"])}) {candidate["bound"]} at h',
                          f'  exact {"bind_exact" if method == "equal_span" else "bind_contained"}',
                          f'    {literal(rep["basis"])} {literal(candidate["basis"])} h',
                          '    (by decide)' + (' (by decide)' if method == 'equal_span' else '') + ' (by decide)', '']
        else:
            row['reason'] = ('same_span_bound_below_frozen_label' if direct else
                             'no_parsed_same_span_bound_in_imported_closure')
        registry.append(row)
    names = [row['declaration'] for row in registry if row['status'] == 'pending_kernel_check']
    checked = [row for row in registry if row['status'] == 'pending_kernel_check']
    source_modules = {row['candidate']['module'] for row in checked if 'candidate' in row}
    optional_imports = {m for m in source_modules if m.startswith('FrozenRegistry.')}
    if any(m.startswith('QiushiPlane413') for m in source_modules):
        optional_imports.add('FrozenRegistry.AdditionalSources')
    for module in sorted(optional_imports):
        if not re.fullmatch(r'FrozenRegistry\.[A-Za-z][A-Za-z0-9_]*', module):
            raise ValueError('Invalid registry source module')
        if f'import {module}' not in lines:
            lines.insert(1, f'import {module}')
    lines += ['def checkedIds : List Nat :=',
              '  ' + literal(row['index'] for row in checked), '',
              'end QiushiMatmul.FrozenRegistry', '']
    (root / 'FrozenRegistry/Bindings.lean').write_text('\n'.join(lines))
    manifest = {'schema': 1, 'entries': [
        {k: row[k] for k in ['index', 'basis', 'lb', 'declaration', 'method']} |
        ({'source': {k: row['candidate'][k] for k in ['theorem', 'module', 'basis', 'bound']}}
         if 'candidate' in row else {}) |
        ({'witness': row['witness']} if 'witness' in row else {}) for row in checked]}
    (root / 'FrozenRegistry/checked.json').write_text(json.dumps(manifest, indent=2) + '\n')
    (out / 'candidates.json').write_text(json.dumps(candidates, indent=2) + '\n')
    (out / 'registry.json').write_text(json.dumps(registry, indent=2) + '\n')
    unbound = [row for row in registry if row['status'] == 'unbound']
    (out / 'unbound.json').write_text(json.dumps(unbound, indent=2) + '\n')
    print(json.dumps({'candidates': len(candidates), 'parsed_spaces': len(by_space),
                      'proposed_bindings': len(names), 'unbound_ids': [row['index'] for row in unbound]}), flush=True)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_output(root, out, imports):
    if root == out or root.is_relative_to(out):
        raise ValueError('Output must not contain the source root')
    lib = out / 'lib'
    for path in imports:
        path = path.resolve()
        if lib.is_relative_to(path) or path.is_relative_to(lib):
            raise ValueError('Output library must be separate from every import directory')


def checked_names(manifest):
    entries = manifest['entries']
    ids = [row['index'] for row in entries]
    if ids != sorted(set(ids)) or any(not 0 <= i < 496 for i in ids):
        raise ValueError('Manifest indices must be unique, sorted, and within Fin 496')
    names = [f'QiushiMatmul.FrozenRegistry.rep{i:03}' for i in ids]
    if names != [row['declaration'] for row in entries]:
        raise ValueError('Manifest declaration/index mismatch')
    return names


def validate_audit(manifest, log):
    names = checked_names(manifest)
    axioms = re.findall(r'^REGISTRY_AXIOMS ([^:]+): (.+)$', log, re.MULTILINE)
    types = re.findall(r'^REGISTRY_TYPE ([^:]+):', log, re.MULTILINE)
    counts = re.findall(r'^REGISTRY_CHECKED (\d+)$', log, re.MULTILINE)
    if [name for name, _ in axioms] != names or types != names or counts != [str(len(names))]:
        raise ValueError('Missing, duplicate, or inconsistent Lean type/axiom audit')
    for _, printed in axioms:
        actual = set(printed.strip('[]').replace(',', ' ').split())
        if not actual <= {'propext', 'Classical.choice', 'Quot.sound'}:
            raise ValueError('Unexpected axiom in audit log')
    return len(names)


def validate_global_audit(log):
    names = ['QiushiMatmul.FrozenRegistry.' + suffix for suffix in
             ['all_representatives', 'L0_rank_sound', 'coverage_with_rank_bound']]
    axioms = re.findall(r'^FROZEN_GLOBAL_AXIOMS ([^:]+): (.+)$', log, re.MULTILINE)
    counts = re.findall(r'^FROZEN_GLOBAL_CHECKED (\d+)$', log, re.MULTILINE)
    if [name for name, _ in axioms] != names or counts != ['496']:
        raise ValueError('Missing, duplicate, or inconsistent global type/axiom audit')
    for _, printed in axioms:
        actual = set(printed.strip('[]').replace(',', ' ').split())
        if not actual <= {'propext', 'Classical.choice', 'Quot.sound'}:
            raise ValueError('Unexpected axiom in global audit log')


def replay_roots(manifest):
    count = len(checked_names(manifest))
    roots = ['FrozenRegistry.Bindings', 'FrozenRegistry.Tests']
    if count == 496:
        roots += ['FrozenRegistry.Remaining', 'FrozenRegistry.GlobalTests']
    return roots


def build(root, environment_file, import_dirs, out, modules):
    environment = json.loads(environment_file.read_text())
    imports = [p.resolve() for p in import_dirs]
    imports += [Path(p).resolve() for p in environment['lean_path'].split(os.pathsep) if p]
    check_output(root, out, imports)
    lib = out / 'lib'
    logs = out / 'logs'
    lib.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [lib, *imports])))
    results = []
    for module in modules:
        if not re.fullmatch(r'(?:FrozenRegistry\.[A-Za-z][A-Za-z0-9_]*|Qiushi[A-Za-z0-9_]+)', module):
            raise ValueError('Only registry and existing Qiushi modules may be compiled')
        source = root / (module.replace('.', '/') + '.lean')
        target = lib / (module.replace('.', '/') + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        log = logs / (module + '.log')
        strict = module.startswith('FrozenRegistry.')
        cmd = [environment['lean'], '-j1', f'-DwarningAsError={str(strict).lower()}',
               '-o', str(target), str(source)]
        before = digest(source)
        with log.open('w') as stream:
            result = subprocess.run(cmd, cwd=root, env=env, stdout=stream, stderr=subprocess.STDOUT)
        record = {'module': module, 'exit_code': result.returncode,
                  'source_sha256': before,
                  'command': cmd, 'lean_path': env['LEAN_PATH']}
        if digest(source) != before:
            raise ValueError('Source changed during compilation')
        if result.returncode == 0:
            record['olean_sha256'] = digest(target)
        (logs / (module + '.json')).write_text(json.dumps(record, indent=2) + '\n')
        results.append(record)
        print(module, 'exit', result.returncode, flush=True)
        if result.returncode:
            print(log.read_text()[-12000:], flush=True)
            break
    return results


def build_missing(root, environment_file, import_dirs, out, modules):
    from source_graph import imports as source_imports
    environment = json.loads(environment_file.read_text())
    libraries = [out / 'lib', *import_dirs]
    libraries += [Path(p) for p in environment['lean_path'].split(os.pathsep) if p]
    pending, seen = [], set()

    def visit(module, force=False):
        if module in seen:
            return
        seen.add(module)
        relative = module.replace('.', '/')
        if not force and not module.startswith('FrozenRegistry.') and any(
                (p / (relative + '.olean')).is_file() for p in libraries):
            return
        source = root / (relative + '.lean')
        if not source.is_file():
            raise ValueError(f'Missing source and compiled import: {module}')
        for dependency in source_imports(source.read_text()):
            visit(dependency)
        pending.append(module)

    for module in modules:
        visit(module, force=True)
    print('Missing import closure:', pending, flush=True)
    return build(root, environment_file, import_dirs, out, pending)


def replay(root, environment_file, import_dirs, out):
    out.mkdir(parents=True, exist_ok=True)
    receipt = out / 'checkpoint.json'
    receipt.unlink(missing_ok=True)
    manifest_file = root / 'FrozenRegistry/checked.json'
    manifest_hash = digest(manifest_file)
    modules = replay_roots(json.loads(manifest_file.read_text()))
    try:
        results = build_missing(root, environment_file, import_dirs, out, modules)
    except (OSError, ValueError) as error:
        print(f'Replay prerequisite failed: {error}', flush=True)
        return False
    if not results or any(r['exit_code'] for r in results):
        return False
    manifest = json.loads(manifest_file.read_text())
    if digest(manifest_file) != manifest_hash:
        raise ValueError('Manifest changed during replay')
    count = validate_audit(manifest, (out / 'logs/FrozenRegistry.Tests.log').read_text())
    if count == 496:
        validate_global_audit((out / 'logs/FrozenRegistry.GlobalTests.log').read_text())
        remaining_log = (out / 'logs/FrozenRegistry.Remaining.log').read_text()
        if (re.findall(r'^REMAINING_GOALS_CHECKED (\d+)$', remaining_log, re.MULTILINE) != ['0']
                or re.search(r'^REMAINING_GOAL ', remaining_log, re.MULTILINE)):
            raise ValueError('A complete registry must have no remaining rank goals')
    record = {'checked': count, 'manifest_sha256': manifest_hash,
              'environment_sha256': digest(environment_file), 'modules': results,
              'global_rank_sound': count == 496,
              'remaining_ids': sorted(set(range(496)) - {r['index'] for r in manifest['entries']})}
    receipt.write_text(json.dumps(record, indent=2) + '\n')
    registry_file = out / 'registry.json'
    if registry_file.exists():
        registry = json.loads(registry_file.read_text())
        for row in registry:
            if row['index'] not in record['remaining_ids']:
                row['status'] = 'kernel_checked'
        registry_file.write_text(json.dumps(registry, indent=2) + '\n')
    print(json.dumps({'checked': count, 'remaining_ids': record['remaining_ids']}), flush=True)
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['build', 'build-missing', 'generate', 'replay'])
    parser.add_argument('modules', nargs='*')
    parser.add_argument('--environment', type=Path,
                        help='Pinned environment JSON with lean and lean_path fields')
    parser.add_argument('--import-dir', type=Path, action='append', default=[],
                        help='Additional read-only import directory, in precedence order')
    parser.add_argument('--representatives', type=Path,
                        help='Discovery only: JSON with the 496 frozen rows')
    parser.add_argument('--extra-candidates', type=Path, help='Additional checked span-adapter metadata')
    parser.add_argument('--transports', type=Path, help='Exact orbit witnesses and existing source bounds')
    parser.add_argument('--output', type=Path, required=True,
                        help='Private output directory, separate from all import libraries')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    out = args.output.resolve()
    if args.action == 'generate':
        if args.representatives is None:
            parser.error('generate requires --representatives')
        generate(root, args.representatives, out, args.extra_candidates, args.transports)
        return
    if args.environment is None:
        parser.error('build/replay requires --environment')
    if args.action == 'replay':
        raise SystemExit(not replay(root, args.environment, args.import_dir, out))
    if not args.modules:
        parser.error('build requires at least one focused module')
    builder = build_missing if args.action == 'build-missing' else build
    results = builder(root, args.environment, args.import_dir, out, args.modules)
    raise SystemExit(any(row['exit_code'] for row in results))


if __name__ == '__main__':
    main()
