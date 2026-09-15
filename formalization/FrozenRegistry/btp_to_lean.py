"""Translate existing BTP leaves to exhaustive count splits and checked Farkas rays.

No integer solver or orbit search is used. Optional root compression proposes
a rationalized LP dual ray, checks its exact integer arithmetic, and emits the
same Lean Farkas semantics. All rank premises are existing declarations.
"""

import argparse
from collections import Counter
from fractions import Fraction
from functools import reduce
import hashlib
import importlib.util
import inspect
import json
from math import gcd, lcm
from pathlib import Path
import re

from btp_archive import (ARCHIVE_BYTES, ARCHIVE_SHA256, CERTIFICATE_SHA256, Archive,
                         canonical_image, lean_transport, read_metadata, rref,
                         trace_dependencies)
from generate_certificate import span
from source_graph import imports as source_imports


def check_source_imports(module, target, root=None):
    root = root or Path(__file__).resolve().parents[1]
    visiting, done = set(), set()

    def visit(name):
        if not name.startswith('FrozenRegistry.') or name in done:
            return
        if (name == 'FrozenRegistry.Bindings' or re.match(rf'FrozenRegistry\.Btp{target}(?:[A-Z]|$)', name)
                or name in visiting):
            raise ValueError('use an acyclic source adapter, not the aggregate registry')
        path = root / (name.replace('.', '/') + '.lean')
        if not path.is_file():
            raise ValueError(f'unavailable source adapter {name}')
        visiting.add(name)
        for child in source_imports(path.read_text()):
            visit(child)
        visiting.remove(name)
        done.add(name)

    visit(module)


def rank_source(original, entry):
    if entry['method'] == 'orbit_containment':
        return dict(module='FrozenRegistry.TransportBindings',
                    theorem=f'QiushiMatmul.FrozenRegistry.Transport.bound{original["index"]:03}',
                    basis=original['basis'], bound=original['lb'])
    return entry['source']


def singleton_cover_certificate(meta):
    pivots = sum(1 << (c.bit_length() - 1) for c in meta['basis'])
    sections = [c for c in range(1, 512) if not c & pivots]
    best = {}
    for row in meta['source_rows']:
        members = span(row['basis'])
        labels = [q for q, c in enumerate(sections) if c in members]
        if len(labels) == 1:
            q = labels[0]
            if q not in best or row['lb'] > best[q]['lb']:
                best[q] = row
    if len(best) != len(sections):
        return None
    rhs = sum(meta['target'] - best[q]['lb'] for q in range(len(sections))) - meta['target']
    if rhs >= 0:
        return None
    refs = [dict(type='occ', row=best[q]['idx'], multiplier=1) for q in range(len(sections))]
    refs.append(dict(type='total_ge', multiplier=1))
    leaf = dict(path='', lower={}, upper={}, used_rows=refs, rhs=rhs)
    return dict(basis=meta['basis'], branch=dict(tree=dict(type='leaf', path=''), certs=[leaf]))


def root_rows(meta):
    pivots = sum(1 << (c.bit_length() - 1) for c in meta['basis'])
    sections = [c for c in range(1, 512) if not c & pivots]
    matrix, bounds, refs = [], [], []
    for row in meta['source_rows']:
        members = span(row['basis'])
        matrix.append([int(c in members) for c in sections])
        bounds.append(meta['target'] - row['lb'])
        refs.append(dict(type='occ', row=row['idx']))
    matrix.append([-1] * len(sections))
    bounds.append(-meta['target'])
    refs.append(dict(type='total_ge'))
    for q in range(len(sections)):
        matrix.append([-int(j == q) for j in range(len(sections))])
        bounds.append(0)
        refs.append(dict(type='nonneg', label=q + 1))
    return matrix, bounds, refs


def checked_root_certificate(meta, weights):
    matrix, bounds, refs = root_rows(meta)
    if (len(weights) != len(refs) or
            any(type(w) is not int or w < 0 for w in weights)):
        raise ValueError('invalid root Farkas weights')
    rhs = sum(w * b for w, b in zip(weights, bounds))
    if rhs >= 0 or any(sum(w * row[q] for w, row in zip(weights, matrix))
                       for q in range(len(matrix[0]))):
        raise ValueError('root ray fails exact integer cancellation or strict negativity')
    used = [dict(ref, multiplier=w) for ref, w in zip(refs, weights) if w]
    leaf = dict(path='', lower={}, upper={}, used_rows=used, rhs=rhs)
    return dict(basis=meta['basis'], branch=dict(tree=dict(type='leaf', path=''), certs=[leaf]))


def root_farkas_certificate(meta):
    import numpy as np
    from scipy.optimize import linprog

    matrix, bounds, refs = root_rows(meta)
    n = len(matrix[0])
    dual = linprog(bounds, A_eq=np.vstack([np.array(matrix).T, np.ones(len(refs))]),
                   b_eq=np.r_[np.zeros(n), 1], bounds=(0, None), method='highs',
                   options={'threads': 1, 'time_limit': 30})
    if not dual.success or dual.fun >= 0:
        return None
    fractions = [Fraction(float(x)).limit_denominator(100000) for x in dual.x]
    denominator = lcm(*(x.denominator for x in fractions))
    weights = [int(x * denominator) for x in fractions]
    divisor = reduce(gcd, weights)
    if not divisor:
        raise ValueError('zero root Farkas ray')
    return checked_root_certificate(meta, [w // divisor for w in weights])


def translate(row, records, all_rows, registry, source_only=False):
    trace = trace_dependencies(row, records, all_rows)
    basis, target = row['basis'], row['lb'] - 1
    pivots = sum(1 << (c.bit_length() - 1) for c in basis)
    sections = [c for c in range(1, 512) if not c & pivots]
    by_basis = {tuple(r['basis']): r for r in all_rows}
    known = {r['index']: r for r in registry['entries']}
    cursor = 0
    sources, source_keys, transports, ledger = [], {}, {}, {}
    checked_modules = set()

    def register(actual, original, transport):
        entry = known.get(original['index'])
        if entry is None or not entry.get('source'):
            raise ValueError(f'unregistered rank prerequisite {original["index"]}')
        source = rank_source(original, entry)
        if source['module'] not in checked_modules:
            check_source_imports(source['module'], row['index'])
            checked_modules.add(source['module'])
        if not all(preimage in span(source['basis']) for _, preimage in transport['pairs']):
            raise ValueError(f'prerequisite {original["index"]} needs its registry orbit adapter')
        if source['bound'] < original['lb']:
            raise ValueError('original source bound too weak')
        if actual not in source_keys:
            index = len(sources)
            source_keys[actual] = index
            sources.append(dict(idx=index, orig=index, basis=list(actual),
                                orbit=original['index'], lb=original['lb']))
            transports[index] = transport
            ledger[str(original['index'])] = dict(orbit=original['index'],
                lb=source['bound'], basis_codes=source['basis'],
                theorem=source['theorem'], module=source['module'])
        return source_keys[actual]

    def metadata():
        return dict(plane=row['index'], module_prefix=f'Btp{row["index"]}', name_tag='Btp',
                    basis=basis, target=target, n_live=len(sections), n_occ=len(sources),
                    n_dead=1, live_list=list(range(len(sections))), source_rows=sources,
                    dead_witnesses=[dict(basis=basis)])

    if source_only:
        for witness in trace['witnesses']:
            register(tuple(witness['basis']), all_rows[witness['source_id']],
                     witness['lean_transport'])
        return metadata(), None, dict(entries=ledger), transports

    def read_node(prefix, maximum):
        nonlocal cursor
        depth, mask, query, store = records[cursor]
        if len(prefix) == depth:
            selected = [sections[q] for i, q in enumerate(prefix) if mask >> i & 1]
            actual = rref([*basis, *selected])
            canonical = canonical_image(actual, query, store)
            original = by_basis[canonical]
            transport = lean_transport(actual, query, store)
            index = register(actual, original, transport)
            cursor += 1
            return dict(source=index, prefix=prefix,
                        selected=Counter(q for i, q in enumerate(prefix) if mask >> i & 1))
        return dict(prefix=prefix, children=[read_node([*prefix, q], q)
                                            for q in range(maximum + 1)])

    original_tree = read_node([], len(sections) - 1)
    if cursor != len(records):
        raise ValueError('unconsumed trace')
    certificates = []

    def leaf(path, lower, upper, refs):
        coeff, rhs = [0] * len(sections), 0
        for ref in refs:
            kind = ref['type']
            if kind == 'occ':
                source = sources[ref['row']]
                vector = [int(c in span(source['basis'])) for c in sections]
                bound = target - source['lb']
            elif kind == 'total_ge':
                vector, bound = [-1] * len(sections), -target
            else:
                q = ref['label'] - 1
                sign = 1 if kind == 'branch_upper' else -1
                vector = [sign * int(j == q) for j in range(len(sections))]
                bound = sign * ref.get('bound', 0)
            coeff = [a + b for a, b in zip(coeff, vector)]
            rhs += bound
            ref['multiplier'] = 1
        if any(coeff) or rhs >= 0:
            raise ValueError('translated leaf fails exact Farkas arithmetic')
        certificates.append(dict(path=path, lower={str(k): v for k, v in lower.items()},
                                 upper={str(k): v for k, v in upper.items()},
                                 used_rows=refs, rhs=rhs))
        return dict(type='leaf', path=path)

    def convert(node, path):
        count = Counter(node['prefix'])
        if 'source' in node:
            index = node['source']
            members = span(sources[index]['basis'])
            lower = dict(node['selected'])
            refs = [dict(type='occ', row=index)]
            for q, code in enumerate(sections):
                if code in members:
                    refs.append(dict(type='branch_lower', label=q + 1, bound=lower[q])
                                if q in lower else dict(type='nonneg', label=q + 1))
            return leaf(path, lower, {}, refs)

        def choose(q, current_path):
            if q < 0:
                upper = {j: count[j] for j in range(len(sections))}
                refs = [dict(type='total_ge')] + [
                    dict(type='branch_upper', label=j + 1, bound=v) for j, v in upper.items()]
                return leaf(current_path, {}, upper, refs)
            return dict(type='branch', path=current_path, label=q + 1, floor=count[q],
                        left=choose(q - 1, current_path + 'L'),
                        right=convert(node['children'][q], current_path + 'R'))

        return choose(len(node['children']) - 1, path)

    tree = convert(original_tree, '')
    return metadata(), dict(basis=basis, branch=dict(tree=tree, certs=certificates)), dict(entries=ledger), transports


def emit_source_dispatch(emitter, meta, out, chunk_size=10):
    p, mod = emitter.names(meta)
    m = meta['n_occ']
    lines = [f'import {mod}Sources{i:02}' for i in range((m + chunk_size - 1) // chunk_size)]
    lines += ['namespace QiushiMatmul']
    for row in meta['source_rows']:
        i = row['idx']
        index = f'({i} : Fin {m})'
        lines += [f'theorem {p}Bound{i:04} :',
                  f'    QuotientRankAtLeast (spanCodes ({p}SourceBasis {index})) ({p}SourceLb {index}) := by',
                  f'  rw [show {p}SourceBasis {index} = {row["basis"]} from rfl,',
                  f'      show {p}SourceLb {index} = {row["lb"]} from rfl]',
                  f'  exact {p}Source{i:04}']
    lines += [f'theorem {p}SourceQRA (i : Fin {m}) :',
              f'    QuotientRankAtLeast (spanCodes ({p}SourceBasis i)) ({p}SourceLb i) :=',
              '  match i with']
    lines += [f'  | ⟨{i}, _⟩ => {p}Bound{i:04}' for i in range(m)]
    lines += [f'  | ⟨k + {m}, h⟩ => by omega', 'end QiushiMatmul', '']
    (out / (mod + 'Dispatch.lean')).write_text('\n'.join(lines))


def emit_tests(meta, destination):
    node, lower = meta['plane'], meta['target'] + 1
    prefix = f'plane{node}BtpGen'
    text = f'''import FrozenRegistry.Btp{node}Final
import QiushiFrozenWangData

open QiushiMatmul

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis {node}))
    (frozenWangTable.lower {node}) := by
  rw [show frozenWangTable.basis {node} = {meta['basis']} by decide +kernel,
      show frozenWangTable.lower {node} = {lower} by decide +kernel]
  exact {prefix}_lb{lower}

run_cmd do
  for name in #[``{prefix}_lb{lower}, ``{prefix}NoModel,
      ``{prefix}SourceQRA] do
    let axioms \u2190 Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {{ax}} in {{name}}"
    Lean.logInfo m!"BTP{node}_AXIOMS {{name}}: {{axioms}}"
  Lean.logInfo "BTP{node}_CHECKED"
#check {prefix}_lb{lower}
'''
    (destination / f'Btp{node}Tests.lean').write_text(text)


def emit(emitter, meta, cert, ledger, transports, staging, destination):
    if 'transports' not in inspect.signature(emitter.finish).parameters:
        raise ValueError('the certificate emitter must support supplied exact transports')
    staging.mkdir(parents=True, exist_ok=True)
    destination.mkdir(parents=True, exist_ok=True)
    _, mod = emitter.names(meta)
    leaf_name = re.compile(re.escape(mod) + r'(?:Leaf\d+|Leaves\d+)\.lean')
    for path in staging.glob(mod + 'Lea*.lean'):
        if leaf_name.fullmatch(path.name):
            path.unlink()
    emitter.emit_data(meta, staging)
    original_dispatch = emitter.emit_dispatch
    try:
        emitter.emit_dispatch = lambda data, out, chunk_size=10: emit_source_dispatch(
            emitter, data, out, chunk_size)
        emitter.finish(meta, cert, ledger, staging, transports=transports)
    finally:
        emitter.emit_dispatch = original_dispatch
    p, mod = emitter.names(meta)
    final = [f'import {mod}{suffix}' for suffix in ('Bool', 'Tree', 'Dispatch')]
    final += ['import FrozenRegistry.PaddedExtraction', 'namespace QiushiMatmul',
              f'theorem {p}_lb{meta["target"] + 1} :',
              f'    QuotientRankAtLeast (spanCodes {meta["basis"]}) {meta["target"] + 1} :=',
              f'  FrozenRegistry.padded_plane_qra {p}Config {p}Bool',
              f'    (by intro c hc; have h := {p}Bool.hDeadCover c hc',
              f'        have hd : forall d : Fin 1, {p}DeadBasis d = {meta["basis"]} := by decide +kernel',
              f'        simpa only [{p}Config, hd] using h)',
              f'    (0 : Fin {meta["n_live"]}) {p}SourceQRA {p}NoModel',
              'end QiushiMatmul', '']
    (staging / (mod + 'Final.lean')).write_text('\n'.join(final))
    # Batch independent leaves to avoid hundreds of compiler startups.
    leaf_files = sorted(path for path in staging.glob(mod + 'Leaf*.lean')
                        if re.fullmatch(re.escape(mod) + r'Leaf\d+\.lean', path.name))
    groups = []
    for start in range(0, len(leaf_files), 16):
        name = mod + f'Leaves{start // 16:03}'
        groups.append(name)
        lines = [f'import {mod}Data', 'set_option linter.unusedVariables false',
                 'set_option linter.unusedSimpArgs false']
        for path in leaf_files[start:start + 16]:
            lines += [line for line in path.read_text().splitlines() if not line.startswith('import ')]
        (staging / (name + '.lean')).write_text('\n'.join(lines) + '\n')
    tree_path = staging / (mod + 'Tree.lean')
    tree = [f'import {name}' for name in groups]
    tree += [line for line in tree_path.read_text().splitlines() if not line.startswith('import ')]
    tree_path.write_text('\n'.join(tree) + '\n')
    files = [path for path in staging.glob(mod + '*.lean') if path not in leaf_files]
    for path in files:
        text = re.sub(r'^import (' + re.escape(mod) + r'\w+)\s*$', r'import FrozenRegistry.\1',
                      path.read_text(), flags=re.M)
        (destination / path.name).write_text(text)
    written = {path.name for path in files}
    for path in destination.glob(mod + 'Leaves*.lean'):
        if leaf_name.fullmatch(path.name) and path.name not in written:
            path.unlink()
    return len(files)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, required=True)
    parser.add_argument('--certificate', type=Path, required=True)
    parser.add_argument('--registry', type=Path, required=True)
    parser.add_argument('--node', type=int, required=True)
    parser.add_argument('--leaf-limit', type=int, default=1000)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--emitter', type=Path)
    parser.add_argument('--emit-dir', type=Path)
    parser.add_argument('--emit-tests', action='store_true',
                        help='Emit exact frozen-type and transitive axiom guards')
    compression = parser.add_mutually_exclusive_group()
    compression.add_argument('--singleton-cover', action='store_true',
                             help='Use an exact sum of singleton occupation rows')
    compression.add_argument('--root-farkas', action='store_true',
                             help='Propose one root LP ray and check its exact integer arithmetic')
    args = parser.parse_args()
    if args.emit_tests and not args.emit_dir:
        parser.error('--emit-tests requires --emit-dir')
    data = args.archive.read_bytes()
    if len(data) != ARCHIVE_BYTES or hashlib.sha256(data).hexdigest() != ARCHIVE_SHA256:
        raise ValueError('wrong pinned archive')
    metadata = read_metadata(args.certificate)
    if metadata['certificate_sha256'] != CERTIFICATE_SHA256:
        raise ValueError('wrong pinned protobuf')
    if not 0 <= args.node < len(metadata['rows']):
        raise ValueError('node index out of range')
    registry = json.loads(args.registry.read_text())
    meta, cert, ledger, transports = translate(metadata['rows'][args.node],
        Archive(data).records(args.node, args.leaf_limit), metadata['rows'], registry,
        source_only=args.singleton_cover or args.root_farkas)
    translated_leaves = len(cert['branch']['certs']) if cert is not None else None
    if args.singleton_cover:
        cert = singleton_cover_certificate(meta)
        if cert is None:
            raise ValueError('the archived singleton rows do not supply a strict capacity contradiction')
    elif args.root_farkas:
        cert = root_farkas_certificate(meta)
        if cert is None:
            raise ValueError('no root Farkas contradiction found for the archived source rows')
    args.output.mkdir(parents=True, exist_ok=True)
    for name, value in [('tables', meta), ('branch', cert), ('sources', ledger),
                        ('transport-witnesses', transports)]:
        (args.output / (name + '.json')).write_text(json.dumps(value, indent=2) + '\n')
    result = dict(node=args.node, original_leaves=metadata['rows'][args.node]['proof_size'],
                  translated_leaves=translated_leaves, emitted_leaves=len(cert['branch']['certs']),
                  singleton_cover=args.singleton_cover, rows=meta['n_occ'],
                  root_farkas=args.root_farkas,
                  sources=sorted(int(k) for k in ledger['entries']))
    if args.emit_dir:
        if not args.emitter:
            parser.error('--emit-dir requires --emitter')
        spec = importlib.util.spec_from_file_location('btp_checked_emitter', args.emitter)
        emitter = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(emitter)
        result['modules'] = emit(emitter, meta, cert, ledger, transports,
                                 args.output / 'lean', args.emit_dir)
        if args.emit_tests:
            emit_tests(meta, args.emit_dir)
            result['test_module'] = f'FrozenRegistry.Btp{args.node}Tests'
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
