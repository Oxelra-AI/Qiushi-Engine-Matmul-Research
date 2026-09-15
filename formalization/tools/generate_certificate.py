"""Emit checked source transports and an exact Farkas branch proof.

Inputs are explicit numeric tables and certificates. Orbit labels only select
candidate source theorems; emitted Lean checks the actual subspace transport.
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path
import numpy as np


def rref(basis):
    out = [0] * 9
    for v in basis:
        v = int(v)
        for i in range(8, -1, -1):
            if v >> i & 1 and out[i]:
                v ^= out[i]
        if v:
            i = v.bit_length() - 1
            out[i] = v
            for j in range(i + 1, 9):
                if out[j] >> i & 1:
                    out[j] ^= v
    return tuple(v for v in reversed(out) if v)


def span(basis):
    out = {0}
    for c in basis:
        out |= {x ^ c for x in tuple(out)}
    return out


def actions():
    matrices = ((np.arange(512)[:, None] >> np.arange(9)) & 1).reshape(512, 3, 3)
    gl = [c for c in range(512) if len(rref([sum(int(matrices[c, i, j]) << j for j in range(3)) for i in range(3)])) == 3]
    assert len(gl) == 168
    prod = np.matmul(matrices[gl, None], matrices[gl]) % 2
    inv = np.all(prod == np.eye(3), axis=(2, 3)).argmax(axis=1)
    assert np.all(prod[np.arange(168), inv] == np.eye(3))
    codes = np.array(gl)
    ps = np.repeat(codes, 168)
    qs = np.tile(codes, 168)
    qis = np.tile(codes[inv], 168)
    # Build the linear action from the images of the nine matrix units.
    units = matrices[1 << np.arange(9)]
    imgs = np.matmul(np.matmul(matrices[ps].transpose(0, 2, 1)[:, None], units),
                     matrices[qis].transpose(0, 2, 1)[:, None]) % 2
    images = (imgs.reshape(-1, 9, 9) * (1 << np.arange(9))).sum(axis=2).astype(np.uint16)
    table = np.zeros((len(ps), 512), dtype=np.uint16)
    for c in range(1, 512):
        bit = (c & -c).bit_length() - 1
        table[:, c] = table[:, c ^ (1 << bit)] ^ images[:, bit]
    trans = (matrices.transpose(0, 2, 1).reshape(512, 9) * (1 << np.arange(9))).sum(axis=1)
    return ps, qs, qis, table, trans


def find_transports(rows, entries):
    ps, qs, qis, table, trans = actions()
    answers = {}
    grouped = defaultdict(list)
    for row in rows:
        grouped[row['orbit']].append(row)
    for orbit, group in sorted(grouped.items()):
        entry = entries[orbit]
        basis = entry['basis_codes']
        pending = {rref(row['basis']) for row in group}
        found = {}
        for flip in (False, True):
            action = table[:, trans] if flip else table
            for idx, images in enumerate(action[:, basis]):
                key = rref(images)
                if key not in pending:
                    continue
                found[key] = (idx, flip)
                pending.remove(key)
                if not pending:
                    break
            if not pending:
                break
        if pending:
            raise ValueError(f'Unmatched actual spaces for orbit {orbit}: {pending}')
        for row in group:
            idx, flip = found[rref(row['basis'])]
            action = table[idx, trans] if flip else table[idx]
            inverse = np.argsort(action)
            pre = [int(inverse[c]) for c in row['basis']]
            assert all(c in span(basis) for c in pre)
            answers[row['idx']] = {'P': int(ps[idx]), 'Q': int(qs[idx]),
                                   'Qinv': int(qis[idx]), 'flip': flip,
                                   'pairs': list(zip(row['basis'], pre))}
        print(f'Orbit {orbit}: {len(group)} actual-space witnesses', flush=True)
    return answers


def literal(xs):
    return '[' + ', '.join(map(str, xs)) + ']'


def names(meta):
    tag = meta.get('name_tag', '')
    if tag and (not tag.isascii() or not tag.isalpha()):
        raise ValueError('The module tag must contain ASCII letters only')
    module = meta.get('module_prefix', f'QiushiPlane{meta["plane"]}{tag}Gen')
    if not module or not module.isascii() or not module.isalnum() or not module[0].isalpha():
        raise ValueError('The module prefix must be an ASCII identifier')
    return f'plane{meta["plane"]}{tag}Gen', module


def emit_data(meta, out):
    """Bound the depth of finite lookup terms independently of table size."""
    p, mod = names(meta)
    n, m, nd = meta['n_live'], meta['n_occ'], meta['n_dead']
    if n < 0 or min(m, nd) <= 0:
        raise ValueError('The extraction requires source and dead-witness tables')
    basis = rref(meta['basis'])
    free = sorted(set(range(9)) - {v.bit_length() - 1 for v in basis})
    live = meta['live_list']
    sections = [sum(((q + 1) >> j & 1) << bit for j, bit in enumerate(free)) for q in live]
    live_index = {q: j + 1 for j, q in enumerate(live)}
    classify, cover = [], []
    for c in range(512):
        reduced = c
        for b in basis:
            if reduced >> (b.bit_length() - 1) & 1:
                reduced ^= b
        q = sum((reduced >> bit & 1) << j for j, bit in enumerate(free)) - 1
        classify.append(live_index.get(q, 0))
        witnesses = [i for i, w in enumerate(meta['dead_witnesses']) if c in span(w['basis'])]
        if classify[-1] == 0 and not witnesses:
            raise ValueError(f'Uncovered zero/dead label: {c}')
        cover.append(witnesses[0] if witnesses else 0)
    lines = ['import QiushiGenericPlaneExtraction', '',
             'set_option maxHeartbeats 8000000', 'set_option maxRecDepth 100000',
             'namespace QiushiMatmul', '']

    def table(name, count, typ, values):
        if count == 0:
            lines.extend([f'def {p}{name} (i : Fin 0) : {typ} := Fin.elim0 i', ''])
            return
        lines.extend([f'def {p}{name} (i : Fin {count}) : {typ} :=',
                      '  match i.val / 32 with'])
        for start in range(0, count, 32):
            lines.extend([f'  | {start // 32} =>', '    match i.val % 32 with'])
            for j, v in enumerate(values[start:start + 32]):
                lines.append(f'    | {j} => {v}')
            lines.append(f'    | _ => {values[start]}')
        lines.extend([f'  | _ => {values[0]}', ''])

    table('Classify', 512, f'Fin {n + 1}', [f'⟨{v}, by decide⟩' for v in classify])
    table('Section', n, 'Fin 512', [f'⟨{v}, by decide⟩' for v in sections])
    table('DeadBasis', nd, 'List Nat', [literal(w['basis']) for w in meta['dead_witnesses']])
    table('DeadCover', 512, f'Fin {nd}', [f'⟨{v}, by decide⟩' for v in cover])
    table('SourceBasis', m, 'List Nat', [literal(r['basis']) for r in meta['source_rows']])
    table('SourceLb', m, 'Nat', [str(r['lb']) for r in meta['source_rows']])
    masks = [sum((1 << j) for j, c in enumerate(sections) if c in span(r['basis']))
             for r in meta['source_rows']]
    table('RowMask', m, 'Nat', list(map(str, masks)))
    lines += [f'def {p}OccCoeff (i : Fin {m}) (j : Fin {n}) : Int :=',
              f'  if ({p}RowMask i).testBit j.val then 1 else 0', '',
              f'def {p}OccRhs (i : Fin {m}) : Int := {meta["target"]} - ({p}SourceLb i : Int)', '',
              f'def {p}OccSys : OccSys {n} {m} where',
              f'  occCoeff := {p}OccCoeff', f'  occRhs := {p}OccRhs',
              f'  target := {meta["target"]}', '', f'def {p}Config : PlaneExtConfig where',
              f'  nOcc := {m}', f'  nDead := {nd}', f'  nLive := {n}',
              f'  target := {meta["target"]}', f'  planeBasis := {literal(meta["basis"])}',
              f'  sourceBasis := {p}SourceBasis', f'  sourceLb := {p}SourceLb',
              f'  deadBasis := {p}DeadBasis', f'  classifyCode := {p}Classify',
              f'  sectionCode := {p}Section', f'  deadCover := {p}DeadCover',
              f'  occSys := {p}OccSys', '', 'end QiushiMatmul', '']
    (out / (mod + 'Data.lean')).write_text('\n'.join(lines))
    emit_checks(meta, out)


def emit_checks(meta, out, width=32):
    """Split kernel computations, with a proved exhaustive assembly of blocks."""
    if width < 1:
        raise ValueError('Block width must be positive')
    p, mod = names(meta)
    cfg = p + 'Config'
    n, m, nd = meta['n_live'], meta['n_occ'], meta['n_dead']
    fields = [
        ('Section', 'hSectionCoset', 512,
         f'forall j : Fin {n}, ({cfg}.classifyCode i).val = j.val + 1 -> '
         f'spanContainsCode {cfg}.planeBasis (i.val ^^^ ({cfg}.sectionCode j).val) = true'),
        ('Dead', 'hDeadCover', 512,
         f'({cfg}.classifyCode i).val = 0 -> '
         f'spanContainsCode ({cfg}.deadBasis ({cfg}.deadCover i)) i.val = true'),
        ('Source', 'hPlaneLeSource', m,
         f'forall g : Nat, g \u2208 {cfg}.planeBasis -> '
         f'spanContainsCode ({cfg}.sourceBasis i) g = true'),
        ('DeadSource', 'hPlaneLeDead', nd,
         f'forall g : Nat, g \u2208 {cfg}.planeBasis -> '
         f'spanContainsCode ({cfg}.deadBasis i) g = true'),
        ('Indicator', 'hIndicator', m,
         f'forall j : Fin {n}, {cfg}.occSys.occCoeff i j = '
         f'if spanContainsCode ({cfg}.sourceBasis i) ({cfg}.sectionCode j).val then 1 else 0'),
    ]
    header = ['set_option maxHeartbeats 80000000', 'set_option maxRecDepth 100000',
              'set_option synthInstance.maxSize 512',
              'namespace QiushiMatmul']
    props = [f'import {mod}Data', 'import QiushiFiniteBlocks', *header]
    for key, _, count, predicate in fields:
        props += [f'abbrev {p}{key}Property (i : Fin {count}) : Prop :=', '  ' + predicate]
    props += ['end QiushiMatmul', '']
    (out / (mod + 'CheckProperties.lean')).write_text('\n'.join(props))
    for key, _, count, _ in fields:
        blocks = (count + width - 1) // width
        prop = f'{p}{key}Property'
        for block in range(blocks):
            theorem = f'{p}{key}Block{block}'
            lines = [f'import {mod}CheckProperties', *header,
                     f'theorem {theorem} : forall offset : Fin {width},',
                     f'    forall hlt : {block} * {width} + offset.val < {count},',
                     f'    {prop} (Fin.mk ({block} * {width} + offset.val) hlt) := by',
                     f'  simp only [{prop}, {cfg}, {p}OccSys]',
                     '  decide +kernel', 'end QiushiMatmul', '']
            (out / f'{mod}{key}Block{block}.lean').write_text('\n'.join(lines))
        lines = [f'import {mod}{key}Block{block}' for block in range(blocks)]
        lines += [*header, f'theorem {p}{key}All : forall i, {prop} i := by',
                  f'  apply forall_fin_of_blocks (blocks := {blocks}) (width := {width})',
                  '    (by decide) (by decide)', '  intro block', '  match block with']
        for block in range(blocks):
            lines.append(f'  | \u27e8{block}, _\u27e9 => exact {p}{key}Block{block}')
        lines += [f'  | \u27e8k + {blocks}, h\u27e9 => omega', 'end QiushiMatmul', '']
        (out / f'{mod}{key}All.lean').write_text('\n'.join(lines))
    lines = [f'import {mod}{key}All' for key, _, _, _ in fields]
    lines += [*header, f'theorem {p}Bool : PlaneExtBool {cfg} where']
    lines += [f'  {field} := {p}{key}All' for key, field, _, _ in fields]
    lines += ['  hRhs := by intro i; rfl', '  hTarget := rfl', 'end QiushiMatmul', '']
    (out / (mod + 'Bool.lean')).write_text('\n'.join(lines))


def emit_dispatch(meta, out, chunk_size=10):
    """Bind actual-space proofs to table entries using checked value equalities."""
    p, mod = names(meta)
    m, nd = meta['n_occ'], meta['n_dead']
    rows = sorted(meta['source_rows'], key=lambda row: row['idx'])
    if [row['idx'] for row in rows] != list(range(m)):
        raise ValueError('Missing or duplicate source indices')
    modules = []
    for start in range(0, m, chunk_size):
        module = f'{mod}Bindings{start // chunk_size:02d}'
        modules.append(module)
        lines = [f'import {mod}Sources{start // chunk_size:02d}',
                 'set_option maxHeartbeats 8000000', 'set_option maxRecDepth 100000',
                 'namespace QiushiMatmul']
        for row in rows[start:start + chunk_size]:
            i, basis, lb = row['idx'], literal(row['basis']), row['lb']
            index = f'({i} : Fin {m})'
            lines += [f'theorem {p}Bound{i:04d} :',
                      f'    QuotientRankAtLeast (spanCodes ({p}SourceBasis {index})) ({p}SourceLb {index}) := by',
                      f'  rw [show {p}SourceBasis {index} = {basis} from rfl,',
                      f'      show {p}SourceLb {index} = {lb} from rfl]',
                      f'  exact {p}Source{i:04d}']
        lines += ['end QiushiMatmul', '']
        (out / f'{module}.lean').write_text('\n'.join(lines))
    lines = [f'import {module}' for module in modules]
    lines += ['set_option maxHeartbeats 8000000', 'set_option maxRecDepth 100000',
              'namespace QiushiMatmul', f'theorem {p}SourceQRA (i : Fin {m}) :',
              f'    QuotientRankAtLeast (spanCodes ({p}SourceBasis i)) ({p}SourceLb i) :=',
              '  match i with']
    lines += [f'  | \u27e8{i}, _\u27e9 => {p}Bound{i:04d}' for i in range(m)]
    lines += [f'  | \u27e8k + {m}, h\u27e9 => by omega']
    if len(meta['dead_witnesses']) != nd:
        raise ValueError('Missing dead witnesses')
    for idx, dw in enumerate(meta['dead_witnesses']):
        witness = dw['witness_source_idx']
        if rows[witness]['basis'] != dw['basis']:
            raise ValueError('Dead witness and source basis disagree')
        lines += [f'theorem {p}DeadBound{idx:04d} :',
                  f'    QuotientRankAtLeast (spanCodes ({p}DeadBasis ({idx} : Fin {nd}))) {meta["target"]} := by',
                  f'  rw [show {p}DeadBasis ({idx} : Fin {nd}) = {literal(dw["basis"])} from rfl]',
                  f'  exact quotientRankAtLeast_weaken {p}Source{witness:04d} (by decide)']
    lines += [f'theorem {p}DeadQRA (d : Fin {nd}) :',
              f'    QuotientRankAtLeast (spanCodes ({p}DeadBasis d)) {meta["target"]} :=',
              '  match d with']
    lines += [f'  | \u27e8{idx}, _\u27e9 => {p}DeadBound{idx:04d}' for idx in range(nd)]
    lines += [f'  | \u27e8k + {nd}, h\u27e9 => by omega', 'end QiushiMatmul', '']
    (out / (mod + 'Dispatch.lean')).write_text('\n'.join(lines))


def finish(meta, cert, ledger, out, *, transports=None):
    plane = meta['plane']
    p, mod = names(meta)
    n, m = meta['n_live'], meta['n_occ']
    rows = meta['source_rows']
    entries = {}
    for row in rows:
        candidates = [v for v in ledger['entries'].values()
                      if v['orbit'] == row['orbit'] and v['lb'] >= row['lb']
                      and v.get('module') and v.get('basis_codes')
                      and not set(v.get('observed_axioms', [])) - {'propext', 'Classical.choice', 'Quot.sound'}]
        if not candidates:
            raise ValueError(f'No explicit source theorem for {row}')
        entries[row['orbit']] = max(candidates, key=lambda e: e['lb'])
    witnesses = find_transports(rows, entries) if transports is None else transports
    if set(witnesses) != {row['idx'] for row in rows}:
        raise ValueError('Missing or unexpected supplied transport indices')
    (out / 'transport-witnesses.json').write_text(json.dumps(witnesses, indent=2) + '\n')
    modules = sorted({e['module'] for e in entries.values()})
    (out / 'source-modules.json').write_text(json.dumps(modules, indent=2) + '\n')
    chunk_size = 10
    row_modules = []
    for start in range(0, m, chunk_size):
        name = mod + f'Sources{start // chunk_size:02d}'
        row_modules.append(name)
        lines = [f'import {mod}Data', 'import QiushiCertifiedTransport']
        chunk_modules = sorted({entries[row['orbit']]['module']
                                for row in rows[start:start + chunk_size]})
        lines += [f'import {s}' for s in chunk_modules]
        lines += ['set_option maxHeartbeats 8000000', 'set_option maxRecDepth 10000', 'namespace QiushiMatmul', '']
        for row in rows[start:start + chunk_size]:
            i = row['idx']
            e = entries[row['orbit']]
            w = witnesses[i]
            pairs = '[' + ', '.join(f'({a}, {b})' for a, b in w['pairs']) + ']'
            lines += [f'theorem {p}Source{i:04d} :',
                      f'    QuotientRankAtLeast (spanCodes {literal(row["basis"])}) {row["lb"]} := by',
                      '  apply quotientRankAtLeast_weaken (n := ' + str(e['lb']) + ') _ (by decide)',
                      '  exact quotientRankAtLeast_of_code_transport',
                      f'    {literal(e["basis_codes"])} {pairs}',
                      f'    (codeMat {w["P"]}) (codeMat {w["Q"]}) (codeMat {w["Qinv"]}) {str(w["flip"]).lower()}',
                      '    (by decide) (by decide) (by decide) (by decide)',
                      f'    {e["theorem"]}', '']
        lines += ['end QiushiMatmul', '']
        (out / (name + '.lean')).write_text('\n'.join(lines))
    emit_dispatch(meta, out, chunk_size)

    # Replay the exact nonnegative Farkas multipliers, not an unbounded solver.
    live_index = {q: i for i, q in enumerate(meta['live_list'])}
    source_index = {r['orig']: r['idx'] for r in rows}
    paths = {}
    for leaf_idx, leaf in enumerate(cert['branch']['certs']):
        lname = p + f'Leaf{leaf_idx:04d}'
        paths[leaf['path']] = (leaf_idx, leaf)
        lower = [(live_index[int(v)], int(b)) for v, b in leaf['lower'].items()]
        upper = [(live_index[int(v)], int(b)) for v, b in leaf['upper'].items()]
        refs, mults, row_proofs = [], [], []
        for u in leaf['used_rows']:
            typ = u['type']
            k = int(u['multiplier'])
            if k < 0:
                raise ValueError('Negative Farkas multiplier')
            mults.append(k)
            if typ == 'occ':
                ri = source_index[int(u['row'])]
                refs.append(f'.occ {ri}')
                row_proofs.append(f'exact hroot.hOcc {ri}')
            elif typ == 'total_ge':
                refs.append('.sumGe')
                row_proofs.append(f'change (∑ j, (-1 : Int) * x j) ≤ -{p}OccSys.target; '
                                  'simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal')
            elif typ == 'total_le':
                raise ValueError('RootHolds provides a lower total bound only')
            else:
                j = live_index[int(u['label']) - 1]
                if typ == 'nonneg':
                    refs.append(f'.nonneg {j}')
                    row_proofs.append(f'change (∑ k, (if k = ({j} : Fin {n}) then (-1 : Int) else 0) * x k) ≤ 0; '
                                      f'simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg {j}')
                elif typ == 'branch_upper':
                    b = int(u['bound'])
                    if (j, b) not in upper:
                        raise ValueError('Missing upper branch assumption')
                    refs.append(f'.branchLe {j} ({b})')
                    row_proofs.append(f'change (∑ k, (if k = ({j} : Fin {n}) then (1 : Int) else 0) * x k) ≤ ({b} : Int); '
                                      f'simpa only [indicator_sum, one_mul] using hUB_{j}')
                elif typ == 'branch_lower':
                    b = int(u['bound'])
                    if (j, b) not in lower:
                        raise ValueError('Missing lower branch assumption')
                    refs.append(f'.branchGe {j} ({b})')
                    row_proofs.append(f'change (∑ k, (if k = ({j} : Fin {n}) then (-1 : Int) else 0) * x k) ≤ -({b} : Int); '
                                      f'simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_{j}')
                else:
                    raise ValueError(typ)
        count = len(refs)
        lines = [f'import {mod}Data', 'set_option maxHeartbeats 8000000',
                 'set_option maxRecDepth 10000', 'namespace QiushiMatmul', '']
        for suffix, typ, values in [('Refs', f'RowRef {m} {n}', refs), ('Mult', 'Nat', mults)]:
            lines += [f'def {lname}{suffix} : Fin {count} → {typ} := ![{", ".join(map(str, values))}]', '']
        lines += [f'theorem {lname} (x : Fin {n} → Int)', f'    (hroot : {p}OccSys.RootHolds x)']
        lines += [f'    (hLB_{j} : ({b} : Int) ≤ x {j})' for j, b in lower]
        lines += [f'    (hUB_{j} : x {j} ≤ ({b} : Int))' for j, b in upper]
        lines += ['    : False := by',
                  f'  apply farkas_leaf_unsat (fun i j => ({lname}Refs i).resolveCoeff {p}OccSys j)',
                  f'    (fun i => ({lname}Refs i).resolveRhs {p}OccSys) {lname}Mult',
                  '    (by decide) (by decide) x',
                  f'  intro i; fin_cases i <;> simp only [{lname}Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,',
                  '    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]']
        lines += ['  · ' + proof for proof in row_proofs]
        lines += ['', 'end QiushiMatmul', '']
        (out / (mod + f'Leaf{leaf_idx:04d}.lean')).write_text('\n'.join(lines))
    lines = [f'import {mod}Leaf{i:04d}' for i in range(len(paths))]
    lines += ['set_option maxHeartbeats 8000000', 'namespace QiushiMatmul', '',
              f'theorem {p}NoModel (x : Fin {n} → Int) (hroot : {p}OccSys.RootHolds x) : False := by']
    visited = set()
    def tree(node, indent, ancestors):
        if node['type'] == 'leaf':
            i, leaf = paths[node['path']]
            visited.add(node['path'])
            count = len(leaf['lower']) + len(leaf['upper'])
            lines.append(indent + f'exact {p}Leaf{i:04d} x hroot' + ' (by omega)' * count)
        elif node['type'] == 'branch':
            j = live_index[int(node['label']) - 1]
            floor = int(node['floor'])
            hname = 'hbranch_' + (node['path'] or 'root')
            lines.append(indent + f'by_cases {hname} : x {j} ≤ ({floor} : Int)')
            lines.append(indent + '·')
            tree(node['left'], indent + '  ', ancestors + [(j, floor, True)])
            lines.append(indent + '·')
            tree(node['right'], indent + '  ', ancestors + [(j, floor, False)])
        else:
            raise ValueError('Unclosed branch')
    tree(cert['branch']['tree'], '  ', [])
    if visited != set(paths):
        raise ValueError('Unused or missing leaves')
    lines += ['', 'end QiushiMatmul', '']
    (out / (mod + 'Tree.lean')).write_text('\n'.join(lines))
    final = [f'import {mod}{s}' for s in ('Bool', 'Tree', 'Dispatch')]
    final += ['namespace QiushiMatmul', '',
              f'theorem {p}_lb{meta["target"] + 1} :',
              f'    QuotientRankAtLeast (spanCodes {literal(cert["basis"])}) {meta["target"] + 1} :=',
              f'  generic_plane_qra {p}Config {p}Bool {p}SourceQRA {p}DeadQRA',
              f'    (by decide) {p}NoModel', '', 'end QiushiMatmul', '']
    (out / (mod + 'Final.lean')).write_text('\n'.join(final))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--metadata', type=Path, required=True)
    parser.add_argument('--certificate', type=Path, required=True)
    parser.add_argument('--ledger', type=Path, required=True)
    parser.add_argument('--out-dir', type=Path, required=True)
    parser.add_argument('--data', action='store_true', help='Also regenerate finite tables and their Lean checks')
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    metadata = json.loads(args.metadata.read_text())
    if args.data:
        emit_data(metadata, args.out_dir)
    finish(metadata, json.loads(args.certificate.read_text()),
           json.loads(args.ledger.read_text()), args.out_dir)
