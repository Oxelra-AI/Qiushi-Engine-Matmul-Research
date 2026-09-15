"""Emit generator-checked span bounds from existing functional-kernel bounds."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from generate_certificate import rref, literal


def extract(log, module, output):
    rows = [json.loads(line.removeprefix('REGISTRY_CANDIDATE '))
            for line in log.read_text().splitlines() if line.startswith('REGISTRY_CANDIDATE ')]
    selected = {}
    for row in rows:
        if not row.get('kernels') or not row.get('kernel_space'):
            continue
        basis = rref(c for c in range(512) if all((c & k).bit_count() % 2 == 0 for k in row['kernels']))
        old = selected.get(basis)
        if old is None or (row['bound'], -len(row['theorem'])) > (old['bound'], -len(old['theorem'])):
            selected[basis] = row
    lines = ['import FrozenRegistry.Bridge', 'import FrozenRegistry.AdditionalSources', '',
             'set_option maxHeartbeats 16000000', 'set_option maxRecDepth 100000', '',
             'namespace QiushiMatmul.FrozenRegistry.Kernel', '']
    candidates = []
    for i, (basis, source) in enumerate(sorted(selected.items())):
        name = f'bound{i:03}'
        b, n, space = literal(basis), source['bound'], source['kernel_space']
        lines += [f'theorem {name} : QuotientRankAtLeast (spanCodes {b}) {n} := by',
                  f'  have h := {source["theorem"]}',
                  f'  change QuotientRankAtLeast ({space}) {n} at h',
                  f'  have hgen : ∀ c ∈ {b}, codeMat c ∈ ({space}) := by',
                  ('    simp only [Submodule.mem_inf, mem_kerEvalFunc]' if len(source['kernels']) > 1
                   else '    simp only [mem_kerEvalFunc]'), '    decide',
                  '  apply quotientRankAtLeast_mono ?_ h',
                  '  apply Submodule.span_le.mpr', '  rintro M ⟨c, hc, rfl⟩',
                  '  exact hgen c hc', '']
        candidates.append({'basis': list(basis), 'bound': n, 'module': 'FrozenRegistry.KernelBindings',
                           'theorem': 'QiushiMatmul.FrozenRegistry.Kernel.' + name, 'source': source})
    lines += ['end QiushiMatmul.FrozenRegistry.Kernel', '', 'run_cmd do',
              '  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]',
              '  for name in #[' + ', '.join('``' + c['theorem'] for c in candidates) + '] do',
              '    let axioms ← Lean.collectAxioms name',
              '    for ax in axioms do', '      unless allowed.contains ax do',
              '        throwError "Unexpected axiom {ax} in {name}"',
              '    Lean.logInfo m!"KERNEL_BOUND_AXIOMS {name}: {axioms}"',
              f'  Lean.logInfo "KERNEL_BOUND_CHECKED {len(candidates)}"', '']
    module.write_text('\n'.join(lines))
    output.write_text(json.dumps(candidates, indent=2) + '\n')
    print('Emitted kernel span adapters:', len(candidates), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log', type=Path, required=True)
    parser.add_argument('--module', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    extract(args.log, args.module, args.output)
