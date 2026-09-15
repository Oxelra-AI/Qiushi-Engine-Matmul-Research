"""Emit finite fixtures and kernel proofs; Python results carry no proof authority."""

import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, required=True)
BASE = parser.parse_args().output.resolve()
BASE.mkdir(parents=True, exist_ok=True)
OUT = BASE


def rank(code):
    rows = [(code >> (3 * i)) & 7 for i in range(3)]
    pivot = 0
    for bit in range(3):
        found = next((j for j in range(pivot, 3) if rows[j] & (1 << bit)), None)
        if found is None:
            continue
        rows[pivot], rows[found] = rows[found], rows[pivot]
        for j in range(3):
            if j != pivot and rows[j] & (1 << bit):
                rows[j] ^= rows[pivot]
        pivot += 1
    return pivot


high = [rank(a) >= 2 for a in range(512)]
counts = [sum(high[a] and high[b] and high[a ^ b] for b in range(512))
          for a in range(512)]
assert sum(counts) == 192108


def vector(values):
    return ',\n  '.join(', '.join(values[i:i + 16]) for i in range(0, len(values), 16))


data = '''import QiushiHuaCoset

namespace QiushiMatmul.AllHighCount
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Packed finite rank lookup; agreement with rankCode is checked below. -/
def highCodeMask : Nat := HIGH_MASK

def highCode (c : Fin 512) : Bool := highCodeMask.testBit c.val

theorem highCode_correct : ∀ c : Fin 512,
    highCode c = decide (2 ≤ rankCode c.val) := by
  decide +kernel +revert

def xorCode (a b : Fin 512) : Fin 512 :=
  ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 9) a.isLt b.isLt⟩

def fastEligible (a b : Fin 512) : Bool :=
  highCode a && highCode b && highCode (xorCode a b)

def rowCount (a : Fin 512) : Nat :=
  (List.finRange 512).countP (fastEligible a)

def expectedRowCounts : Vector Nat 512 := ⟨#[
  COUNT_VALUES
], by decide⟩

theorem expected_row_sum :
    ((List.finRange 512).map (fun a => expectedRowCounts[a])).sum = 192108 := by
  decide

end QiushiMatmul.AllHighCount
'''.replace('HIGH_MASK', str(sum(1 << a for a in range(512) if high[a]))).replace(
    'COUNT_VALUES', vector(list(map(str, counts))))
(BASE / 'QiushiAllHighCountData.lean').write_text(data)
modules = ['QiushiAllHighCountData']
for block in range(32):
    name = f'QiushiAllHighCountRows{block:02d}'
    code = f'''import QiushiAllHighCountData

namespace QiushiMatmul.AllHighCount
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem rowCount_block{block:02d} (i : Fin 16) :
    rowCount ⟨{block} * 16 + i.val, by omega⟩ =
      expectedRowCounts[(⟨{block} * 16 + i.val, by omega⟩ : Fin 512)] := by
  fin_cases i <;> decide +kernel

end QiushiMatmul.AllHighCount
'''
    (BASE / (name + '.lean')).write_text(code)
    modules.append(name)

code = '\n'.join('import ' + name for name in modules[1:]) + '''

namespace QiushiMatmul.AllHighCount
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem rowCount_correct (a : Fin 512) : rowCount a = expectedRowCounts[a] := by
  have hrows : ∀ (q : Fin 32) (r : Fin 16),
      rowCount ⟨q.val * 16 + r.val, by omega⟩ =
        expectedRowCounts[(⟨q.val * 16 + r.val, by omega⟩ : Fin 512)] := by
    intro q r
    fin_cases q
CASES
  have h := hrows ⟨a.val / 16, by omega⟩ ⟨a.val % 16, by omega⟩
  have heq : (⟨a.val / 16 * 16 + a.val % 16, by omega⟩ : Fin 512) = a := by
    apply Fin.ext
    dsimp
    omega
  simpa only [heq] using h

theorem eligible_row_total : ((List.finRange 512).map rowCount).sum = 192108 := by
  rw [show rowCount = (fun a => expectedRowCounts[a]) from funext rowCount_correct]
  exact expected_row_sum

end QiushiMatmul.AllHighCount
'''.replace('CASES', '\n'.join(f'    · exact rowCount_block{i:02d} r' for i in range(32)))
(BASE / 'QiushiAllHighCountRows.lean').write_text(code)
modules.append('QiushiAllHighCountRows')
(OUT / 'generated-fixtures.json').write_text(json.dumps({
    'status': 'untrusted_until_lean_checked', 'modules': modules,
    'first_codes': 512, 'second_codes_per_row': 512,
    'shards': 32, 'rows_per_shard': 16, 'expected_total': sum(counts),
    'rank_histogram': {k: sum(rank(a) == k for a in range(512)) for k in range(4)},
    'row_count_histogram': {k: counts.count(k) for k in sorted(set(counts))},
}, indent=2) + '\n')
print(json.dumps({'modules': len(modules), 'row_count_histogram': {
    k: counts.count(k) for k in sorted(set(counts))}}))
