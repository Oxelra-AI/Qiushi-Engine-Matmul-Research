import QiushiAllHighCountRows00
import QiushiAllHighCountRows01
import QiushiAllHighCountRows02
import QiushiAllHighCountRows03
import QiushiAllHighCountRows04
import QiushiAllHighCountRows05
import QiushiAllHighCountRows06
import QiushiAllHighCountRows07
import QiushiAllHighCountRows08
import QiushiAllHighCountRows09
import QiushiAllHighCountRows10
import QiushiAllHighCountRows11
import QiushiAllHighCountRows12
import QiushiAllHighCountRows13
import QiushiAllHighCountRows14
import QiushiAllHighCountRows15
import QiushiAllHighCountRows16
import QiushiAllHighCountRows17
import QiushiAllHighCountRows18
import QiushiAllHighCountRows19
import QiushiAllHighCountRows20
import QiushiAllHighCountRows21
import QiushiAllHighCountRows22
import QiushiAllHighCountRows23
import QiushiAllHighCountRows24
import QiushiAllHighCountRows25
import QiushiAllHighCountRows26
import QiushiAllHighCountRows27
import QiushiAllHighCountRows28
import QiushiAllHighCountRows29
import QiushiAllHighCountRows30
import QiushiAllHighCountRows31

namespace QiushiMatmul.AllHighCount
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem rowCount_correct (a : Fin 512) : rowCount a = expectedRowCounts[a] := by
  have hrows : ∀ (q : Fin 32) (r : Fin 16),
      rowCount ⟨q.val * 16 + r.val, by omega⟩ =
        expectedRowCounts[(⟨q.val * 16 + r.val, by omega⟩ : Fin 512)] := by
    intro q r
    fin_cases q
    · exact rowCount_block00 r
    · exact rowCount_block01 r
    · exact rowCount_block02 r
    · exact rowCount_block03 r
    · exact rowCount_block04 r
    · exact rowCount_block05 r
    · exact rowCount_block06 r
    · exact rowCount_block07 r
    · exact rowCount_block08 r
    · exact rowCount_block09 r
    · exact rowCount_block10 r
    · exact rowCount_block11 r
    · exact rowCount_block12 r
    · exact rowCount_block13 r
    · exact rowCount_block14 r
    · exact rowCount_block15 r
    · exact rowCount_block16 r
    · exact rowCount_block17 r
    · exact rowCount_block18 r
    · exact rowCount_block19 r
    · exact rowCount_block20 r
    · exact rowCount_block21 r
    · exact rowCount_block22 r
    · exact rowCount_block23 r
    · exact rowCount_block24 r
    · exact rowCount_block25 r
    · exact rowCount_block26 r
    · exact rowCount_block27 r
    · exact rowCount_block28 r
    · exact rowCount_block29 r
    · exact rowCount_block30 r
    · exact rowCount_block31 r
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
