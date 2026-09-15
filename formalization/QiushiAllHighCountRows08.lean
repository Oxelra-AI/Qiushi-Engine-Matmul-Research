import QiushiAllHighCountData

namespace QiushiMatmul.AllHighCount
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem rowCount_block08 (i : Fin 16) :
    rowCount ⟨8 * 16 + i.val, by omega⟩ =
      expectedRowCounts[(⟨8 * 16 + i.val, by omega⟩ : Fin 512)] := by
  fin_cases i <;> decide +kernel

end QiushiMatmul.AllHighCount
