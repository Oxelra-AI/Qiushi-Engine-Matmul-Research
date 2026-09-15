import QiushiFrozenLabelKeysData

namespace QiushiMatmul.FrozenLabel
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem signature_keys_11 (i : Fin 8) :
    refinedSignature (frozenWangBasis ⟨88 + i.val, by omega⟩) =
      signatureFixture ⟨88 + i.val, by omega⟩ := by
  fin_cases i <;> decide +kernel

end QiushiMatmul.FrozenLabel
