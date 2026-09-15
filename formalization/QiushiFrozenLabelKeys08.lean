import QiushiFrozenLabelKeysData

namespace QiushiMatmul.FrozenLabel
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem signature_keys_08 (i : Fin 8) :
    refinedSignature (frozenWangBasis ⟨64 + i.val, by omega⟩) =
      signatureFixture ⟨64 + i.val, by omega⟩ := by
  fin_cases i <;> decide +kernel

end QiushiMatmul.FrozenLabel
