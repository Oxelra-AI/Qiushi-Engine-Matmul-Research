import QiushiFrozenLabelKeysData

namespace QiushiMatmul.FrozenLabel
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem signature_keys_16 (i : Fin 16) :
    refinedSignature (frozenWangBasis ⟨128 + i.val, by omega⟩) =
      signatureFixture ⟨128 + i.val, by omega⟩ := by
  fin_cases i <;> decide +kernel

end QiushiMatmul.FrozenLabel
