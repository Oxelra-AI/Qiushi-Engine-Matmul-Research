import QiushiFrozenLabelKeysData
namespace QiushiMatmul.FrozenLabel
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
theorem signature_keys_01a3 (i : Fin 2) :
    refinedSignature (frozenWangBasis ⟨14 + i.val, by omega⟩) =
      signatureFixture ⟨14 + i.val, by omega⟩ := by
  fin_cases i <;> decide +kernel
end QiushiMatmul.FrozenLabel
