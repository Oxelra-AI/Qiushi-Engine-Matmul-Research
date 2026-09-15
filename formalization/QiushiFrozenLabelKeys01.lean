import QiushiFrozenLabelKeys01A0
import QiushiFrozenLabelKeys01A1
import QiushiFrozenLabelKeys01A2
import QiushiFrozenLabelKeys01A3

namespace QiushiMatmul.FrozenLabel
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem signature_keys_01 (i : Fin 8) :
    refinedSignature (frozenWangBasis ⟨8 + i.val, by omega⟩) =
      signatureFixture ⟨8 + i.val, by omega⟩ := by
  fin_cases i
  · exact signature_keys_01a0 0
  · exact signature_keys_01a0 1
  · exact signature_keys_01a1 0
  · exact signature_keys_01a1 1
  · exact signature_keys_01a2 0
  · exact signature_keys_01a2 1
  · exact signature_keys_01a3 0
  · exact signature_keys_01a3 1

end QiushiMatmul.FrozenLabel
