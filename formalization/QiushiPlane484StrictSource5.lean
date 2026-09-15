import QiushiPlane484StrictData
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane484SourceStrictBlock5 : ∀ offset : Fin 32,
    ∀ hlt : 5 * 32 + offset.val < 1665,
    plane484SourceStrictCheck ⟨5 * 32 + offset.val, hlt⟩ = true := by
  decide +kernel
end QiushiMatmul
