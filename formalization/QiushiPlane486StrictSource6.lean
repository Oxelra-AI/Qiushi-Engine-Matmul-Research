import QiushiPlane486StrictData
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane486SourceStrictBlock6 : ∀ offset : Fin 32,
    ∀ hlt : 6 * 32 + offset.val < 262,
    plane486SourceStrictCheck ⟨6 * 32 + offset.val, hlt⟩ = true := by
  decide +kernel
end QiushiMatmul
