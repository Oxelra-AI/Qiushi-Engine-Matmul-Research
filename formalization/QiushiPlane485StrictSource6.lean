import QiushiPlane485StrictData
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane485SourceStrictBlock6 : ∀ offset : Fin 32,
    ∀ hlt : 6 * 32 + offset.val < 421,
    plane485SourceStrictCheck ⟨6 * 32 + offset.val, hlt⟩ = true := by
  decide +kernel
end QiushiMatmul
