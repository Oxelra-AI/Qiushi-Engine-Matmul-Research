import QiushiPlane491StrictData
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane491SourceStrictBlock3 : ∀ offset : Fin 32,
    ∀ hlt : 3 * 32 + offset.val < 726,
    plane491SourceStrictCheck ⟨3 * 32 + offset.val, hlt⟩ = true := by
  decide +kernel
end QiushiMatmul
