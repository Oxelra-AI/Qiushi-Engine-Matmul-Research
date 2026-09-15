import QiushiPlane491StrictData
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane491SourceStrictBlock2 : ∀ offset : Fin 32,
    ∀ hlt : 2 * 32 + offset.val < 726,
    plane491SourceStrictCheck ⟨2 * 32 + offset.val, hlt⟩ = true := by
  decide +kernel
end QiushiMatmul
