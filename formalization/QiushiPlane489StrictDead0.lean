import QiushiPlane489StrictData
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane489DeadStrictBlock0 : ∀ offset : Fin 32,
    ∀ hlt : 0 * 32 + offset.val < 95,
    plane489DeadStrictCheck ⟨0 * 32 + offset.val, hlt⟩ = true := by
  decide +kernel
end QiushiMatmul
