import QiushiPlane491StrictData
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane491DeadStrictBlock0 : ∀ offset : Fin 32,
    ∀ hlt : 0 * 32 + offset.val < 78,
    plane491DeadStrictCheck ⟨0 * 32 + offset.val, hlt⟩ = true := by
  decide +kernel
end QiushiMatmul
