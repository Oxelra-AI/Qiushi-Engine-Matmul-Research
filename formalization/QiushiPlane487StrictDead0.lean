import QiushiPlane487StrictData
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane487DeadStrictBlock0 : ∀ offset : Fin 32,
    ∀ hlt : 0 * 32 + offset.val < 79,
    plane487DeadStrictCheck ⟨0 * 32 + offset.val, hlt⟩ = true := by
  decide +kernel
end QiushiMatmul
