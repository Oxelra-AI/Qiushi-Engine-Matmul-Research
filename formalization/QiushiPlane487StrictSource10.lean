import QiushiPlane487StrictData
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane487SourceStrictBlock10 : ∀ offset : Fin 32,
    ∀ hlt : 10 * 32 + offset.val < 668,
    plane487SourceStrictCheck ⟨10 * 32 + offset.val, hlt⟩ = true := by
  decide +kernel
end QiushiMatmul
