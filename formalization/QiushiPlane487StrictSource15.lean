import QiushiPlane487StrictData
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane487SourceStrictBlock15 : ∀ offset : Fin 32,
    ∀ hlt : 15 * 32 + offset.val < 668,
    plane487SourceStrictCheck ⟨15 * 32 + offset.val, hlt⟩ = true := by
  decide +kernel
end QiushiMatmul
