import QiushiPlane488StrictData
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane488SourceStrictBlock1 : ∀ offset : Fin 32,
    ∀ hlt : 1 * 32 + offset.val < 413,
    plane488SourceStrictCheck ⟨1 * 32 + offset.val, hlt⟩ = true := by
  decide +kernel
end QiushiMatmul
