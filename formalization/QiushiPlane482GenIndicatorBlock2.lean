import QiushiPlane482GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane482GenIndicatorBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 118,
    plane482GenIndicatorProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane482GenIndicatorProperty, plane482GenConfig, plane482GenOccSys]
  decide +kernel
end QiushiMatmul
