import QiushiPlane419GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane419GenIndicatorBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 59,
    plane419GenIndicatorProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane419GenIndicatorProperty, plane419GenConfig, plane419GenOccSys]
  decide +kernel
end QiushiMatmul
