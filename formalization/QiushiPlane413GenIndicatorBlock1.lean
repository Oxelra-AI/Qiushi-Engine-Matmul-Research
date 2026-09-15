import QiushiPlane413GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane413GenIndicatorBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 49,
    plane413GenIndicatorProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane413GenIndicatorProperty, plane413GenConfig, plane413GenOccSys]
  decide +kernel
end QiushiMatmul
