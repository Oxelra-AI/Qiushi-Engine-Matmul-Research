import QiushiPlane433GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane433GenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 63,
    plane433GenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane433GenIndicatorProperty, plane433GenConfig, plane433GenOccSys]
  decide +kernel
end QiushiMatmul
