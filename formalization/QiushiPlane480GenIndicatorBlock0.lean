import QiushiPlane480GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane480GenIndicatorBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 221,
    plane480GenIndicatorProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane480GenIndicatorProperty, plane480GenConfig, plane480GenOccSys]
  decide +kernel
end QiushiMatmul
