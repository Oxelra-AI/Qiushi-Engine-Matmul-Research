import QiushiPlane425GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane425GenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 202,
    plane425GenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane425GenIndicatorProperty, plane425GenConfig, plane425GenOccSys]
  decide +kernel
end QiushiMatmul
