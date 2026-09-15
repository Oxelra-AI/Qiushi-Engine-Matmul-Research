import QiushiPlane475GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane475GenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 126,
    plane475GenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane475GenIndicatorProperty, plane475GenConfig, plane475GenOccSys]
  decide +kernel
end QiushiMatmul
