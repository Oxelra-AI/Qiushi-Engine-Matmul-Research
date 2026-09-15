import QiushiPlane475GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane475GenIndicatorBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 126,
    plane475GenIndicatorProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane475GenIndicatorProperty, plane475GenConfig, plane475GenOccSys]
  decide +kernel
end QiushiMatmul
