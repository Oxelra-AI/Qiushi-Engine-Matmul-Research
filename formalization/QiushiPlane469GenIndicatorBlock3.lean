import QiushiPlane469GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane469GenIndicatorBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 217,
    plane469GenIndicatorProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane469GenIndicatorProperty, plane469GenConfig, plane469GenOccSys]
  decide +kernel
end QiushiMatmul
