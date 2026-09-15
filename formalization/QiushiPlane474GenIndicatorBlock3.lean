import QiushiPlane474GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane474GenIndicatorBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 146,
    plane474GenIndicatorProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane474GenIndicatorProperty, plane474GenConfig, plane474GenOccSys]
  decide +kernel
end QiushiMatmul
