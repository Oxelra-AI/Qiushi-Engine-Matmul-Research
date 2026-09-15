import QiushiPlane474GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane474GenIndicatorBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 146,
    plane474GenIndicatorProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane474GenIndicatorProperty, plane474GenConfig, plane474GenOccSys]
  decide +kernel
end QiushiMatmul
