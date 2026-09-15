import QiushiPlane315GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane315GenIndicatorBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 74,
    plane315GenIndicatorProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane315GenIndicatorProperty, plane315GenConfig, plane315GenOccSys]
  decide +kernel
end QiushiMatmul
