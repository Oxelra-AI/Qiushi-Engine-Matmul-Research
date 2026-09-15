import QiushiPlane463GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane463GenIndicatorBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 278,
    plane463GenIndicatorProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane463GenIndicatorProperty, plane463GenConfig, plane463GenOccSys]
  decide +kernel
end QiushiMatmul
