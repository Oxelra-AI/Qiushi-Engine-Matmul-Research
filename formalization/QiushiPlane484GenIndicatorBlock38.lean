import QiushiPlane484GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane484GenIndicatorBlock38 : forall offset : Fin 32,
    forall hlt : 38 * 32 + offset.val < 1665,
    plane484GenIndicatorProperty (Fin.mk (38 * 32 + offset.val) hlt) := by
  simp only [plane484GenIndicatorProperty, plane484GenConfig, plane484GenOccSys]
  decide +kernel
end QiushiMatmul
