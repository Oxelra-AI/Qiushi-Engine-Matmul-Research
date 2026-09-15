import QiushiPlane490GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane490GenIndicatorBlock17 : forall offset : Fin 32,
    forall hlt : 17 * 32 + offset.val < 713,
    plane490GenIndicatorProperty (Fin.mk (17 * 32 + offset.val) hlt) := by
  simp only [plane490GenIndicatorProperty, plane490GenConfig, plane490GenOccSys]
  decide +kernel
end QiushiMatmul
