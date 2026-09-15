import QiushiPlane487GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane487GenIndicatorBlock19 : forall offset : Fin 32,
    forall hlt : 19 * 32 + offset.val < 668,
    plane487GenIndicatorProperty (Fin.mk (19 * 32 + offset.val) hlt) := by
  simp only [plane487GenIndicatorProperty, plane487GenConfig, plane487GenOccSys]
  decide +kernel
end QiushiMatmul
