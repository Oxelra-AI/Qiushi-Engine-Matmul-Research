import QiushiPlane453GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane453GenIndicatorBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 210,
    plane453GenIndicatorProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane453GenIndicatorProperty, plane453GenConfig, plane453GenOccSys]
  decide +kernel
end QiushiMatmul
