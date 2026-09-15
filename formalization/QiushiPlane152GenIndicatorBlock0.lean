import QiushiPlane152GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane152GenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 16,
    plane152GenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane152GenIndicatorProperty, plane152GenConfig, plane152GenOccSys]
  decide +kernel
end QiushiMatmul
