import QiushiPlane449GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane449GenIndicatorBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 56,
    plane449GenIndicatorProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane449GenIndicatorProperty, plane449GenConfig, plane449GenOccSys]
  decide +kernel
end QiushiMatmul
