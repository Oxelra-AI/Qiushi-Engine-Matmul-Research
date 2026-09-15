import QiushiPlane428GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane428GenIndicatorBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 51,
    plane428GenIndicatorProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane428GenIndicatorProperty, plane428GenConfig, plane428GenOccSys]
  decide +kernel
end QiushiMatmul
