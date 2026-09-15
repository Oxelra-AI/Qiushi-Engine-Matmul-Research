import QiushiPlane467GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane467GenIndicatorBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 84,
    plane467GenIndicatorProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane467GenIndicatorProperty, plane467GenConfig, plane467GenOccSys]
  decide +kernel
end QiushiMatmul
