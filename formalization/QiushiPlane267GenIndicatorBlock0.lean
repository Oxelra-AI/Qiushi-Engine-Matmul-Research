import QiushiPlane267GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane267GenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 33,
    plane267GenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane267GenIndicatorProperty, plane267GenConfig, plane267GenOccSys]
  decide +kernel
end QiushiMatmul
