import QiushiPlane468GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane468GenIndicatorBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 253,
    plane468GenIndicatorProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane468GenIndicatorProperty, plane468GenConfig, plane468GenOccSys]
  decide +kernel
end QiushiMatmul
