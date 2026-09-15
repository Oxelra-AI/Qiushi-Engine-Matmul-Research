import QiushiPlane292GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane292GenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 28,
    plane292GenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane292GenIndicatorProperty, plane292GenConfig, plane292GenOccSys]
  decide +kernel
end QiushiMatmul
