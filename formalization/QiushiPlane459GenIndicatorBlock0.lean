import QiushiPlane459GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane459GenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 42,
    plane459GenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane459GenIndicatorProperty, plane459GenConfig, plane459GenOccSys]
  decide +kernel
end QiushiMatmul
