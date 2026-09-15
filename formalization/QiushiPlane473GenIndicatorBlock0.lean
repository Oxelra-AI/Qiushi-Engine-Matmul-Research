import QiushiPlane473GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane473GenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 153,
    plane473GenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane473GenIndicatorProperty, plane473GenConfig, plane473GenOccSys]
  decide +kernel
end QiushiMatmul
