import QiushiPlane472GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane472GenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 242,
    plane472GenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane472GenIndicatorProperty, plane472GenConfig, plane472GenOccSys]
  decide +kernel
end QiushiMatmul
